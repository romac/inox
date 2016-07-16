/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.collection.mutable.{Map => MutableMap}

trait Definitions { self: Trees =>

  sealed trait Definition extends Tree {
    val id: Identifier

    override def equals(that: Any): Boolean = that match {
      case d: Definition => id == d.id
      case _=> false
    }

    override def hashCode = id.hashCode
  }

  abstract class LookupException(id: Identifier, what: String)
    extends Exception("Lookup failed for " + what + " with symbol " + id)
  case class FunctionLookupException(id: Identifier) extends LookupException(id, "function")
  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")

  case class NotWellFormedException(id: Identifier, s: Symbols)
    extends Exception(s"$id not well formed in ${s.asString}")

  /** Common super-type for [[ValDef]] and [[Expressions.Variable]].
    *
    * Both types share much in common and being able to reason about them
    * in a uniform manner can be useful in certain cases.
    */
  private[ast] trait VariableSymbol extends Typed {
    val id: Identifier
    val tpe: Type

    def getType(implicit s: Symbols): Type = tpe

    override def equals(that: Any): Boolean = that match {
      case vs: VariableSymbol => id == vs.id && tpe == vs.tpe
      case _ => false
    }

    def hashCode: Int = 61 * id.hashCode + tpe.hashCode
  }

  /** 
    * A ValDef declares a formal parameter (with symbol [[id]]) to be of a certain type.
    */
  case class ValDef(id: Identifier, tpe: Type) extends Definition with VariableSymbol {
    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]] */
    def toVariable: Variable = Variable(id, tpe)
    def freshen: ValDef = ValDef(id.freshen, tpe).copiedFrom(this)
  }

  /** A wrapper for a program. For now a program is simply a single object. */
  case class Symbols(classes: Map[Identifier, ClassDef], functions: Map[Identifier, FunDef])
     extends Tree
        with TypeOps
        with SymbolOps
        with CallGraph
        with Constructors
        with Paths {

    val trees: self.type = self
    val symbols: this.type = this
    private implicit def s: Symbols = symbols

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdate(id -> tps, lookupClass(id).map(_.typed(tps)))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    private val typedFunctionCache: MutableMap[(Identifier, Seq[Type]), Option[TypedFunDef]] = MutableMap.empty
    def lookupFunction(id: Identifier): Option[FunDef] = functions.get(id)
    def lookupFunction(id: Identifier, tps: Seq[Type]): Option[TypedFunDef] =
      typedFunctionCache.getOrElseUpdate(id -> tps, lookupFunction(id).map(_.typed(tps)(this)))

    def getFunction(id: Identifier): FunDef = lookupFunction(id).getOrElse(throw FunctionLookupException(id))
    def getFunction(id: Identifier, tps: Seq[Type]): TypedFunDef = lookupFunction(id, tps).getOrElse(throw FunctionLookupException(id))
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def freshen = TypeParameterDef(tp.freshen)
    val id = tp.id
  }
 
  /** A trait that represents flags that annotate a ClassDef with different attributes */
  sealed trait ClassFlag

  object ClassFlag {
    def fromName(name: String, args: Seq[Option[Any]]): ClassFlag = Annotation(name, args)
  }

  /** A trait that represents flags that annotate a FunDef with different attributes */
  sealed trait FunctionFlag

  object FunctionFlag {
    def fromName(name: String, args: Seq[Option[Any]]): FunctionFlag = name match {
      case "inline" => IsInlined
      case _ => Annotation(name, args)
    }
  }

  // Compiler annotations given in the source code as @annot
  case class Annotation(annot: String, args: Seq[Option[Any]]) extends FunctionFlag with ClassFlag
  // Class has ADT invariant method
  case class HasADTInvariant(id: Identifier) extends ClassFlag
  // Is inlined
  case object IsInlined extends FunctionFlag

  /** Represents a class definition (either an abstract- or a case-class) */
  sealed trait ClassDef extends Definition {
    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    val flags: Set[ClassFlag]

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect { case Annotation(s, args) => s -> args }.toMap

    def root(implicit s: Symbols): ClassDef
    def invariant(implicit s: Symbols): Option[FunDef] = {
      val rt = root
      if (rt ne this) rt.invariant
      else flags.collect { case HasADTInvariant(id) => id }.headOption.map(s.getFunction)
    }

    def hasInvariant(implicit s: Symbols): Boolean = invariant.isDefined

    val isAbstract: Boolean

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef
    def typed(implicit s: Symbols): TypedClassDef
  }

  /** Abstract classes. */
  class AbstractClassDef(val id: Identifier,
                         val tparams: Seq[TypeParameterDef],
                         val children: Seq[Identifier],
                         val flags: Set[ClassFlag]) extends ClassDef {
    val isAbstract = true

    def descendants(implicit s: Symbols): Seq[ClassDef] = children
      .map(id => s.getClass(id) match {
        case ccd: CaseClassDef => ccd
        case _ => throw NotWellFormedException(id, s)
      })

    def ccDescendants(implicit s: Symbols): Seq[CaseClassDef] =
      descendants collect { case ccd: CaseClassDef => ccd }

    def isInductive(implicit s: Symbols): Boolean = {
      def induct(tpe: Type, seen: Set[ClassDef]): Boolean = tpe match {
        case ct: ClassType =>
          val tcd = ct.lookupClass.getOrElse(throw ClassLookupException(ct.id))
          val root = tcd.cd.root
          seen(root) || (tcd match {
            case tccd: TypedCaseClassDef =>
              tccd.fields.exists(vd => induct(vd.getType, seen + root))
            case _ => false
          })
        case TupleType(tpes) =>
          tpes.exists(tpe => induct(tpe, seen))
        case _ => false
      }

      if (this == root && !this.isAbstract) false
      else ccDescendants.exists { ccd =>
        ccd.fields.exists(vd => induct(vd.getType, Set(root)))
      }
    }

    def root(implicit s: Symbols): ClassDef = this

    def typed(implicit s: Symbols): TypedAbstractClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedAbstractClassDef = {
      require(tps.length == tparams.length)
      TypedAbstractClassDef(this, tps)
    }
  }

  /** Case classes/ case objects. */
  class CaseClassDef(val id: Identifier,
                     val tparams: Seq[TypeParameterDef],
                     val parent: Option[Identifier],
                     val fields: Seq[ValDef],
                     val flags: Set[ClassFlag]) extends ClassDef {

    val isAbstract = false

    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.indexWhere(_.id == id)

      if (index < 0) {
        scala.sys.error(
          "Could not find '"+id+"' ("+id.uniqueName+") within "+
          fields.map(_.id.uniqueName).mkString(", ")
        )
      } else index
    }

    def root(implicit s: Symbols): ClassDef = parent.map(id => s.getClass(id).root).getOrElse(this)

    def typed(implicit s: Symbols): TypedCaseClassDef = typed(tparams.map(_.tp))
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedCaseClassDef = {
      require(tps.length == tparams.length)
      TypedCaseClassDef(this, tps)
    }
  }

  sealed abstract class TypedClassDef extends Tree {
    val cd: ClassDef
    val tps: Seq[Type]
    implicit val symbols: Symbols

    val id: Identifier = cd.id

    lazy val root: TypedClassDef = cd.root.typed(tps)
    lazy val invariant: Option[TypedFunDef] = cd.invariant.map(_.typed(tps))
    lazy val hasInvariant: Boolean = invariant.isDefined

    def toType = ClassType(cd.id, tps)
  }

  case class TypedAbstractClassDef(cd: AbstractClassDef, tps: Seq[Type])(implicit symbols: Symbols) extends TypedClassDef {
    def descendants: Seq[TypedClassDef] = cd.descendants.map(_.typed(tps))
    def ccDescendants: Seq[TypedCaseClassDef] = cd.ccDescendants.map(_.typed(tps))
  }

  case class TypedCaseClassDef(cd: CaseClassDef, tps: Seq[Type])(implicit symbols: Symbols) extends TypedClassDef {
    lazy val fields: Seq[ValDef] = {
      val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.getType, tmap)))
    }

    lazy val fieldsTypes = fields.map(_.tpe)

    lazy val parent: Option[TypedAbstractClassDef] = cd.parent.map(id => symbols.getClass(id) match {
      case acd: AbstractClassDef => TypedAbstractClassDef(acd, tps)
      case _ => throw NotWellFormedException(id, symbols)
    })
  }


  /** Function/method definition.
    *
    *  This class represents methods or fields of objects or classes. By "fields" we mean
    *  fields defined in the body of a class/object, not the constructor arguments of a case class
    *  (those are accessible through [[leon.purescala.Definitions.ClassDef.fields]]).
    *
    *  When it comes to verification, all are treated the same (as functions).
    *  They are only differentiated when it comes to code generation/ pretty printing.
    *  By default, the FunDef represents a function/method as opposed to a field,
    *  unless otherwise specified by its flags.
    *
    *  Bear in mind that [[id]] will not be consistently typed.
    */
  class FunDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Set[FunctionFlag]
  ) extends Definition {

    /* Body manipulation */

    lazy val body: Option[Expr] = exprOps.withoutSpec(fullBody)
    lazy val precondition = exprOps.preconditionOf(fullBody)
    lazy val precOrTrue = precondition getOrElse BooleanLiteral(true)

    lazy val postcondition = exprOps.postconditionOf(fullBody)
    lazy val postOrTrue = postcondition getOrElse {
      val arg = ValDef(FreshIdentifier("res", alwaysShowUniqueID = true), returnType)
      Lambda(Seq(arg), BooleanLiteral(true))
    }

    def hasBody          = body.isDefined
    def hasPrecondition  = precondition.isDefined
    def hasPostcondition = postcondition.isDefined

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap

    /* Wrapping in TypedFunDef */

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedFunDef = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed(implicit s: Symbols): TypedFunDef = typed(tparams.map(_.tp))

    /* Auxiliary methods */

    def isRecursive(implicit s: Symbols) = s.transitiveCallees(this) contains this

    def typeArgs = tparams map (_.tp)

    def applied(args: Seq[Expr])(implicit s: Symbols): FunctionInvocation = s.functionInvocation(this, args)
    def applied = FunctionInvocation(id, typeArgs, params map (_.toVariable))
  }


  // Wrapper for typing function according to valuations for type parameters
  case class TypedFunDef(fd: FunDef, tps: Seq[Type])(implicit symbols: Symbols) extends Tree {
    val id = fd.id

    def signature = {
      if (tps.nonEmpty) {
        id.toString+tps.mkString("[", ", ", "]")
      } else {
        id.toString
      }
    }

    private lazy val typesMap: Map[TypeParameter, Type] = {
      (fd.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2)
    }

    def translated(t: Type): Type = symbols.instantiateType(t, typesMap)

    def translated(e: Expr): Expr = symbols.instantiateType(e, typesMap)

    /** A mapping from this [[TypedFunDef]]'s formal parameters to real arguments
      *
      * @param realArgs The arguments to which the formal argumentas are mapped
      */
    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == params.size)
      (params zip realArgs).toMap
    }

    /** Substitute this [[TypedFunDef]]'s formal parameters with real arguments in some expression
     *
     * @param realArgs The arguments to which the formal argumentas are mapped
     * @param e The expression in which the substitution will take place
     */
    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      exprOps.replaceFromSymbols(paramSubst(realArgs), e)
    }

    def applied(realArgs: Seq[Expr]): FunctionInvocation = {
      FunctionInvocation(id, tps, realArgs)
    }

    def applied: FunctionInvocation = applied(params map { _.toVariable })

    /** Params will contain ValDefs instantiated with the correct types */
    lazy val params: Seq[ValDef] = {
      if (typesMap.isEmpty) {
        fd.params
      } else {
        fd.params.map(vd => vd.copy(tpe = translated(vd.getType)))
      }
    }

    lazy val functionType = FunctionType(params.map(_.getType).toList, returnType)

    lazy val returnType: Type = translated(fd.returnType)

    lazy val fullBody      = translated(fd.fullBody)
    lazy val body          = fd.body map translated
    lazy val precondition  = fd.precondition map translated
    lazy val precOrTrue    = translated(fd.precOrTrue)
    lazy val postcondition = fd.postcondition map translated
    lazy val postOrTrue    = translated(fd.postOrTrue)

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined
  }
}