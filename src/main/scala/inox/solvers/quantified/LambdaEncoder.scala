/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

import ast._
import utils._

trait LambdaEncoder extends LiveSymbolTransformer   { self =>

  val ctx: Context

  val t: self.s.type = self.s

  import s._
  import s.dsl._

  private val lambdas        = new IncrementalSet[Lambda]
  private val lambdaFreeVars = new IncrementalMap[Lambda, Seq[Variable]]()
  private val qLambdas       = new IncrementalMap[FunctionType, FunDef]()
  private val lambdaSorts    = new IncrementalMap[Int, ADTSort]()
  private val lambdaCons     = new IncrementalBijection[Lambda, ADTConstructor]()
  private val lambdaInsts    = new IncrementalMap[Lambda, Expr]()
  private val sortCons       = new IncrementalMap[ADTSort, Set[ADTConstructor]]()

  def transform(syms: Symbols, expr: Expr): (Symbols, Expr) = {
    implicit val iSyms: Symbols = syms

    val fns = syms.functions.values.toList

    val allLambdas = (expr :: fns.map(_.fullBody)) flatMap { expr =>
      exprOps.collect {
        case lam: Lambda => Set(lam)
        case _ => Set.empty[Lambda]
      } (expr)
    }

    // Instantiate every lambda in the program before actually processing the program
    // so that all the sorts and constructors are defined when we will actually need them
    allLambdas foreach instantiateLambda

    // Rewrite function types in ADTs by their defunctionalized equivalent
    val adts = syms.adts.values.toList map {
      case cons: ADTConstructor =>
        val fields = cons.fields.map { case vd =>
          rewriteLambdaTypes(vd.toVariable).asInstanceOf[Variable].toVal
        }
        cons.copy(fields = fields)

      case sort: ADTSort =>
        sort
    }

    val newSyms = NoSymbols.withFunctions(fns).withADTs(adts)

    def encodeFunction(fd: FunDef)(syms: Symbols): FunDef = {
      val body = encode(fd.fullBody)(syms)
      val params = fd.params.map(vd => vd.copy(tpe = funToSort(vd.tpe)))
      val returnType = funToSort(fd.returnType)
      fd.copy(params = params, returnType = returnType, fullBody = body)
    }

    val functions = fns.map(fn => encodeFunction(fn)(newSyms))
    val newExpr = encode(expr)(newSyms)
    val qLambdaDefs = qLambdas.values.toSeq.map(fn => encodeFunction(fn)(newSyms))

    val newFunctions = functions ++ qLambdaDefs
    val newADTs = adts ++ lambdaSorts.values.toSeq ++ sortCons.values.flatten.toSeq

    val finalSyms = NoSymbols.withFunctions(newFunctions).withADTs(newADTs)

    check(newExpr)(finalSyms)

    // println("=" * 80)
    // println("LambdaEncoder")
    // println("=" * 80)
    // println(program)
    // println()
    // println(newExpr)
    // println()

    (finalSyms, newExpr)
  }

  def check(expr: Expr)(implicit syms: Symbols): Unit = {
    def collectApps(expr: Expr): Set[Application] = {
      exprOps.collect[Application] {
        case app: Application => Set(app)
        case _ => Set.empty
      } (expr)
    }

    def errorFun(apps: Seq[Application], fd: FunDef): Unit = {
      val msg = apps.toSeq.map(_.toString).mkString(" - ", "\n - ", "\n")
      sys.error("LambdaEncoder: found the following applications\n" + msg + "\nin " + fd)
    }

    def errorExpr(apps: Seq[Application], expr: Expr): Unit = {
      val msg = apps.toSeq.map(_.toString).mkString(" - ", "\n - ", "\n")
      sys.error("LambdaEncoder: found the following applications\n" + msg + "\nin\n\n" + expr)
    }

    val apps = collectApps(expr)
    if (apps.nonEmpty) {
      errorExpr(apps.toSeq, expr)
    }

    syms.functions.values.toSeq foreach { fd =>
      val apps = collectApps(fd.fullBody)
      if (apps.nonEmpty) {
        errorFun(apps.toSeq, fd)
      }
    }
  }

  def encode(expr: Expr)(implicit syms: Symbols) = {
    rewriteLambdaTypes(rewriteApplications(encodeLambdas(expr)(syms))(syms))(syms)
  }

  def encodeLambdas(expr: Expr)(implicit syms: Symbols): Expr = {
    def go(expr: Expr): Option[Expr] = expr match {
      case lam: Lambda =>
        Some(instantiateLambda(lam)(syms))

      case Forall(args, body) =>
        val newArgs = args.zip(args.map(_.tpe)) map {
          case (arg, ft: FunctionType) =>
            val sortTpe = mkLambdaSort(ft).typed(syms).toType
            arg.copy(tpe = sortTpe)

          case (arg, _) =>
            arg
        }

        Some(Forall(newArgs, rewriteLambdaTypes(body)(syms)))

      case _ => None
    }

    exprOps.postMap(go)(expr)
  }

  def rewriteApplications(expr: Expr)(implicit syms: Symbols): Expr = {
    import syms._

    def go(expr: Expr): Option[Expr] = expr match {

      // @romac - FIXME: This should not be needed
      case Application(caller: ADT, args) =>
        val adts = lambdaSorts.values ++ lambdaCons.bSet
        val sym = syms.withADTs(adts.toSeq)
        val cons = caller.adt.getADT(sym).definition.typed(sym).toConstructor.definition
        val ft @ FunctionType(_, _) = bestRealType(lambdaCons.getA(cons).get.getType(sym))
        val fd = mkQLambda(ft)
        Some(E(fd.id).apply(caller.getType, args.map(_.getType): _*)((caller +: args): _*))

      case Application(caller, args) =>
        val ft @ FunctionType(_, _) = bestRealType(caller.getType(syms))
        val fd = mkQLambda(ft)
        Some(E(fd.id).apply(caller.getType, args.map(_.getType): _*)((caller +: args): _*))

      case _ => None
    }

    exprOps.postMap(go)(expr)
  }

  def isFun(tp: Type)(implicit syms: Symbols): Boolean = {
    tp.isInstanceOf[FunctionType]
  }

  def funToSort(tp: Type)(implicit syms: Symbols): Type = {
    def go(tp: Type): Option[Type] = tp match {
      case ft: FunctionType =>
        Some(mkLambdaSort(ft).typed(ft.from :+ ft.to).toType)
      case _ =>
        None
    }

    typeOps.postMap(go)(tp)
  }

  def rewriteLambdaTypes(expr: Expr)(implicit syms: Symbols): Expr = {
    def go(expr: Expr): Option[Expr] = expr match {
      case v: Variable =>
        Some(v.copy(tpe = funToSort(v.tpe)))
      case ai: AsInstanceOf if isFun(ai.tpe) =>
        Some(ai.copy(tpe = funToSort(ai.tpe)))
      case ii: IsInstanceOf if isFun(ii.tpe) =>
        Some(ii.copy(tpe = funToSort(ii.tpe)))
      case fs: FiniteSet if isFun(fs.base) =>
        Some(fs.copy(base = funToSort(fs.base)))
      case fb: FiniteBag if isFun(fb.base) =>
        Some(fb.copy(base = funToSort(fb.base)))
      case fm: FiniteMap if isFun(fm.keyType) || isFun(fm.valueType) =>
        Some(fm.copy(keyType = funToSort(fm.keyType), valueType = funToSort(fm.valueType)))
      case fi: FunctionInvocation =>
        Some(fi.copy(tps = fi.tps.map(funToSort)))

      case adt: ADT =>
        val ADTType(id, tps) = adt.adt
        val tpe = ADTType(id, tps.map(tp => funToSort(tp)))
        Some(adt.copy(adt = tpe))
      case _ =>
        None
    }

    exprOps.postMap(go)(expr)
  }

  private def freeVars(lam: Lambda)(implicit syms: Symbols): Seq[Variable] = lambdaFreeVars.cached(lam) {
    (exprOps.variablesOf(lam.body) -- lam.args.map(_.toVariable)).toSeq
  }

  private def mkFreshParams(n: Int): Seq[TypeParameterDef] = {
    // FIXME: Only works for arities < 26
    ('A' to 'Z').take(n + 1)
                .map(_.toString)
                .map(FreshIdentifier(_))
                .map(TypeParameterDef(_))
  }

  private def mkLambdaSort(ft: FunctionType)(implicit syms: Symbols): ADTSort = lambdaSorts.cached(ft.arity) {
    val id = FreshIdentifier("Arrow" + ft.arity.toString)
    new ADTSort(id, mkFreshParams(ft.arity), Seq.empty, Set.empty)
  }

  private var lambdaConsNum: Int = 0

  private def mkLambdaCons(lam: Lambda)(implicit syms: Symbols): ADTConstructor = lambdaCons.cachedB(lam) {
    import syms._

    val ft @ FunctionType(froms, to) = bestRealType(lam.getType)
    val sort = mkLambdaSort(ft)
    val frees = freeVars(lam)
    val fields = frees.map(_.toVal).map(v => v.copy(tpe = funToSort(v.tpe)))
    val id = FreshIdentifier(sort.id.name + "_" + lambdaConsNum)
    lambdaConsNum += 1

    lambdaSorts += ft.arity -> sort.copy(cons = sort.cons :+ id)

    val cons = new ADTConstructor(id, mkFreshParams(ft.arity), Some(sort.id), fields, Set.empty)
    val allCons = sortCons.getOrElse(sort, Set.empty)
    sortCons += sort -> (allCons + cons)
    cons
  }

  private def instantiateLambda(lam: Lambda)(implicit syms: Symbols): Expr = lambdaInsts.cached(lam) {
    import syms._

    lambdas += lam

    val ft @ FunctionType(_, _) = bestRealType(lam.getType)
    val cons = mkLambdaCons(lam)
    val sort = mkLambdaSort(ft)

    ADT(cons.typed(ft.from :+ ft.to).toType, freeVars(lam))
  }

  private def simplify(expr: Expr)(implicit syms: Symbols): Expr = {
      syms.simplifyHOFunctions(syms.simplifyExpr(expr))
    }

    private def normalizeArgs(lam: Lambda, newArgs: Seq[ValDef])(implicit syms: Symbols): Lambda = {

      Lambda(newArgs, exprOps.replaceFromSymbols(lam.args.zip(newArgs.map(_.toVariable)).toMap, lam.body))
    }

    private def newQLambdaId(ft: FunctionType)(implicit syms: Symbols): Identifier = {
      implicit val printerOpts: PrinterOptions = PrinterOptions.fromSymbols(syms, ctx)
      FreshIdentifier("apply_Arrow" + ft.arity)
    }

    private def mkQLambda(ft: FunctionType)(implicit syms: Symbols): FunDef = qLambdas.cached(ft) {
      val id = newQLambdaId(ft)
      val sort = mkLambdaSort(ft)
      val conss = sortCons.getOrElse(sort, Set.empty).toList

      // if (conss.isEmpty) {
      //   val consId = FreshIdentifier(sort.id.name + "_Cons")
      //   val cons = new ADTConstructor(consId, Seq.empty, Some(sort.id), Seq.empty, Set.empty)
      //   sortCons += sort -> Set(cons)
      //   lambdaSorts += ft.arity -> sort.copy(cons = sort.cons :+ consId)
      // }

      val lam = Variable.fresh("lam", sort.typed.toType)

      val newVars = sort.tparams.init map { tparam =>
        Variable.fresh("arg", tparam.tp, alwaysShowUniqueID = true)
      }

      val newArgs = newVars.map(_.toVal)

      val branches = conss.map { cons =>
        val tpe = cons.typed(ft.from :+ ft.to).toType
        val lets = cons.fields.map { v =>
          (body: Expr) => Let(v, lam.asInstOf(tpe).getField(v.id), body)
        }

        val lambda = normalizeArgs(lambdaCons.fromB(cons), newArgs)
        val body: Expr = simplify(lambda.body).asInstOf(sort.tparams.last.tp)
        val args = exprOps.variablesOf(body).toSeq.map(_.toVal)
        val thenBody = lets.foldRight(body) { (f, e) => f(e) }

        tpe -> thenBody
      }

      val unintepretedVariable: Expr = Variable(FreshIdentifier("<uninterpreted>"), ft.to, Set.empty)

      val body = branches.foldRight(unintepretedVariable) { case ((tpe, thn), els) =>
        IfExpr(lam.isInstOf(tpe), thn, els)
      }

      val flags = if (branches.isEmpty) Set[Flag](Uninterpreted) else Set.empty[Flag]

      new FunDef(id, mkFreshParams(ft.arity), lam.toVal +: newArgs, sort.tparams.last.tp, body, flags)
    }

  }

object LambdaEncoder {

  def apply(trees: Trees, context: Context): LambdaEncoder {
    val s: trees.type
    val ctx: context.type
  } = new LambdaEncoder {
    override val s: trees.type = trees
    override val ctx: context.type = context
  }

}
