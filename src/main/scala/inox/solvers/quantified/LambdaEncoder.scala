/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

import utils._

trait LambdaEncoder { self =>

  val sourceProgram: Program

  import sourceProgram._
  import sourceProgram.trees._
  import sourceProgram.trees.dsl._
  import sourceProgram.symbols._

  private val lambdas        = new IncrementalSet[Lambda]
  private val lambdaFreeVars = new IncrementalMap[Lambda, Seq[Variable]]()
  private val qLambdas       = new IncrementalMap[FunctionType, FunDef]()
  private val lambdaSorts    = new IncrementalMap[FunctionType, ADTSort]()
  private val lambdaCons     = new IncrementalBijection[Lambda, ADTConstructor]()
  private val lambdaInsts    = new IncrementalMap[Lambda, Expr]()
  private val sortCons       = new IncrementalMap[ADTSort, Set[ADTConstructor]]()

  def transform(expr: Expr): (Program { val trees: sourceProgram.trees.type }, Expr) = {
    val simpleExpr = simplifyFormula(expr)
    val fns = symbols.functions.values.toList

    val allLambdas = (simpleExpr :: fns.map(_.fullBody)) flatMap { expr =>
      exprOps.collect {
        case lam: Lambda => Set(lam)
        case _ => Set.empty[Lambda]
      } (expr)
    }

    allLambdas foreach instantiateLambda

    val functions = fns map { fd =>
      val body = encode(fd.fullBody)
      val params = fd.params.map(vd => vd.copy(tpe = funToSort(vd.tpe)))
      val returnType = funToSort(fd.returnType)
      fd.copy(params = params, returnType = returnType, fullBody = body)
    }

    val newExpr = encode(simpleExpr)

    val qLambdaDefs = qLambdas.values.toSeq

    val adts = symbols.adts.values.toSeq map {
      case cons: ADTConstructor =>
        val fields = cons.fields.map { case vd =>
          rewriteLambdaTypes(vd.toVariable).asInstanceOf[Variable].toVal
        }
        cons.copy(fields = fields)

      case sort: ADTSort =>
        sort
    }

    val allFunctions = functions ++ qLambdaDefs
    val allADTs = adts ++ lambdaSorts.values.toSeq ++ sortCons.values.flatten.toSeq

    val program = new Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = NoSymbols.withFunctions(allFunctions).withADTs(allADTs)
      val ctx = sourceProgram.ctx
    }

    (program, newExpr)
  }

  def encode(expr: Expr) = {
    rewriteLambdaTypes(rewriteApplications(encodeLambdas(expr)))
  }

  def encodeLambdas(expr: Expr): Expr = {
    def go(expr: Expr): Option[Expr] = expr match {
      case lam: Lambda =>
        Some(instantiateLambda(lam))

      case Forall(args, body) =>
        println(expr)
        val newArgs = args.zip(args.map(_.tpe)) map {
          case (arg, ft: FunctionType) =>
            val sortTpe = mkLambdaSort(ft).typed.toType
            arg.copy(tpe = sortTpe)

          case (arg, _) =>
            arg
        }

        println(Forall(newArgs, rewriteLambdaTypes(body)))
        Some(Forall(newArgs, rewriteLambdaTypes(body)))

      case _ => None
    }

    exprOps.postMap(go)(expr)
  }

  def rewriteApplications(expr: Expr): Expr = {
    def go(expr: Expr): Option[Expr] = expr match {

      // @romac - FIXME: This should not be needed
      case Application(caller: ADT, args) =>
        val adts = lambdaSorts.values ++ lambdaCons.bSet
        val sym = NoSymbols.withADTs(adts.toSeq)
        val cons = caller.adt.getADT(sym).definition.typed.toConstructor.definition
        val ft @ FunctionType(_, _) = bestRealType(lambdaCons.getA(cons).get.getType)
        val fd = mkQLambda(ft)
        Some(fd.apply((caller +: args): _*))

      case Application(caller, args) =>
        val ft @ FunctionType(_, _) = bestRealType(caller.getType)
        val fd = mkQLambda(ft)
        Some(fd.apply((caller +: args): _*))

      case _ => None
    }

    exprOps.postMap(go)(expr)
  }

  def isFun(tp: Type): Boolean =
    tp.isInstanceOf[FunctionType]

  def funToSort(tp: Type): Type = tp match {
    case ft: FunctionType => lambdaSorts(ft).typed.toType
    case _ => tp
  }

  def rewriteLambdaTypes(expr: Expr): Expr = {
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
      case _ =>
        None
    }

    exprOps.postMap(go)(expr)
  }

  private def freeVars(lam: Lambda): Seq[Variable] = lambdaFreeVars.cached(lam) {
    (exprOps.variablesOf(lam.body) -- lam.args.map(_.toVariable)).toSeq
  }

  private def mkLambdaSort(ft: FunctionType): ADTSort = {
    lambdaSorts.cached(ft) {
      val id = FreshIdentifier("LambdaSort", alwaysShowUniqueID = true)
      new ADTSort(id, Seq.empty, Seq.empty, Set.empty)
    }
  }

  private def mkLambdaCons(lam: Lambda): ADTConstructor = lambdaCons.cachedB(lam) {
    val ft @ FunctionType(froms, to) = bestRealType(lam.getType)
    val sort = mkLambdaSort(ft)
    val frees = freeVars(lam)
    val fields = frees.map(_.toVal)
    val id = FreshIdentifier("LambdaCons", alwaysShowUniqueID = true)

    lambdaSorts += ft -> sort.copy(cons = sort.cons :+ id)

    val cons = new ADTConstructor(id, Seq.empty, Some(sort.id), fields, Set.empty)
    val allCons = sortCons.getOrElse(sort, Set.empty)
    sortCons += sort -> (allCons + cons)
    cons
  }

  private def instantiateLambda(lam: Lambda): Expr = lambdaInsts.cached(lam) {
    lambdas += lam

    val ft @ FunctionType(_, _) = bestRealType(lam.getType)
    val cons = mkLambdaCons(lam)
    val sort = mkLambdaSort(ft)

    ADT(cons.typed.toType, freeVars(lam))
  }

  private def simplifyBody(lam: Lambda): Expr = {
    simplifyHOFunctions(simplifyExpr(lam.body))
  }

  private def normalizeArgs(lam: Lambda, newArgs: Seq[ValDef]): Lambda = {
    Lambda(newArgs, exprOps.replaceFromSymbols(lam.args.zip(newArgs.map(_.toVariable)).toMap, lam.body))
  }

  private def newQLambdaId(ft: FunctionType): Identifier = {
    FreshIdentifier("qLambda", alwaysShowUniqueID = true)
  }

  private def mkQLambda(ft: FunctionType): FunDef = qLambdas.cached(ft) {
    val id = newQLambdaId(ft)
    val sort = mkLambdaSort(ft)
    val conss = sortCons.getOrElse(sort, Set.empty).toList

    if (conss.isEmpty) {
      val consId = FreshIdentifier("LambdaCons", alwaysShowUniqueID = true)
      val cons = new ADTConstructor(consId, Seq.empty, Some(sort.id), Seq.empty, Set.empty)
      sortCons += sort -> Set(cons)
      lambdaSorts += ft -> sort.copy(cons = sort.cons :+ consId)
    }

    val lam = Variable.fresh("lam", sort.typed.toType)

    val newVars = ft.from map { tpe =>
      Variable.fresh("arg", tpe, alwaysShowUniqueID = true)
    }

    val newArgs = newVars.map(_.toVal)

    val branches = conss.map { cons =>
      val tpe = cons.typed.toType
      val lets = cons.fields.map { v =>
        (body: Expr) => Let(v, lam.asInstOf(tpe).getField(v.id), body)
      }

      val lambda = normalizeArgs(lambdaCons.fromB(cons), newArgs)
      val body = simplifyBody(lambda)
      val args = exprOps.variablesOf(body).toSeq.map(_.toVal)
      val thenBody = lets.foldRight(body) { (f, e) => f(e) }

      tpe -> thenBody
    }

    val (body, flags) = branches.isEmpty match {
      case true => 
        val v = Variable(FreshIdentifier("<uninterpreted>"), ft.to, Set.empty)
        (v, Set[Flag](Uninterpreted))
      case false =>
        val cases = branches.init.foldRight(branches.last._2) { case ((tpe, thn), els) =>
          IfExpr(lam.isInstOf(tpe), thn, els)
        }
        (cases, Set.empty[Flag])
    }

    new FunDef(id, Seq.empty, lam.toVal +: newArgs, ft.to, body, flags)
  }

}

object LambdaEncoder {
  def apply(p: Program): LambdaEncoder {
    val sourceProgram: p.type
  } = new LambdaEncoder {
    val sourceProgram: p.type = p
  }
}

