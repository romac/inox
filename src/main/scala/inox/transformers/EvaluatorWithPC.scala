/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

import scala.language.existentials
import scala.util.Try
import scala.concurrent.{Future, Await, blocking}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._

import utils._
import solvers._
import SolverResponses._

import scala.util.DynamicVariable
import scala.collection.mutable.{Map => MutableMap}

object optPartialEval extends FlagOptionDef("partial-eval", false)

trait PathUtil { self: EvaluatorWithPC =>

  import trees._
  import symbols._
  import exprOps._
  import dsl._

  lazy private val solverCtx = context.withOpts(optPartialEval(false), optTimeout(200.millis), optNoSimplifications(false))
  lazy private val solver = semantics.getSolver(solverCtx).toAPI
  lazy private val solveVALID = (solver.solveVALID(_)).asInstanceOf[Expr => Option[Boolean]]
  lazy private val solveSAT = (solver.solveSAT(_)).asInstanceOf[Expr => SimpleResponse]

  private[this] var i: Int = 0

  private[this] def runTimeout[A](task: => A): Option[A] = {
    val future = Future(task)
    Try(Await.result(future, 200.millis)).toOption
  }

  implicit class PathOp(val path: Path) {
    def subsumes(other: Path): Boolean = {
      (path.elements.toSet subsetOf other.elements.toSet) || {
        false
        // val query = implies(other.toClause, path.toClause)
        // println("sub query  : " + query)
        // val res = runTimeout(solveVALID(query)).flatten.getOrElse(false)
        // println("sub res    : " + res)
        // res
      }
    }

    def contains(e: Expr): Boolean = {
      require(e.getType == BooleanType())
      i = i + 1
      val clause = path.toClause
      // println(s"$i - clause : " + clause)
      val query = implies(clause, e)
      // println(s"$i - query  : " + query)
      // val res = runTimeout(solveSAT(query).isSAT).getOrElse(false)
      val res = runTimeout(solveVALID(query)).flatten.getOrElse(false)

      res
    }
  }

}

trait EvaluatorWithPC extends TransformerWithPC with PathUtil { self =>
  import trees._
  import symbols._
  import exprOps._
  import dsl._

  val opts: solvers.PurityOptions
  val semantics: Semantics
  val context: Context

    // val TopLevelOrs(es) = unexpandLets(e)
    // val conds = conditions.toSeq
    // val topOr = orJoin(es.distinct.sortBy(_.hashCode))
    // val query = or(not(andJoin(conds)), topOr)
    // println("bindings:   " + exprSubst.iterator.toList.mkString(", "))
    // println("conditions: " + andJoin(conditions.toSeq))
    // println("query:      " + query)

    // val res = runTimeout(solve(query).isSAT).getOrElse(false)
    // // val res = solve(query).getOrElse(false)
    // println("result:     " + res)
    // println()
    // res

  type Env = Path

  // @nv: note that we make sure the initial env is fresh each time
  //      (since aggressive caching of cnf computations is taking place)
  def initEnv: Env = Path.empty

  private[this] var dynStack: DynamicVariable[List[Int]] = new DynamicVariable(Nil)
  // private[this] var dynPurity: DynamicVariable[List[Boolean]] = new DynamicVariable(Nil)

  private sealed abstract class PurityCheck
  private case object Pure extends PurityCheck
  private case object Impure extends PurityCheck
  private case object Checking extends PurityCheck

  private[this] val pureCache: MutableMap[Identifier, PurityCheck] = MutableMap.empty

  private def isPureFunction(id: Identifier): Boolean = {
    true
  }

  private def isInstanceOf(e: Expr, tpe: ADTType, path: Env): Option[Boolean] = {
    val tadt = tpe.getADT
    if (tadt.definition.isSort) {
      Some(true)
    } else if (path contains IsInstanceOf(e, tpe)) {
      Some(true)
    } else if (tadt.toConstructor.sort.isDefined) {
      val tsort = tadt.toConstructor.sort.get
      val alts = (tsort.constructors.toSet - tadt).map(_.toType)

      if (alts exists (tpe => path contains IsInstanceOf(e, tpe))) {
        Some(false)
      } else if (alts forall (tpe => path contains Not(IsInstanceOf(e, tpe)))) {
        Some(true)
      } else {
        Some(e.getType == tpe).filter(x => x).filter(x => x)
      }
    } else {
      None
    }
  }

  def isPure(e: Expr, path: Env): Boolean = true

  private val simplifyCache = new LruCache[Expr, (Env, Expr)](100)

  private def simplify(e: Expr, path: Env): Expr = {
    val cached = simplifyCache.get(e).filter(_._1.subsumes(path)).map(_._2)
    val res = cached match {
      case None =>
        val res = simplifyExpr(e, path)
        simplifyCache(e) = path -> res
        res

      case Some(res) =>
        res
    }
    println("")
    println("=============================")
    println(e)
    println("-----------------------------")
    println(res)
    println("-----------------------------")
    println("")
    res
  }

  private def simplifyExpr(e: Expr, path: Env): Expr = e match {
    case e if isGround(e) =>
      val evalCtx = context.withOpts(evaluators.optEvalQuantifiers(false))
      val evaluator = semantics.getEvaluator(context)
      evaluator.eval(e).result.map(exprOps.freshenLocals(_)).getOrElse(e)

    case e if e.getType == BooleanType() && (path contains e) =>
      BooleanLiteral(true)

    case e if e.getType == BooleanType() && (path contains not(e)) =>
      BooleanLiteral(false)

    // case v: Variable if path.getBinding(v).isDefined =>
    //   val e = path.getBinding(v).get
    //   println(s"\nfound binding: $v ==> $e\n")
    //   e

    case c @ Choose(res, BooleanLiteral(true)) if hasInstance(res.tpe) == Some(true) =>
      c

    case c: Choose =>
      c

    case Lambda(args, body) =>
      val rb = simplify(body, path)
      Lambda(args, rb)

    case Implies(l, r) => simplify(or(not(l), r), path)

    case And(e +: es) => simplify(e, path) match {
      case BooleanLiteral(true) => simplify(andJoin(es), path withCond e)
      case BooleanLiteral(false) => BooleanLiteral(false)
      case re =>
        val res = simplify(andJoin(es), path withCond re)
        if (res == BooleanLiteral(false)) {
          BooleanLiteral(false)
        } else {
          and(re, res)
        }
    }

    case Or(e +: es) => simplify(e, path) match {
      case BooleanLiteral(true) => BooleanLiteral(true)
      case BooleanLiteral(false) => simplify(orJoin(es), path)
      case re =>
        val res = simplify(orJoin(es), path withCond not(re))
        if (res == BooleanLiteral(true)) {
          BooleanLiteral(true)
        } else {
          or(re, res)
        }
    }

    case IfExpr(c, t, e) => simplify(c, path) match {
      case BooleanLiteral(true) => simplify(t, path)
      case BooleanLiteral(false) => simplify(e, path)
      case rc =>
        val rt = simplify(t, path withCond rc)
        val re = simplify(e, path withCond not(rc))
        if (rt == re) {
          rt
        } else {
          ifExpr(rc, rt, re)
        }
    }

    case Assume(pred, body) =>
      simplify(body, path withCond pred)

    // case Assume(pred, body) => simplify(pred, path) match {
    //   case BooleanLiteral(true) => simplify(body, path)
    //   case BooleanLiteral(false) =>
    //     val rb = simplify(body, path)
    //     Assume(BooleanLiteral(false), rb)
    //   case rp =>
    //     val rb = simplify(body, path withCond rp)
    //     Assume(rp, rb)
    // }

    case IsInstanceOf(ADT(tpe1, args), tpe2: ADTType) if !tpe2.getADT.definition.isSort =>
      // val re = (tpe1.getADT.toConstructor.fields zip args)
      //   .foldRight(BooleanLiteral(tpe1.id == tpe2.id): Expr) {
      //     case ((vd, e), body) => Let(vd.freshen, e, body)
      //   }
      // simplify(re, path)

      BooleanLiteral(tpe1.id == tpe2.id)

    case IsInstanceOf(e, tpe: ADTType) =>
      val re = simplify(e, path)
      if (tpe.getADT.definition.isSort) {
        BooleanLiteral(true)
      } else isInstanceOf(re, tpe, path) match {
        case Some(b) => BooleanLiteral(b)
        case None => IsInstanceOf(re, tpe)
      }

    case AsInstanceOf(e, tpe: ADTType) =>
      val re = simplify(e, path)
      re.getType match {
        case reTpe: ADTType if reTpe.id == tpe.id => re
        case _ => AsInstanceOf(re, tpe)
      }

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2), Let(vd, e1, e2)), path)

    case Let(vd, v: Variable, b) =>
      simplify(replaceFromSymbols(Map(vd -> v), b), path)

//     case let @ Let(vd, e, b) =>
//       simplifyCache.get(let)
//         .filter(_._1.subsumes(path))
//         .map(p => p._2)
//         .getOrElse {
//           val re = simplify(e, path)
//           val rb =  simplify(b, path withBinding (vd -> re))
//           replaceFromSymbols(Map(vd -> re), rb)
//         }

    // case let @ Let(vd, e, b) =>
    //   val re = simplify(e, path)
    //   val rb = simplify(b, path withBinding (vd -> re))
    //   simplify(replaceFromSymbols(Map(vd -> re), rb), path)

    case Let(vd, ADT(tpe, es), b) if {
      val v = vd.toVariable
      def rec(e: Expr): Boolean = e match {
        case ADTSelector(`v`, id) => true
        case `v` => false
        case Operator(es, _) => es.forall(rec)
      }
      rec(b)
    } =>
      val tadt = tpe.getADT.toConstructor
      val vds = tadt.fields.map(_.freshen)
      val selectors = tadt.fields.map(f => ADTSelector(vd.toVariable, f.id))
      val selectorMap: Map[Expr, Expr] = (selectors zip vds.map(_.toVariable)).toMap
      simplify((vds zip es).foldRight(replace(selectorMap, b)) { case ((vd, e), b) => Let(vd, e, b) }, path)

    // @nv: Simplifying lets can lead to exponential simplification cost.
    //      The `simplifyCache` greatly reduces the cost of simplifying lets but
    //      there are still corner cases that will make this expensive.
    //      In `assumeChecked` mode, the cost should be lower as most lets with
    //      `insts <= 1` will be inlined immediately.
    case let @ Let(vd, e, b) =>
      val re = simplify(e, path)
      re match {
        case Tuple(es) if {
          val v = vd.toVariable
          def rec(e: Expr): Boolean = e match {
            case TupleSelect(`v`, idx) => true
            case `v` => false
            case Operator(es, _) => es.forall(rec)
          }
          rec(b)
        } =>
          val indexes = (1 to es.length).toSeq
          val selectors = indexes.map(idx => TupleSelect(vd.toVariable, idx))
          val vds = indexes.map(idx => ValDef(FreshIdentifier(s"${vd.id}_$idx"), es(idx - 1).getType))
          val selectorMap: Map[Expr, Expr] = (selectors zip vds.map(_.toVariable)).toMap
          simplify((vds zip es).foldRight(replace(selectorMap, b)) { case ((vd, e), b) => Let(vd, e, b) }, path)

        case ADT(tpe, es) if {
          val v = vd.toVariable
          def rec(e: Expr): Boolean = e match {
            case ADTSelector(`v`, id) => true
            case `v` => false
            case Operator(es, _) => es.forall(rec)
          }
          rec(b)
        } =>
          val tadt = tpe.getADT.toConstructor
          val vds = tadt.fields.map(_.freshen)
          val selectors = tadt.fields.map(f => ADTSelector(vd.toVariable, f.id))
          val selectorMap: Map[Expr, Expr] = (selectors zip vds.map(_.toVariable)).toMap
          simplify((vds zip es).foldRight(replace(selectorMap, b)) { case ((vd, e), b) => Let(vd, e, b) }, path)

        // @nv: Simplifying lets can lead to exponential simplification cost.
        //      The `simplifyCache` greatly reduces the cost of simplifying lets but
        //      there are still corner cases that will make this expensive.
        //      In `assumeChecked` mode, the cost should be lower as most lets with
        //      `insts <= 1` will be inlined immediately.
        case e =>
          val re = simplify(e, path)
          val rb = simplify(b, path withBinding (vd -> re))
          val v = vd.toVariable
          lazy val insts = count { case `v` => 1 case _ => 0 }(rb)
          lazy val inLambda = exists { case l: Lambda => variablesOf(l) contains v case _ => false }(rb)
          lazy val immediateCall = existsWithPC(rb) { case (`v`, path) => path.isEmpty case _ => false }
          lazy val containsLambda = exists { case l: Lambda => true case _ => false }(re)

          if (
            ((!inLambda || (inLambda && !containsLambda)) && insts <= 1) ||
            (!inLambda && immediateCall && insts == 1)
          ) {
            simplify(replaceFromSymbols(Map(vd -> re), rb), path)
          } else {
            val let = Let(vd, re, rb)
            re match {
              case l: Lambda =>
                val inlined = inlineLambdas(let)
                if (inlined != let) simplify(inlined, path)
                else let
              case _ => let
            }
          }
      }

    case Equals(e1: Literal[_], e2: Literal[_]) =>
      BooleanLiteral(e1 == e2)

    case Equals(e1: Terminal, e2: Terminal) if e1 == e2 =>
      BooleanLiteral(true)

    case Equals(a, b) => (simplify(a, path), simplify(b, path)) match {
      case (ra, rb) if ra == rb => BooleanLiteral(true)
      case (ra, rb) => Equals(ra, rb)
    }

    case Not(e) =>
      val re = simplify(e, path)
      not(re)

    case fi @ FunctionInvocation(id, tps, args) =>
      val tfd = getFunction(id, tps)
      val rargs = args.map(simplify(_, path))

      val res = if (isRecursive(tfd.fd.id)) {
        // println(s"$id is recursive")
        val expr = tfd.withParamSubst(rargs, tfd.fullBody)
        // println(s"after subst: $expr")
        tryReduce(expr, path) match {
          case Some(res) =>
            // println(s"$expr can be reduced to $res")
            simplify(res, path)
          case None =>
            FunctionInvocation(id, tps, rargs)
        }
      } else {
        // println(s"$id is not recursive")
        val expr = tfd.withParamSubst(rargs, tfd.fullBody)
        simplify(expr, path)
      }

      // println(s"BEFORE:\n$fi\n")
      // println(s"AFTER:\n$res\n")
      res

    case adtSel @ ADTSelector(expr, sel) => simplify(expr, path) match {
      case ADT(adt, args) =>
        simplify(args(adtSel.selectorIndex), path)

      case AsInstanceOf(ADT(adt, args), tpe) =>
        simplify(args(adtSel.selectorIndex), path)

      case other =>
        adtSelector(other, sel)
    }

    case sel @ TupleSelect(t, idx) => simplify(t, path) match {
      case Tuple(exprs) =>
        simplify(exprs(sel.selectorIndex), path)

      case other =>
        TupleSelect(other, idx)
    }

    case ADT(tpe, args)      => simplifyAndCons(args, path, adt(tpe, _))
    case Tuple(es)           => simplifyAndCons(es, path, tupleWrap)
    case UMinus(t)           => simplifyAndCons(Seq(t), path, es => uminus(es.head))
    case Plus(l, r)          => simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)))
    case Minus(l, r)         => simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)))
    case Times(l, r)         => simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)))
    case Forall(args, body)  => simplifyAndCons(Seq(body), path, es => simpForall(args, es.head))

    case Application(e, es)  => simplify(e, path) match {
      case l: Lambda =>
        val rargs = es.map(simplify(_, path))
        val res = l.withParamSubst(rargs, l.body)
        simplify(res, path)

      case Assume(pred, l: Lambda) =>
        val rargs = es.map(simplify(_, path))
        val res = l.withParamSubst(rargs, l.body)
        simplify(res, path withCond pred)

      case re =>
        application(re, es.map(simplify(_, path)))
    }

    case e =>
      // println("Unhandled tree: " + e.getClass)
      dynStack.value = 0 :: dynStack.value
      val re = super.rec(e, path)
      // val (rpure, rest) = dynPurity.value.splitAt(dynStack.value.head)
      dynStack.value = dynStack.value.tail
      // dynPurity.value = rest
      re
  }

  private def simplifyAndCons(es: Seq[Expr], path: Env, cons: Seq[Expr] => Expr): Expr = {
    cons(es.map(simplify(_, path)))
  }

  private def tryReduce(expr: Expr, path: Env): Option[Expr] = expr match {
    case IfExpr(cnd, thn, els) => simplify(cnd, path) match {
      case BooleanLiteral(true) => Some(thn)
      case BooleanLiteral(false) => Some(els)
      case rc => evalCond(rc) match {
        case Some(true) => Some(thn)
        case Some(false) => Some(els)
        case None => None
      }
    }

    case Assume(pred, body) =>
      val bl = simplify(pred, path)
      tryReduce(body, path withCond bl)

    case let @ Let(vd, e, b) => tryReduce(e, path) match {
      case Some(re) =>
        val rb = tryReduce(b, path withBinding (vd -> re)).getOrElse(b)
        Some(Let(vd, re, rb))

      case None =>
        tryReduce(b, path withBinding (vd -> e))
    }

    case _ =>
      None
  }

  private def evalCond(cnd: Expr): Option[Boolean] = cnd match {
    case BooleanLiteral(b) => Some(b)
    case Let(_, _, b) => evalCond(b)
    case Assume(pred, body) => evalCond(body)
    case _ => None
  }

  override protected def rec(e: Expr, path: Env): Expr = {
    dynStack.value = if (dynStack.value.isEmpty) Nil else (dynStack.value.head + 1) :: dynStack.value.tail
    val re = simplify(e, path)
    // dynPurity.value = if (dynStack.value.isEmpty) dynPurity.value else pe :: dynPurity.value
    re
  }
}
