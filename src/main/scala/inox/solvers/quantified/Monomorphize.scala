/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

import ast._
import utils._

trait Monomorphize { self =>

  val sourceProgram: Program

  import sourceProgram._
  import sourceProgram.trees._
  import sourceProgram.trees.dsl._
  import sourceProgram.symbols._

  def transform(expr: Expr): (Program { val trees: sourceProgram.trees.type }, Expr) = {
    val (monoSyms, monoExpr) = fixpoint(monomorphizeProgram)((sourceProgram.symbols, expr))

    val program = new Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = monoSyms
      val ctx = sourceProgram.ctx
    }

    println("\nprogram:\n\n" + program)
    println("\nexpr: " + monoExpr)

    (program, monoExpr)
  }

  private def monomorphizeProgram(input: (Symbols, Expr)): (Symbols, Expr) = {
    implicit val syms = input._1

    val (expr, adts) = instantiateGenericAssertions(input._2)
    val entry = entryPoint(expr)

    val callGraph = new TypedCallGraph {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = syms.withFunctions(Seq(entry))
    }

    val calls = callGraph.transitiveCallees(entry)

    val paramCalls = calls.filter(_._2.nonEmpty)

    if (paramCalls.isEmpty) return (syms, expr)

    val (beforePoly, beforeMono) = paramCalls partition {
      case (fd, tps) => tps exists isParametricType
    }

    val monoMap = beforeMono.map(_monomorphizeFunction).flatten.toMap
    val callsLeft = calls.map(_._1) -- monoMap.keys.map(_.fd).toSet

    val applied = (monoMap.values.toSet ++ callsLeft) map monomorphizeInvocations(monoMap)
    val newEntry = monomorphizeInvocations(monoMap)(entry)

    val newSyms = NoSymbols
      .withADTs(syms.adts.values.toSeq ++ adts.toSeq)
      .withFunctions(applied.toSeq)

    println(newSyms)

    (newSyms, newEntry.fullBody)
  }

  private def instantiateGenericAssertions(expr: Expr): (Expr, Set[ADTDefinition]) = {
    var adts = new IncrementalMap[TypeParameter, (ADTSort, ADTConstructor)]

    def go(expr: Expr): Option[Expr] = expr match {
      case Forall(args, body) =>
        args.zip(args.map(_.tpe)) foreach { case (arg, tp) =>
          typeParamsOf(tp) foreach { param =>
            adts.cached(param) {
              val sortId = param.id.freshen
              val consId = param.id.freshen
              val cons = new ADTConstructor(consId, Seq.empty, Some(sortId), Seq.empty, Set.empty)
              val sort = new ADTSort(sortId, Seq.empty, Seq(consId), Set.empty)
              (sort, cons)
            }
          }
        }

        val substs = adts.iterator.map(s => (s._1, s._2._1.typed.toType)).toMap
        val newArgs = args map { arg =>
          arg.copy(tpe = typeOps.replace(substs.asInstanceOf[Map[Type, Type]], arg.tpe))
        }

        Some(Forall(newArgs, instantiateType(body, substs)))

      case _ =>
        None
    }

    val res = exprOps.postMap(go)(expr)
    val (sorts, conss) = (adts.values.map(_._1).toSet, adts.values.map(_._2).toSet)
    (res, sorts ++ conss)
  }

  private def monomorphizeInvocations(map: Map[TypedFunDef, FunDef])(fd: FunDef): FunDef = {
    def go(expr: Expr): Option[Expr] = expr match {
      case fi @ FunctionInvocation(id, tps, args) if map contains fi.tfd =>
        val mono = map(fi.tfd)

        val newArgs = args.zip(fi.tfd.params).map {
          case (arg: Variable, param) if arg.getType != param.tpe =>
            arg.copy(tpe = param.tpe)

          case (arg, _) =>
            arg
        }

        Some(FunctionInvocation(mono.id, Seq.empty, newArgs))

      case _ =>
        None
    }

    fd.copy(fullBody = exprOps.postMap(go)(fd.fullBody))
  }

  private val _monomorphizeFunction = (monomorphizeFunction _).tupled

  private def monomorphizeFunction(fd: FunDef, tps: Seq[Type]): Option[(TypedFunDef, FunDef)] = {
    val isPoly = tps exists isParametricType

    if (isPoly) return None

    val monoId = FreshIdentifier(s"${fd.id}_mono_${tps mkString "$"}")
    val tfd = fd.typed(tps)

    val mono = new FunDef(monoId, Seq.empty, tfd.params, tfd.returnType, tfd.fullBody, fd.flags)

    Some(tfd, mono)
  }

  private val entryId = FreshIdentifier("entry")

  private def entryPoint(body: Expr)(implicit syms: Symbols): FunDef =
    new FunDef(entryId, Seq.empty, Seq.empty, body.getType, body, Set.empty)

}

object Monomorphize {
  def apply(p: Program): Monomorphize {
    val sourceProgram: p.type
  } = new Monomorphize {
    val sourceProgram: p.type = p
  }
}
