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
    val (syms, monoExpr) = fixpoint(monomorphizeProgram)((sourceProgram.symbols, expr))

    val monoFunctions = syms.functions.values.toSeq.filter(_.tparams.isEmpty)
    val monoSyms = NoSymbols.withFunctions(monoFunctions).withADTs(syms.adts.values.toSeq)

    val program = new Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = monoSyms
      val ctx = sourceProgram.ctx
    }

    (program, monoExpr)
  }

  private def monomorphizeProgram(input: (Symbols, Expr)): (Symbols, Expr) = {
    implicit val syms = input._1

    val (expr, adts) = instantiateGenericAssertions(input._2)
    val entry = entryPoint(expr)(syms.withADTs(adts.toSeq))

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

    val monoMap = beforeMono.map((monomorphizeFunction _).tupled).flatten.toMap
    val callsLeft = calls.map(_._1) -- monoMap.keys.map(_.fd).toSet

    val applied = (monoMap.values.toSet ++ callsLeft) map monomorphizeInvocations(monoMap)
    val newEntry = monomorphizeInvocations(monoMap)(entry)

    val newSyms = NoSymbols
      .withADTs(syms.adts.values.toSeq ++ adts.toSeq)
      .withFunctions(applied.toSeq)

    (newSyms, newEntry.fullBody)
  }

  private def instantiateGenericAssertions(expr: Expr)(implicit syms: Symbols): (Expr, Set[ADTDefinition]) = {
    val adts = new IncrementalMap[TypeParameter, ADTConstructor]

    val substs = syms.typeParamsOf(expr) map { param =>
      val adt = adts.cached(param) {
        val consId = FreshIdentifier(param.id.name ++ "#")
        new ADTConstructor(consId, Seq.empty, None, Seq.empty, Set.empty)
      }

      param -> adt.typed.toType
    }

    val res = syms.instantiateType(expr, substs.toMap)

    (res, adts.values.toSet)
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

  private def monomorphizeFunction(fd: FunDef, tps: Seq[Type]): Option[(TypedFunDef, FunDef)] = {
    val isPoly = tps exists isParametricType
    if (isPoly) return None

    val monoId = FreshIdentifier(s"${fd.id}_mono_${tps.map(_.compactString) mkString "-"}")
    val tfd = fd.typed(tps)

    val mono = new FunDef(monoId, Seq.empty, tfd.params, tfd.returnType, tfd.fullBody, fd.flags)

    Some(tfd, mono)
  }

  private val entryId = FreshIdentifier("entry")

  private def entryPoint(body: Expr)(syms: Symbols): FunDef = {
    new FunDef(entryId, Seq.empty, Seq.empty, body.getType(syms), body, Set.empty)
  }

}

object Monomorphize {
  def apply(p: Program): Monomorphize {
    val sourceProgram: p.type
  } = new Monomorphize {
    val sourceProgram: p.type = p
  }
}
