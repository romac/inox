/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

import ast._
import utils._

trait Monomorphize extends LiveSymbolTransformer { self =>

  val ctx: Context

  val t: self.s.type = self.s

  import s._

  def transform(syms: s.Symbols, expr: s.Expr): (t.Symbols, t.Expr) = {
    val (newSyms, monoExpr) = fixpoint(monomorphize)((syms, expr))

    val monoFunctions = newSyms.functions.values.toSeq.filter(_.tparams.isEmpty)
    val monoSyms = NoSymbols
      .withFunctions(monoFunctions)
      .withADTs(newSyms.adts.values.toSeq)

    (monoSyms, monoExpr)
  }

  private def monomorphize(input: (s.Symbols, s.Expr)): (s.Symbols, s.Expr) = {
    implicit val syms = input._1

    val (expr, adts) = instantiateGenericAssertions(input._2)
    val entry = entryPoint(expr)(syms.withADTs(adts.toSeq))

    val callGraph = new TypedCallGraph {
      val trees: s.type = s
      val symbols = syms.withFunctions(Seq(entry))
    }

    val calls = callGraph.transitiveCallees(entry)
    val paramCalls = calls.filter(_._2.nonEmpty)
    if (paramCalls.isEmpty) return (syms, expr)

    val (beforePoly, beforeMono) = paramCalls partition {
      case (fd, tps) => tps exists syms.isParametricType
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

  private def monomorphizeInvocations(map: Map[TypedFunDef, FunDef])(fd: FunDef)(implicit syms: Symbols): FunDef = {
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

  private def monomorphizeFunction(fd: FunDef, tps: Seq[Type])(implicit syms: Symbols): Option[(TypedFunDef, FunDef)] = {
    implicit val printerOpts: PrinterOptions = PrinterOptions.fromSymbols(syms, ctx)

    val isPoly = tps exists syms.isParametricType
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

  def apply(trees: Trees, context: Context): Monomorphize {
    val s: trees.type
    val ctx: context.type
  } = new Monomorphize {
    override val s: trees.type = trees
    override val ctx: context.type = context
  }

}
