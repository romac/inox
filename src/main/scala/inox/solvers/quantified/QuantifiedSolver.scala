/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

trait QuantifiedSolver { self: Solver =>

  import program.trees._

  def getFunctionMeaning(fd: FunDef)(implicit syms: Symbols): Option[Forall] = {
    if (fd.flags.contains(Uninterpreted)) return None

    val ufd = unroll(fd)
    val body = Equals(
      FunctionInvocation(ufd.id, Seq.empty, ufd.params.map(_.toVariable)),
      ufd.fullBody
    )

    Some(Forall(ufd.params, body))
  }

  private def unroll(fd: FunDef)(implicit syms: Symbols): FunDef = {
    if (!fd.isRecursive) return fd

    def recCallsCollector(expr: Expr): Set[FunctionInvocation] = expr match {
      case fi @ FunctionInvocation(id, _, _) if fd.id == id => Set(fi)
      case _ => Set()
    }

    val recCalls = exprOps.collect(recCallsCollector)(fd.fullBody)

    val inlined: Map[Expr, Expr] = recCalls.toSeq.map(fi => fi -> fi.inlined).toMap
    val unrolledBody = exprOps.replace(inlined, fd.fullBody)

    val ufd = fd.copy(fullBody = unrolledBody)

    println("Unrolled:")
    println(ufd)

    ufd
  }

}
