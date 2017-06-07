/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

trait QuantifiedSolver extends Solver { self =>

  import program.trees._
  import SolverResponses._

  type UnderlyingSolver <: AbstractSolver

  def newSolver(p: Program { val trees: program.trees.type }): UnderlyingSolver { val program: p.type }

  def getFunctionMeaning(fd: FunDef): Forall = {
    val body = Equals(
      FunctionInvocation(fd.id, Seq.empty, fd.params.map(_.toVariable)),
      fd.fullBody
    )

    Forall(fd.params, body)
  }

}

