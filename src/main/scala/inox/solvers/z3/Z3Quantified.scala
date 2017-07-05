/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers.z3

import utils._
import solvers.{z3 => _, _}
import quantified._

import z3.scala._

trait Z3Quantified extends AbstractZ3Solver { self =>

  import program._
  import program.trees._
  import program.symbols._

  import SolverResponses._

  override val name = "z3-q"

  override
  protected[z3] def toZ3FormulaRec(expr: Expr)(implicit bindings: Map[Variable, Z3AST]): Z3AST = expr match {

    case Forall(Seq(), body) =>
      toZ3FormulaRec(body)

    case Forall(args, body) =>
      val bounds = args.map(arg => declareVariable(arg.toVariable))
      val z3Body = toZ3FormulaRec(body)
      z3.mkForAllConst(0, Seq(), bounds, z3Body)

    case _ =>
      super.toZ3FormulaRec(expr)
  }

}
