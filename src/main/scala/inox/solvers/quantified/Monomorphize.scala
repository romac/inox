/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package quantified

import utils._

trait Monomorphize { self =>

  val sourceProgram: Program

  import sourceProgram._
  import sourceProgram.trees._
  import sourceProgram.trees.dsl._
  import sourceProgram.symbols._

  def transform(expr: Expr): (Program { val trees: sourceProgram.trees.type }, Expr) = {
    val (monoSyms, monoExpr) = fixpoint(sourceProgram.symbols, expr)

    val program = new Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = monoSyms
      val ctx = sourceProgram.ctx
    }

    (program, monoExpr)
  }

  private def fixpoint(syms: Symbols, expr: Expr): (Symbols, Expr) = {
    (syms, expr)
  }

}

object Monomorphize {
  def apply(p: Program): Monomorphize {
    val sourceProgram: p.type
  } = new Monomorphize {
    val sourceProgram: p.type = p
  }
}
