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
    val program = new Program {
      val trees: sourceProgram.trees.type = sourceProgram.trees
      val symbols = sourceProgram.symbols
      val ctx = sourceProgram.ctx
    }

    (program, expr)
  }

}

object Monomorphize {
  def apply(p: Program): Monomorphize {
    val sourceProgram: p.type
  } = new Monomorphize {
    val sourceProgram: p.type = p
  }
}
