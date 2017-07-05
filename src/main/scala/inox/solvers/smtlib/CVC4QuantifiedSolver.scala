/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package smtlib

import scala.language.existentials

import _root_.smtlib.trees._

import quantified._

trait CVC4QuantifiedSolver extends Solver with QuantifiedSolver { self =>

  override lazy val name = s"smt-cvc4-q"

  import program.trees._
  import SolverResponses._

  override type Model = self.program.Model

  protected implicit val semantics: program.Semantics

  protected var underlying: CVC4Solver {
    val program: self.program.type
  } = _

  def getUnderlying = {
    Option(underlying)
  }

  private[this] type Prog = Program { val trees: self.program.trees.type }

  def newSolver(p: Prog): CVC4Solver { val program: Prog } = {
    new {
      val program: p.type = p
      val options = self.options
    } with CVC4Solver {
      lazy val semantics = program.getSemantics(null)
    }
  }

  override def assertCnstr(expr: Expr): Unit = {
    val monomorphize = Monomorphize(program)
    val (monoProgram, monoExpr) = monomorphize.transform(expr)

    val lambdaEncoder = LambdaEncoder(monoProgram)
    val (finalProgram, finalExpr) = lambdaEncoder.transform(monoExpr)

    import finalProgram._

    println(finalProgram + "\n\n" + finalExpr + "\n")

    val solver = newSolver(finalProgram)
    // @romac - FIXME
    underlying = solver.asInstanceOf[CVC4Solver { val program: self.program.type }]

    val functions = finalProgram.symbols.functions.values.toSeq
    functions
      .flatMap(getFunctionMeaning(_))
      .foreach(solver.assertCnstr(_))

      underlying.assertCnstr(finalExpr)
  }

  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    underlying.check(config)

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    underlying.checkAssumptions(config)(assumptions)

  override def free(): Unit      = getUnderlying.foreach(_.free())
  override def pop(): Unit       = getUnderlying.foreach(_.pop())
  override def push(): Unit      = getUnderlying.foreach(_.push())
  override def reset(): Unit     = getUnderlying.foreach(_.reset())
  override def interrupt(): Unit = getUnderlying.foreach(_.interrupt())

}
