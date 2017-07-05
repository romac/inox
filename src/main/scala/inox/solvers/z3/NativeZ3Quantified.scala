/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala._

import ast.ProgramEncoder
import utils._
import solvers.{z3 => _, _}
import quantified._

trait NativeZ3Quantified extends QuantifiedSolver { self =>

  import program.trees._
  import SolverResponses._

  override
  lazy val name = "nativez3-q"

  protected implicit val semantics: program.Semantics

  type UnderlyingSolver = Z3Quantified

  protected var underlying: Z3Quantified {
    val program: self.program.type
  } = _

  def getUnderlying = {
    Option(underlying)
  }

  private[this] def toUnderlying(expr: Expr): Z3AST = {
    underlying.toZ3Formula(expr)
  }

  override
  def newSolver(p: Program { val trees: program.trees.type }): Z3Quantified { val program: p.type } = {
    new {
      val program: p.type = p
      val options = self.options
    } with Z3Quantified {
      lazy val semantics = program.getSemantics(null)
    }
  }

  def assertCnstr(expr: Expr): Unit = {
    val monomorphize = Monomorphize(program)
    val (monoProgram, monoExpr) = monomorphize.transform(expr)

    val lambdaEncoder = LambdaEncoder(monoProgram)
    val (finalProgram, finalExpr) = lambdaEncoder.transform(monoExpr)

    import finalProgram._

    println(finalProgram + "\n\n" + finalExpr + "\n")

    val solver = newSolver(finalProgram)
    underlying = solver.asInstanceOf[Z3Quantified { val program: self.program.type }] // @romac - FIXME

    val functions = finalProgram.symbols.functions.values.toSeq
    functions
      .flatMap(getFunctionMeaning(_))
      .map(toUnderlying(_))
      .foreach(solver.assertCnstr(_))

    solver.assertCnstr(toUnderlying(finalExpr))
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.convert(underlying.check(config),
      (model: Z3Model) => underlying.extractModel(model),
      underlying.extractUnsatAssumptions)

  override
  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    config.convert(underlying.checkAssumptions(config)(assumptions.map(underlying.toZ3Formula(_))),
      (model: Z3Model) => underlying.extractModel(model),
      underlying.extractUnsatAssumptions)

  def free(): Unit      = getUnderlying.foreach(_.free())
  def pop(): Unit       = getUnderlying.foreach(_.pop())
  def push(): Unit      = getUnderlying.foreach(_.push())
  def reset(): Unit     = getUnderlying.foreach(_.reset())
  def interrupt(): Unit = getUnderlying.foreach(_.interrupt())

}
