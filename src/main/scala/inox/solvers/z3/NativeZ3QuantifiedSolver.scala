/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package solvers
package z3

import _root_.z3.scala._

import utils._
import solvers.{z3 => _, _}
import quantified._

trait NativeZ3QuantifiedSolver extends Solver with QuantifiedSolver { self =>

  override lazy val name = "nativez3-q"

  import program.trees._
  import SolverResponses._

  protected implicit val semantics: program.Semantics

  protected var underlying: Z3Quantified {
    val program: self.program.type
  } = _

  private def getUnderlying = {
    Option(underlying)
  }

  private def toUnderlying(expr: Expr): Z3AST = {
    underlying.toZ3Formula(expr)
  }

  private type Prog = Program { val trees: self.program.trees.type }

  private def newSolver(p: Prog, syms: Symbols): Z3Quantified { val program: Prog } = {
    val newProgram = new Program {
      val trees = p.trees
      val symbols = syms
      val ctx = p.ctx
    }

    new {
      val program = newProgram
      val options = self.options
    } with Z3Quantified {
      lazy val semantics = program.getSemantics(null)
    }
  }

  def assertCnstr(expr: Expr): Unit = {
    val monomorphize = Monomorphize(program.trees, program.ctx)
    val lambdaEncoder = LambdaEncoder(program.trees, program.ctx)
    val transformer = monomorphize andThen lambdaEncoder

    val (syms, finalExpr) = transformer.transform(program.symbols, expr)

    println(syms + "\n\n" + finalExpr + "\n")

    val solver = newSolver(program.asInstanceOf[Prog], syms)

    // @romac - FIXME
    underlying = solver.asInstanceOf[Z3Quantified { val program: self.program.type }]

    val functions = syms.functions.values.toSeq

    functions
      .flatMap(getFunctionMeaning(_)(syms))
      .map(toUnderlying(_))
      .foreach(solver.assertCnstr(_))

    val cnstr = toUnderlying(syms.simplifyForalls(finalExpr))
    solver.assertCnstr(cnstr)
  }

  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.convert(underlying.check(config),
      (model: Z3Model) => underlying.extractModel(model),
      underlying.extractUnsatAssumptions)

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    config.convert(underlying.checkAssumptions(config)(assumptions.map(underlying.toZ3Formula(_))),
      (model: Z3Model) => underlying.extractModel(model),
      underlying.extractUnsatAssumptions)

  def free(): Unit      = getUnderlying.foreach(_.free())
  def pop(): Unit       = getUnderlying.foreach(_.pop())
  def push(): Unit      = getUnderlying.foreach(_.push())
  def reset(): Unit     = getUnderlying.foreach(_.reset())
  def interrupt(): Unit = getUnderlying.foreach(_.interrupt())

}
