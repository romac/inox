/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package quantified

import tip._

import scala.language.existentials

class TipTestSuite extends QuantifiedTestSuite with ResourceUtils {

  override def configurations = Seq(
    Seq(optSelectedSolvers(Set("nativez3-q")), optCheckModels(true))
    // Seq(optSelectedSolvers(Set("smt-cvc4-q")), optCheckModels(true))
  )

  override protected def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  private def ignoreFile(solver: String, fileName: String): Boolean = {
    // test containing list of booleans, so CVC4 will crash on this
    // See http://church.cims.nyu.edu/bugzilla3/show_bug.cgi?id=500
    (solver == "smt-cvc4-q" && fileName.endsWith("List-fold.tip")) ||
    // Z3 and CVC4 binaries are exceedingly slow on this benchmark
    (solver == "smt-cvc4-q" && fileName.endsWith("BinarySearchTreeQuant.scala-2.tip")) ||
    // use non-linear operators that aren't supported in CVC4
    (solver == "smt-cvc4-q" && fileName.endsWith("LetsInForall.tip")) ||
    (solver == "smt-cvc4-q" && fileName.endsWith("Instantiation.scala-0.tip")) ||
    (solver == "smt-cvc4-q" && fileName.endsWith("Weird.scala-0.tip")) ||
    (solver == "smt-cvc4-q" && fileName.endsWith("Soundness.scala-0.tip")) ||
    (solver == "smt-cvc4-q" && fileName.endsWith("Soundness2.scala-0.tip"))
  }

  private def ignore(ctx: Context, file: java.io.File): FilterStatus =
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) if ignoreFile(solver, file.getName) => Ignore
      case _ => Test
    }

  // for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
  //   test(s"SAT - ${file.getName}", ignore(_, file)) { ctx =>
  //     for ((syms, expr) <- new Parser(file).parseScript) {
  //       val program = InoxProgram(ctx, syms)
  //       assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isSAT)
  //     }
  //   }
  // }

  for (file <- resourceFiles("regression/tip/quantified", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}", ignore(_, file)) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(program.getSolver.withTimeout(500)).solveSAT(expr).isUNSAT)
      }
    }
  }

  // for (file <- resourceFiles("regression/tip/UNKNOWN", _.endsWith(".tip"))) {
  //   test(s"UNKNOWN - ${file.getName}", ignore(_, file)) { ctx0 =>
  //     val ctx = ctx0.copy(options = ctx0.options + optCheckModels(false))
  //     for ((syms, expr) <- new Parser(file).parseScript) {
  //       val program = InoxProgram(ctx, syms)
  //       val api = SimpleSolverAPI(program.getSolver)
  //       val res = api.solveSAT(expr)
  //       assert(!res.isSAT && !res.isUNSAT)
  //       assert(ctx.reporter.errorCount > 0)
  //     }
  //   }
  // }
}
