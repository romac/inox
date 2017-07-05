/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package quantified

trait QuantifiedTestSuite extends TestSuite {

  override def configurations = for {
    solverName        <- Seq("nativez3-q") // Seq("nativez3-q", "smt-cvc4-q")
    checkModels       <- Seq(false)
    feelingLucky      <- Seq(false)
    unrollAssumptions <- Seq(false)
    modelFinding      <- Seq(0)
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(checkModels),
    unrolling.optFeelingLucky(feelingLucky),
    unrolling.optUnrollAssumptions(unrollAssumptions),
    unrolling.optModelFinding(modelFinding),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )

}
