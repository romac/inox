/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils.Graphs._

trait TypedCallGraph {

  protected val trees: Trees
  import trees._
  import trees.exprOps._
  protected val symbols: Symbols

  lazy val graph: DiGraph[FunDef, LabeledEdge[Seq[Type], FunDef]] = {
    val edges = for {
      (_, fd) <- symbols.functions
      (from, tps, to) <- collect(collectCalls(fd))(fd.fullBody)
    } yield LabeledEdge(from, tps, to)

    DiGraph.fromEdges(edges)
  }

  lazy val allCalls: Set[(FunDef, FunDef, Seq[Type])] = {
    graph.E.map(e => (e._1, e._2, e.l))
  }

  private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, Seq[Type], FunDef)] = e match {
    case f @ FunctionInvocation(id, tps, _) => Set((fd, tps, symbols.getFunction(id)))
    case _ => Set()
  }

  def isRecursive(f: FunDef): Boolean = {
    graph.transitiveSucc(f) contains f
  }

  def isSelfRecursive(f: FunDef): Boolean = {
    graph.succ(f) contains f
  }

  def calls(from: FunDef, to: FunDef): Boolean = {
    graph.E exists {
      case LabeledEdge(a, _, b) => a == from && b == to
    }
  }

  def callers(to: FunDef): Set[(FunDef, Seq[Type])] = {
    graph.inEdges(to).map(e => (e._1, e.l))
  }

  def callers(tos: Set[FunDef]): Set[(FunDef, Seq[Type])] = {
    tos.flatMap(callers)
  }

  def callees(from: FunDef): Set[(FunDef, Seq[Type])] = {
    graph.succL(from)
  }

  def callees(froms: Set[FunDef]): Set[(FunDef, Seq[Type])] = {
    froms.flatMap(callees)
  }

  def transitiveCallers(to: FunDef): Set[(FunDef, Seq[Type])] = {
    graph.transitivePredL(to)
  }

  def transitiveCallers(tos: Set[FunDef]): Set[(FunDef, Seq[Type])] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallees(from: FunDef): Set[(FunDef, Seq[Type])] = {
    graph.transitiveSuccL(from)
  }

  def transitiveCallees(froms: Set[FunDef]): Set[(FunDef, Seq[Type])] = {
    froms.flatMap(transitiveCallees)
  }

  def transitivelyCalls(from: FunDef, to: FunDef): Boolean = {
    transitiveCallees(from) exists (_._1 == to)
  }

  lazy val stronglyConnectedComponents: Set[Set[FunDef]] = {
    graph.stronglyConnectedComponents.N
  }

  lazy val functionComponent: Map[FunDef, Set[FunDef]] = {
    val inComponents = stronglyConnectedComponents.flatMap(fds => fds.map(_ -> fds)).toMap
    inComponents ++ symbols.functions.values.filterNot(inComponents.isDefinedAt).map(_ -> Set.empty[FunDef])
  }

}

