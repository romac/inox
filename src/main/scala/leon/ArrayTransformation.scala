package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object ArrayTransformation extends Pass {

  val description = "Add bound checking for array access and remove side effect array update operations"

  def apply(pgm: Program): Program = {

    val allFuns = pgm.definedFunctions
    val newFuns: Seq[Definition] = allFuns.map(fd => {
      if(fd.hasImplementation) {
        val body = fd.body.get
        id2id = Map()
        val args = fd.args
        val newFd = 
          if(args.exists(vd => containsArrayType(vd.tpe))) {
            println("args has array")
            val newArgs = args.map(vd => {
              val freshId = FreshIdentifier(vd.id.name).setType(TupleType(Seq(vd.tpe, Int32Type)))
              id2id += (vd.id -> freshId)
              val newTpe = transform(vd.tpe)
              VarDecl(freshId, newTpe)
            })
            val freshFunName = FreshIdentifier(fd.id.name)
            val freshFunDef = new FunDef(freshFunName, fd.returnType, newArgs)
            freshFunDef.fromLoop = fd.fromLoop
            freshFunDef.parent = fd.parent
            freshFunDef.precondition = fd.precondition
            freshFunDef.postcondition = fd.postcondition
            freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
            freshFunDef
          } else fd
        val newBody = transform(body)
        newFd.body = Some(newBody)
        newFd
      } else fd
    })

    val Program(id, ObjectDef(objId, _, invariants)) = pgm
    val allClasses: Seq[Definition] = pgm.definedClasses
    Program(id, ObjectDef(objId, allClasses ++ newFuns, invariants))
  }

  private var id2id: Map[Identifier, Identifier] = Map()

  private def transform(tpe: TypeTree): TypeTree = tpe match {
    case ArrayType(base) => TupleType(Seq(ArrayType(transform(base)), Int32Type))
    case TupleType(tpes) => TupleType(tpes.map(transform))
    case t => t
  }
  private def containsArrayType(tpe: TypeTree): Boolean = tpe match {
    case ArrayType(base) => true
    case TupleType(tpes) => tpes.exists(containsArrayType)
    case t => false
  }


  private def transform(expr: Expr): Expr = expr match {
    case fill@ArrayFill(length, default) => {
      var rLength = transform(length)
      val rDefault = transform(default)
      val rFill = ArrayMake(rDefault).setType(fill.getType)
      Tuple(Seq(rFill, length)).setType(TupleType(Seq(fill.getType, Int32Type)))
    }
    case sel@ArraySelect(a, i) => {
      val ar = transform(a)
      val ir = transform(i)
      val length = TupleSelect(ar, 2).setType(Int32Type)
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        ArraySelect(TupleSelect(ar, 1), ir).setType(sel.getType),
        Error("Index out of bound").setType(sel.getType)
      ).setType(sel.getType)
    }
    case ArrayUpdate(a, i, v) => {
      val ar = transform(a)
      val ir = transform(i)
      val vr = transform(v)
      val Variable(id) = ar
      val length = TupleSelect(ar, 2).setType(Int32Type)
      val array = TupleSelect(ar, 1).setType(ArrayType(v.getType))
      //val Tuple(Seq(Variable(id), length)) = ar
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        Block(Seq(Assignment(id, Tuple(Seq(ArrayUpdated(array, i, v).setType(array.getType), length)).setType(TupleType(Seq(array.getType, Int32Type))))), IntLiteral(0)),
        Error("Index out of bound").setType(Int32Type)
      ).setType(Int32Type)
    }
    case ArrayLength(a) => {
      val ar = transform(a)
      TupleSelect(ar, 2).setType(Int32Type)
    }
    case Let(i, v, b) => {
      val vr = transform(v)
      v.getType match {
        case ArrayType(_) => {
          val freshIdentifier = FreshIdentifier("t").setType(vr.getType)
          id2id += (i -> freshIdentifier)
          val br = transform(b)
          LetVar(freshIdentifier, vr, br)
        }
        case _ => {
          val br = transform(b)
          Let(i, vr, br)
        }
      }
    }
    case LetVar(id, e, b) => {
      val er = transform(e)
      val br = transform(b)
      LetVar(id, er, br)
    }

    case ite@IfExpr(c, t, e) => {
      val rc = transform(c)
      val rt = transform(t)
      val re = transform(e)
      IfExpr(rc, rt, re).setType(rt.getType)
    }

    case m @ MatchExpr(scrut, cses) => {
      val scrutRec = transform(scrut)
      val csesRec = cses.map{
        case SimpleCase(pat, rhs) => SimpleCase(pat, transform(rhs))
        case GuardedCase(pat, guard, rhs) => GuardedCase(pat, transform(guard), transform(rhs))
      }
      val tpe = csesRec.head.rhs.getType
      MatchExpr(scrutRec, csesRec).setType(tpe).setPosInfo(m)
    }

    //case LetDef(fd, b) => 

    case n @ NAryOperator(args, recons) => recons(args.map(transform)).setType(n.getType)
    case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2)).setType(b.getType)
    case u @ UnaryOperator(a, recons) => recons(transform(a)).setType(u.getType)

    case v @ Variable(id) => if(id2id.isDefinedAt(id)) Variable(id2id(id)) else v
    case (t: Terminal) => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)

  }

}
