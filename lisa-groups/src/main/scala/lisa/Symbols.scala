package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween}

object Symbols extends lisa.Main:
  val e = variable[Ind]

  val G = variable[Ind]
  val Pr = variable[Ind]
  val H = variable[Ind]

  val * = variable[Ind]
  val ** = variable[Ind]

  inline def op(x: Expr[Ind], * : Expr[Ind], y: Expr[Ind]) = app(*)((x, y))

  val op2 = variable[Ind >>: Ind >>: Ind]