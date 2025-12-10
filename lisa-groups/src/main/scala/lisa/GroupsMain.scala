package lisa.maths.GroupTheory

import lisa.Main

import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau

object Example extends lisa.Main:

  // first-order variables
  val x = variable[Ind]
  val y = variable[Ind]

  val P = variable[Ind >>: Prop]

  // a simple proof with Lisa's DSL
  val helloWorld = Theorem( ∀(x,P(x)) |- ∀(x,P(x)) ) {
    assume(∀(x,P(x)))

  }


object Groups extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]

  private val G = variable[Ind]
  private val op = variable[Ind >>: Ind >>: Ind]

  val binaryOperation = DEF(λ(G, λ(op, 
    ∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G ))
  )))


  val group = DEF(λ(G, λ(op, 
    binaryOperation(G)(op)
  )))


  

