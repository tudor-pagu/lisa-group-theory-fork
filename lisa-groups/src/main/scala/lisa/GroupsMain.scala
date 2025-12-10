package lisa.maths.GroupTheory

import lisa.kernel.proof.*
import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.*
import lisa.maths.SetTheory.Base.Singleton.*
import lisa.maths.SetTheory.Base.Singleton
import lisa.Main

import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.GroupTheory.Groups.binaryOperation
import lisa.maths.GroupTheory.Groups.binaryOperation

object Example extends lisa.Main:

  // first-order variables
  val x = variable[Ind]
  val y = variable[Ind]

  val P = variable[Ind >>: Prop]

  // a simple proof with Lisa's DSL
  val helloWorld = Theorem(∀(x, P(x)) |- ∀(x, P(x))) {
    assume(∀(x, P(x)))

  }

object Groups extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val G = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]

  val binaryOperation = DEF(λ(G, λ(op, ∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)))))

  val isIdentityElement = DEF(λ(G, λ(op, λ(x, ∀(y ∈ G, ((op(x)(y) === x) /\ (op(y)(x) === x)))))))

  val identityElement = DEF(λ(G, λ(op, ∃(x ∈ G, isIdentityElement(G)(op)(x)))))

  val associativity = DEF(λ(G, λ(op, ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))))))

  val inverseElement = DEF(λ(G, λ(op, ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))))

  val group = DEF(
    λ(
      G,
      λ(
        op,
        (binaryOperation(G)(op) /\
          identityElement(G)(op)) /\
          associativity(G)(op) /\
          inverseElement(G)(op)
      )
    )
  )

  /*
   * The most simple group:
   * G = {x}, op(x,x) = x
   *
   */
object TrivialGroup extends lisa.Main:
  private val x = variable[Ind]
  private val y = variable[Ind]

  private val e = constant[Ind]("e")

  addSymbol(e)

  private val G = singleton(e)
  // x * y = e
  private val star = DEF(λ(x, λ(y, e)))

  // prove that this simple structure is indeed
  // a group
  val trivialGroupHasBinaryOperation = Theorem(
    () |- Groups.binaryOperation(G)(star)
  ) {
    val thm2 = have(star(x)(y) === e) by Tautology.from(star.definition)
    val thm3 = have(star(x)(y) ∈ G) by Tautology.from(thm2, Singleton.membership of (x := e, y := star(x)(y)))
    val thm4 = have(x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G) by Tautology.from(thm3)
    thenHave(∀(y, x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G)) by RightForall
    val thm5 = thenHave(∀(x, ∀(y, x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G))) by RightForall
    val thm6 = have(binaryOperation(G)(star)) by Tautology.from(thm5, binaryOperation.definition of (Groups.G := G, Groups.op := star))
  }

  val trivialGroupIsGroup = Theorem(
    () |- Groups.group(G)(star)
  ) {
    have(Groups.group(G)(star)) by Tautology.from(trivialGroupHasBinaryOperation, Groups.group.definition of (Groups.G := G, Groups.op := star))
  }
