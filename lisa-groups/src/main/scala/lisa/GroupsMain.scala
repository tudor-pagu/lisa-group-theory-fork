package lisa.maths.GroupTheory

import lisa.kernel.proof.*
import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.*
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.Singleton.*
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset.*
import lisa.maths.SetTheory.Base.Comprehension.*
import lisa.maths.SetTheory.Base.Replacement.*
import lisa.Main

import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.GroupTheory.Groups.binaryOperation
import lisa.maths.GroupTheory.Groups.binaryOperation
import lisa.maths.GroupTheory.Groups.isIdentityElement
import lisa.maths.GroupTheory.Groups.isIdentityElement
import lisa.maths.GroupTheory.Utils.equalityTransitivity

object Utils extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val equalityTransitivity = Lemma((x === y, y === z) |- x === z) {
    have(thesis) by Congruence
  }

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
  val h = variable[Ind]
  val g = variable[Ind]

  val G = variable[Ind]
  val H = variable[Ind]
  val C = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]

  val binaryOperation = DEF(λ(G, λ(op, ∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)))))

  val isIdentityElement = DEF(λ(G, λ(op, λ(x, x ∈ G /\ ∀(y ∈ G, ((op(x)(y) === y) /\ (op(y)(x) === y)))))))

  val identityElement = DEF(λ(G, λ(op, ∃(x, isIdentityElement(G)(op)(x)))))

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
  Subgroup
   */

  val subgroup = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          group(G)(op) /\
            H ⊆ G /\
            group(H)(op)
        )
      )
    )
  )

  /*
  Cosets
   */

  val leftCoset = DEF(
    λ(
      g,
      λ(
        op,
        λ(
            H,
            (op(g)(h) | (h ∈ H))
        )
      )
    )
  )

  val rightCoset = DEF(
    λ(
      H,
      λ(
        op,
        λ(
            g,
            (op(h)(g) | (h ∈ H))
        )
      )
    )
  )


  /*
  Normal
   */

  val normalizer = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          { g ∈ G | leftCoset(g)(op)(H) === rightCoset(H)(op)(g) }
        )
      )
    )
  )

  val normalSubgroup = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          subgroup(H)(G)(op) /\
            (G === normalizer(H)(G)(op))
        )
      )
    )
  )

  /*
  Functions on groups
   */

  /* Lemmas */
  val identityGetsTransferredByCongruence = Theorem(
    (x === y, isIdentityElement(G)(op)(x)) |- isIdentityElement(G)(op)(y)
  ) {
    have(thesis) by Congruence
  }


  val subgroupTestTwoStep = Theorem(
    (group(G)(op), H ≠ ∅, H ⊆ G, binaryOperation(H)(op), inverseElement(H)(op))
    |- subgroup(H)(G)(op)
  ) {
    assume(group(G)(op), H ≠ ∅, H ⊆ G, binaryOperation(H)(op), inverseElement(H)(op))
    val thm1 = have(binaryOperation(H)(op) /\ inverseElement(H)(op)) by Restate
    val subthm1 = have(identityElement(H)(op)) subproof {
      //  val identityElement = ∃(x, isIdentityElement(G)(op)(x)))

      val obs1 = have(∃(h, h ∈ H)) by Tautology.from(EmptySet.nonEmptyHasElement of (x:=H, y:=h))
      val obs2 = have( ∀(x, x ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))) ) ) by Tautology.from(inverseElement.definition of (G:=H, op:=op))
      val obs3 = thenHave( h ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y))) )  by InstantiateForall(h)
      val obs4 = thenHave( h ∈ H |- ∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y))) )  by Restate
      val obs5 = have( h ∈ H |- h ∈ H /\ (∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y))) ))  by Tautology.from(obs4)
      val obs6 = thenHave( h ∈ H |- ∃(x,x∈H /\( ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))) ) ) )  by RightExists
      val obs7 = thenHave( h ∈ H |- ∃(x ∈H, ( ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))) ) ) )  by Restate
      val obs8 = thenHave(∃(h, h ∈ H) |- ∃(x ∈H, ( ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))) ) ) )  by LeftExists
      val obs9 = have(∃(x ∈H, ( ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))) ) ) )  by Tautology.from(obs1, obs8)
      val obs10 = have(∃(x, ( ∃(y, isIdentityElement(H)(op)(op(x)(y))) ) ) )  by Tautology.from(obs9)

      val obs20 = have( isIdentityElement(H)(op)(op(x)(y))  |- isIdentityElement(H)(op)(op(x)(y)) )  by Tautology
      val obs21 = thenHave( isIdentityElement(H)(op)(op(x)(y))  |- ∃(z, isIdentityElement(H)(op)(z) ) )  by RightExists
      val obs22 = thenHave( ∃(y, isIdentityElement(H)(op)(op(x)(y))) |- ∃(z, isIdentityElement(H)(op)(z) ) )  by LeftExists
      val obs23 = thenHave(∃(x, ∃(y, isIdentityElement(H)(op)(op(x)(y))) ) |- ∃(z, isIdentityElement(H)(op)(z) ) )  by LeftExists
      val obs24 = have(∃(z, isIdentityElement(H)(op)(z) ) )  by Tautology.from(obs23, obs10)
      val obs25 = have( identityElement(H)(op) )  by Tautology.from(obs24, identityElement.definition of (G:= H, op:=op))
    }
    val subthm2 = have(associativity(H)(op)) subproof {
      // ∀(x ∈ H, ∀(y ∈ H, ∀(z ∈ H, op(x)(op(y)(z)) === op(op(x)(y))(z))))
      val thm1 = have( associativity(G)(op)  ) by Tautology.from(group.definition)
      val thm2 = have( ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) ) by Tautology.from(associativity.definition, thm1)
      val thm7 = thenHave( ∀(x, x ∈ G ==> ( ∀(y, y ∈ G ==> (∀(z, (z∈G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) ) ) )) by Restate
      // val thm8 = have( ∀(x, ( ∀(y, (∀(z, ( (x∈G) /\ (y∈G) /\ (z∈G) ) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) ) ) )) by Tautology.from(thm7)

      val thm3 = have( op(x)(op(y)(z)) === op(op(x)(y))(z) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Restate
      val thm4 = thenHave( (x ∈ G, y ∈ G, z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Weakening
      val thm5 = have( (x ∈ G, y ∈ G, z ∈ G, y∈G ==> ( op(x)(op(y)(z)) === op(op(x)(y))(z) ) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(thm4)
      val thm6 = thenHave( (x ∈ G, y ∈ G, z ∈ G, ∀(y∈G, ( op(x)(op(y)(z)) === op(op(x)(y))(z) ) ) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by LeftForall
      // val thm5 = thenHave( (x ∈ G, y ∈ G, z ∈ G, ∀(y∈G, op(x)(op(y)(z)) === op(op(x)(y))(z) ) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by LeftForall
      // val thm4 = have( (z ∈ G) /\ (op(x)(op(y)(z)) === op(op(x)(y))(z)) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(thm3)
      // val thm5 = thenHave( ∀(z,(z ∈ G) /\ (op(x)(op(y)(z)) === op(op(x)(y))(z)) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by LeftForall
      // val thm6 = have( ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(thm5)
      // val thm5 = thenHave(∀(y, ∀(z, op(x)(op(y)(z)) === op(op(x)(y))(z) ) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z) ) by LeftForall
      // val thm6 = thenHave(∀(z,∀(y, ∀(z, op(x)(op(y)(z)) === op(op(x)(y))(z) )) ) |- op(x)(op(y)(z)) === op(op(x)(y))(z) ) by LeftForall
      sorry
    }
    val thm2 = have(group(H)(op)) by Tautology.from(group.definition of (G:= H, op:=op), subthm1, subthm2, thm1)
    val thm3 = have(subgroup(H)(G)(op)) by Tautology.from(subgroup.definition of (G:=G, H:=H, op:=op), thm2)
  }

  /*
   * The most simple group:
   * G = {x}, op(x,x) = x
   *
   */
object TrivialGroup extends lisa.Main:
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]

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

  val everyPairIsE = Theorem(
    star(x)(e) === e
  ) {
    have(star(x)(e) === e) by Tautology.from(star.definition of (y := e))
  }

  val eIsIdentity = Theorem(
    () |- Groups.isIdentityElement(G)(star)(e)
  ) {
    val sub1 = have((x ∈ G) |- (star(x)(e) === x) /\ (star(e)(x) === x)) subproof {
      assume(x ∈ G)
      val thm1 = have(star(x)(e) === e) by Tautology.from(star.definition of (y := e))
      val thm2 = have(star(e)(x) === e) by Tautology.from(star.definition of (x := e, y := x))
      val thm3 = have(e === x) by Tautology.from(Singleton.membership of (x := e, y := x))
      val thm4 = have((star(x)(e) === e) /\ (e === x)) by Tautology.from(thm3, thm1)
      val thm5 = have((star(x)(e) === x)) by Tautology.from(thm4, Utils.equalityTransitivity of (Utils.x := star(x)(e), Utils.y := e, Utils.z := x))
      val thm6 = have(star(e)(x) === x) by Tautology.from(thm2, thm3, Utils.equalityTransitivity of (Utils.x := star(e)(x), Utils.y := e, Utils.z := x))
      val thm7 = have((star(e)(x) === x) /\ (star(x)(e) === x)) by Tautology.from(thm5, thm6)
    }
    val thm1 = have((x ∈ G) ==> ((star(x)(e) === x) /\ (star(e)(x) === x))) by Tautology.from(sub1)
    val thm2 = thenHave(∀(x, (x ∈ G) ==> ((star(x)(e) === x) /\ (star(e)(x) === x)))) by RightForall
    val thm3 = have(∀(x ∈ G, ((star(x)(e) === x) /\ (star(e)(x) === x)))) by Tautology.from(thm2)
    val thm4 = have(e ∈ G /\ ∀(x ∈ G, ((star(x)(e) === x) /\ (star(e)(x) === x)))) by Tautology.from(thm2, Singleton.membership of (x := e, y := e))
    val thm5 = have(Groups.isIdentityElement(G)(star)(e)) by Tautology.from(thm4, Groups.isIdentityElement.definition of (Groups.G := G, Groups.op := star, Groups.x := e))
  }

  val trivialGroupHasIdentityElement = Theorem(
    () |- Groups.identityElement(G)(star)
  ) {
    val thm5 = have(Groups.isIdentityElement(G)(star)(e)) by Restate.from(eIsIdentity)
    val thm6 = thenHave(∃(x, Groups.isIdentityElement(G)(star)(x))) by RightExists
    val thm7 = have(Groups.identityElement(G)(star)) by Tautology.from(thm6, Groups.identityElement.definition of (Groups.G := G, Groups.op := star))
  }

  val trivialGroupIsNotEmpty = Theorem(
    () |- ∃(x, x ∈ G)
  ) {
    have(e ∈ G) by Tautology.from(Singleton.membership of (x := e, y := e))
    thenHave(∃(x, x ∈ G)) by RightExists
  }

  val trivialGroupHasInverse = Theorem(
    () |- Groups.inverseElement(G)(star)
  ) {
    // val inverseElement = DEF(λ(G, λ(op, ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))))
    val subthm1 = have(y ∈ G |- Groups.inverseElement(G)(star)) subproof {
      assume(y ∈ G)
      val thm1 = have(e === star(x)(y)) by Tautology.from(star.definition)
      val thm2 = have(isIdentityElement(G)(star)(star(x)(y))) by Tautology.from(
        eIsIdentity,
        Groups.identityGetsTransferredByCongruence of (Groups.G := G, Groups.op := star, Groups.x := e, Groups.y := star(x)(y)),
        thm1
      )
      val thm3 = have(y ∈ G /\ isIdentityElement(G)(star)(star(x)(y))) by Tautology.from(thm2)
      val thm4 = thenHave(∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y)))) by RightExists
      val thm5 = have(x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y)))) by Tautology.from(thm4)
      val thm6 = thenHave(∀(x, x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y))))) by RightForall
      val thm7 = thenHave(∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y))))) by Restate
      val thm8 = have(Groups.inverseElement(G)(star)) by Tautology.from(thm7, Groups.inverseElement.definition of (Groups.G := G, Groups.op := star))
    }

    val thm1 = thenHave((y ∈ G) |- Groups.inverseElement(G)(star)) by Restate
    val thm3 = thenHave(∃(y, y ∈ G) |- Groups.inverseElement(G)(star)) by LeftExists
    val thm4 = thenHave((∃(x, x ∈ G)) |- Groups.inverseElement(G)(star)) by Restate
    val thm6 = have(Groups.inverseElement(G)(star)) by Tautology.from(thm4, trivialGroupIsNotEmpty)
  }

  val trivialGroupIsAssociative = Theorem(
    () |- Groups.associativity(G)(star)
  ) {
    // DEF(λ(G, λ(op, ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))))))
    val thm1 = have(star(x)(star(y)(z)) === e) by Tautology.from(star.definition of (x := x, y := star(y)(z)))
    val thm2 = have(star(star(x)(y))(z) === e) by Tautology.from(star.definition of (x := star(x)(y), y := z))
    val thm3 = have(star(x)(star(y)(z)) === star(star(x)(y))(z)) by Tautology.from(thm1, thm2, Utils.equalityTransitivity of (x := star(x)(star(y)(z)), y := e, z := star(star(x)(y))(z)))

    val thm4 = have(z ∈ G ==> (star(x)(star(y)(z)) === star(star(x)(y))(z))) by Tautology.from(thm3)
    val thm5 = thenHave(∀(z, z ∈ G ==> (star(x)(star(y)(z)) === star(star(x)(y))(z)))) by RightForall
    val thm6 = have(∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))) by Restate.from(thm5)

    val thm7 = have(y ∈ G ==> ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))) by Tautology.from(thm6)
    val thm8 = thenHave(∀(y, y ∈ G ==> ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by RightForall
    val thm9 = have(∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by Restate.from(thm8)

    val thm10 = have(x ∈ G ==> ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by Tautology.from(thm9)
    val thm11 = thenHave(∀(x, x ∈ G ==> ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))))) by RightForall
    val thm12 = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))))) by Restate.from(thm11)

    val thm13 = have(Groups.associativity(G)(star)) by Tautology.from(thm12, Groups.associativity.definition of (Groups.G := G, Groups.op := star))
  }

  val trivialGroupIsGroup = Theorem(
    () |- Groups.group(G)(star)
  ) {
    have(Groups.group(G)(star)) by Tautology.from(
      trivialGroupHasBinaryOperation,
      trivialGroupIsAssociative,
      trivialGroupHasInverse,
      trivialGroupHasIdentityElement,
      Groups.group.definition of (Groups.G := G, Groups.op := star)
    )
  }
