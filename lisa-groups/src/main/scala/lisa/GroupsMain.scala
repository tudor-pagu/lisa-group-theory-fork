package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}

import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.Base.Symbols._
import lisa.maths.Quantifiers
import lisa.automation.Substitution
import lisa.maths.SetTheory.Functions.Function.bijective
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
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
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

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
  val a = variable[Ind]
  val b = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val h = variable[Ind]

  val g = variable[Ind]
  val e = variable[Ind]

  val f = variable[Ind]

  private val P, Q = variable[Ind >>: Prop]

  val G = variable[Ind]
  val Pr = variable[Ind]
  val H = variable[Ind]
  val C = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]

  val binaryOperation = DEF(λ(G, λ(op, ∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)))))

  val isIdentityElement = DEF(λ(G, λ(op, λ(x, (x ∈ G) /\ (∀(y ∈ G, ((op(x)(y) === y) /\ (op(y)(x) === y))))))))

  val identityElement = DEF(λ(G, λ(op, ∃(x, isIdentityElement(G)(op)(x)))))

  val associativity = DEF(λ(G, λ(op, ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))))))

  val inverseElement = DEF(λ(G, λ(op, ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))))

  val inverseOf = DEF(λ(G, λ(op, λ(x, ε(y, (y ∈ G) /\ (isIdentityElement(G)(op)(op(x)(y))))))))

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

  val inverseStaysInGroup = Theorem(
    (group(G)(op), x ∈ G) |- inverseOf(G)(op)(x) ∈ G
  ) {
    sorry
  }

  val associativityAlternateForm = Theorem(
    ∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))))
      |- associativity(G)(op)
  ) {
    assume(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))))))

    val thm1 = have(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by Restate
    val thm2 = have(∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by InstantiateForall(y)(thm2)
    val thm4 = have(((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(z)(thm3)
    val thm5 = thenHave(((x ∈ G), (y ∈ G), (z ∈ G)) |- (op(x)(op(y)(z)) === op(op(x)(y))(z))) by Restate

    // Build up z quantifier first
    val thm6 = thenHave(((x ∈ G), (y ∈ G)) |- (z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by Restate
    val thm7 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z, (z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by RightForall
    val thm8 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Restate

    // Build up y quantifier
    val thm9 = thenHave((x ∈ G) |- (y ∈ G) ==> ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Restate
    val thm10 = thenHave((x ∈ G) |- ∀(y, (y ∈ G) ==> ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by RightForall
    val thm11 = thenHave((x ∈ G) |- ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Restate

    // Build up x quantifier
    val thm12 = thenHave(() |- (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Restate
    val thm13 = thenHave(() |- ∀(x, (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by RightForall
    val thm14 = thenHave(() |- ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by Restate

    have(associativity(G)(op)) by Tautology.from(thm14, associativity.definition)
  }

  val associativityThm = Theorem(
    (associativity(G)(op), x ∈ G, y ∈ G, z ∈ G) |-
      op(x)(op(y)(z)) === op(op(x)(y))(z)
  ) {
    assume(associativity(G)(op), x ∈ G, y ∈ G, z ∈ G)

    // Unfold the definition of associativity
    val thm1 = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Tautology.from(associativity.definition)

    // Instantiate x
    val thm2 = have((x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Tautology.from(thm2)

    // Instantiate y
    val thm4 = have((y ∈ G) ==> ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(y)(thm3)
    val thm5 = have(∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))) by Tautology.from(thm4)

    // Instantiate z
    val thm6 = have((z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(z)(thm5)
    val thm7 = have(op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(thm6)
  }

  val binaryOperationThm = Theorem(
    (binaryOperation(G)(op), x ∈ G, y ∈ G) |-
      op(x)(y) ∈ G
  ) {
    sorry
  }

  val subgroupTestTwoStep = Theorem(
    (group(G)(op), H ≠ ∅, H ⊆ G, binaryOperation(H)(op), inverseElement(H)(op))
      |- subgroup(H)(G)(op)
  ) {
    assume(group(G)(op), H ≠ ∅, H ⊆ G, binaryOperation(H)(op), inverseElement(H)(op))
    val thm1 = have(binaryOperation(H)(op) /\ inverseElement(H)(op)) by Restate
    val subthm1 = have(identityElement(H)(op)) subproof {
      //  val identityElement = ∃(x, isIdentityElement(G)(op)(x)))

      val obs1 = have(∃(h, h ∈ H)) by Tautology.from(EmptySet.nonEmptyHasElement of (x := H, y := h))
      val obs2 = have(∀(x, x ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y))))) by Tautology.from(inverseElement.definition of (G := H, op := op))
      val obs3 = thenHave(h ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y)))) by InstantiateForall(h)
      val obs4 = thenHave(h ∈ H |- ∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y)))) by Restate
      val obs5 = have(h ∈ H |- h ∈ H /\ (∃(y ∈ H, isIdentityElement(H)(op)(op(h)(y))))) by Tautology.from(obs4)
      val obs6 = thenHave(h ∈ H |- ∃(x, x ∈ H /\ (∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y)))))) by RightExists
      val obs7 = thenHave(h ∈ H |- ∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y)))))) by Restate
      val obs8 = thenHave(∃(h, h ∈ H) |- ∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y)))))) by LeftExists
      val obs9 = have(∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(op)(op(x)(y)))))) by Tautology.from(obs1, obs8)
      val obs10 = have(∃(x, (∃(y, isIdentityElement(H)(op)(op(x)(y)))))) by Tautology.from(obs9)

      val obs20 = have(isIdentityElement(H)(op)(op(x)(y)) |- isIdentityElement(H)(op)(op(x)(y))) by Tautology
      val obs21 = thenHave(isIdentityElement(H)(op)(op(x)(y)) |- ∃(z, isIdentityElement(H)(op)(z))) by RightExists
      val obs22 = thenHave(∃(y, isIdentityElement(H)(op)(op(x)(y))) |- ∃(z, isIdentityElement(H)(op)(z))) by LeftExists
      val obs23 = thenHave(∃(x, ∃(y, isIdentityElement(H)(op)(op(x)(y)))) |- ∃(z, isIdentityElement(H)(op)(z))) by LeftExists
      val obs24 = have(∃(z, isIdentityElement(H)(op)(z))) by Tautology.from(obs23, obs10)
      val obs25 = have(identityElement(H)(op)) by Tautology.from(obs24, identityElement.definition of (G := H, op := op))
    }

    val subthm2 = have((x ∈ H, y ∈ H, z ∈ H) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) subproof {
      assume(x ∈ H, y ∈ H, z ∈ H)
      val obs1 = have(H ⊆ G) by Restate
      val obs2 = have(x ∈ G) by Tautology.from(Subset.membership of (z := x, x := H, y := G), obs1)
      val obs3 = have(y ∈ G) by Tautology.from(Subset.membership of (z := y, x := H, y := G), obs1)
      val obs4 = have(z ∈ G) by Tautology.from(Subset.membership of (z := z, x := H, y := G), obs1)

      val obs5 = have(associativity(G)(op)) by Tautology.from(group.definition)
      val obs7 = have(op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(associativityThm, obs2, obs3, obs4, obs5)
    }

    val subthm3 = have(associativity(H)(op)) subproof {
      have((x ∈ H, y ∈ H, z ∈ H) |- op(x)(op(y)(z)) === op(op(x)(y))(z)) by Restate.from(subthm2)
      val obs1 = thenHave(((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by Restate
      thenHave(∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by RightForall
      thenHave(∀(y, ∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by RightForall
      val obs2 = thenHave(∀(x, ∀(y, ∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by RightForall
      have(associativity(H)(op)) by Tautology.from(obs2, associativityAlternateForm of (G := H, op := op))
    }
    val thm2 = have(group(H)(op)) by Tautology.from(group.definition of (G := H, op := op), subthm1, subthm3, thm1)
    val thm3 = have(subgroup(H)(G)(op)) by Tautology.from(subgroup.definition of (G := G, H := H, op := op), thm2)
  }

  /* Lagrange's Theorem */

  // P is a partition of G
  val partition = DEF(
    λ(
      G,
      λ(
        Pr,
        (∀(x ∈ Pr, x ⊆ G)) /\ // every set in P is a subset of G
          (∀(x ∈ G, ∃(y ∈ Pr, x ∈ y))) /\ // every element of G is found in some set in P
          (∀(x ∈ Pr, ∀(y ∈ Pr, x ≠ y ==> (x ∩ y === ∅)))) // the sets in P are disjoint
      )
    )
  )

  val rightCosetStaysInGroupLemma = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ G) |-
      (rightCoset(H)(op)(x) ⊆ G)
  ) {
    sorry
  }

  val elementInSubgroupMeansItsInGroup = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ H) |- x ∈ G
  ) {
    sorry
  }

  val subgroupHasTheSameIdentity = Theorem(
    (group(G)(op), subgroup(H)(G)(op), isIdentityElement(G)(op)(e)) |- isIdentityElement(H)(op)(e)
  ) {
    sorry
  }

  val groupHasTheSameIdentityAsSubgroup = Theorem(
    (group(G)(op), subgroup(H)(G)(op), isIdentityElement(H)(op)(e)) |- isIdentityElement(G)(op)(e)
  ) {
    sorry
  }

  val cosetEqualityTheorem = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))
      |- rightCoset(H)(op)(a) === rightCoset(H)(op)(b)
  ) {
    sorry
  }

  // we can multiply to both sides of an equality
  val congruence = Theorem(
    (group(G)(op), x === y) |-
      op(z)(x) === op(z)(y)
  ) {
    sorry
  }

  val congruenceRight = Theorem(
    (group(G)(op), x === y) |-
      op(x)(z) === op(y)(z)
  ) {
    sorry
  }

  val inverseProperty2 = Theorem(
    (group(G)(op), x ∈ G) |- isIdentityElement(G)(op)(op(x)(inverseOf(G)(op)(x)))
  ) {
    assume(group(G)(op), x ∈ G)
    val auxP = lambda(y, (y ∈ G) /\ (isIdentityElement(G)(op)(op(x)(y))))
    val eps = have(∃(y, auxP(y)) |- auxP(ε(y, auxP(y)))) by Tautology.from(Quantifiers.existsEpsilon of (P := auxP))

    val ex = have(
      inverseElement(G)(op) |-
        ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))
    ) by Tautology.from(
      inverseElement.definition
    )

    val ex2 = thenHave(
      inverseElement(G)(op) |-
        ∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))
    ) by Restate

    val ex3 = have(∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))) by Tautology.from(ex2, group.definition)
    val ex4 = thenHave(x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))) by InstantiateForall(x)
    val ex5 = have(∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by Tautology.from(ex4)
    val ex6 = have(∃(y ∈ G, auxP(y))) by Tautology.from(ex5)
    val ex7 = thenHave(∃(y, (y ∈ G) /\ auxP(y))) by Restate
    // val ex8 = have(∃(y, auxP(y)) ) by Tautology.from(ex7)
    val ex9 = have(auxP(ε(y, auxP(y)))) by Tautology.from(ex7, eps)

    val inv = inverseOf(G)(op)(x)
    val i1 = have(inv === ε(y, auxP(y))) by Tautology.from(inverseOf.definition)
    val eq1 = inv === ε(y, auxP(y))
    val i2 = have(eq1 |- auxP(inv)) by Substitution.Apply(eq1)(ex9)
    val i3 = have(auxP(inv)) by Tautology.from(i2, i1)
    val i4 = have((inv ∈ G) /\ (isIdentityElement(G)(op)(op(x)(inv)))) by Tautology.from(i3)
    val i5 = have((isIdentityElement(G)(op)(op(x)(inv)))) by Tautology.from(i4)
  }

  val inverseCommutability = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, isIdentityElement(G)(op)(op(x)(y)))
      |- isIdentityElement(G)(op)(op(y)(x))
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, isIdentityElement(G)(op)(op(x)(y)))
    val yInv = inverseOf(G)(op)(y)
    val e = op(x)(y)

    val step0 = have(op(x)(y) === e) by Restate
    val obs1 = have(yInv ∈ G) by Tautology.from(inverseStaysInGroup of (G := G, op := op, x := y))
    val assocG = have(associativity(G)(op)) by Tautology.from(group.definition)

    // Multiply both sides by y^(-1) on the right: (x * y) * y^(-1) === e * y^(-1)
    val step1 = have(op(op(x)(y))(yInv) === op(e)(yInv)) by Tautology.from(
      congruenceRight of (G := G, op := op, x := op(x)(y), y := e, z := yInv),
      step0
    )

    // e is an identity element, so e * y^(-1) === y^(-1)
    val step2a = have(isIdentityElement(G)(op)(e) |- ∀(z ∈ G, (op(e)(z) === z) /\ (op(z)(e) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := e)
    )

    val step2b = thenHave(isIdentityElement(G)(op)(e) |- (yInv ∈ G) ==> ((op(e)(yInv) === yInv) /\ (op(yInv)(e) === yInv))) by InstantiateForall(yInv)
    val step2 = have(op(e)(yInv) === yInv) by Tautology.from(step2b, obs1)

    val step3 = have(op(op(x)(y))(yInv) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(op(x)(y))(yInv), y := op(e)(yInv), z := yInv),
      step1,
      step2
    )

    // Use associativity: (x * y) * y^(-1) === x * (y * y^(-1))
    val step4 = have(op(op(x)(y))(yInv) === op(x)(op(y)(yInv))) by Tautology.from(
      associativityThm of (x := x, y := y, z := yInv),
      assocG,
      obs1
    )

    val step5 = have(op(x)(op(y)(yInv)) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(x)(op(y)(yInv)), y := op(op(x)(y))(yInv), z := yInv),
      step4,
      step3
    )

    // y * y^(-1) is an identity element (using inverseProperty2)
    val step6 = have(isIdentityElement(G)(op)(op(y)(yInv))) by Tautology.from(
      inverseProperty2 of (G := G, op := op, x := y)
    )

    val step7a = have(isIdentityElement(G)(op)(op(y)(yInv)) |- ∀(z ∈ G, (op(op(y)(yInv))(z) === z) /\ (op(z)(op(y)(yInv)) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := op(y)(yInv))
    )
    val step7b = thenHave(isIdentityElement(G)(op)(op(y)(yInv)) |- (x ∈ G) ==> ((op(op(y)(yInv))(x) === x) /\ (op(x)(op(y)(yInv)) === x))) by InstantiateForall(x)
    val step7 = have(op(x)(op(y)(yInv)) === x) by Tautology.from(step7b, step6)

    // Therefore x === y^(-1)
    val step8 = have(x === yInv) by Tautology.from(
      equalityTransitivity of (x := x, y := op(x)(op(y)(yInv)), z := yInv),
      step7,
      step5
    )

    // Multiply both sides by y on the left: y * x === y * y^(-1)
    val step9 = have(op(y)(x) === op(y)(yInv)) by Tautology.from(
      congruence of (G := G, op := op, x := x, y := yInv, z := y),
      step8
    )

    // y * y^(-1) is an identity element (using inverseProperty2 again)
    val step10 = have(isIdentityElement(G)(op)(op(y)(yInv))) by Tautology.from(
      inverseProperty2 of (G := G, op := op, x := y)
    )

    // Therefore y * x is an identity element
    val step11Eq = op(y)(x) === op(y)(yInv)
    val step11 = have(step11Eq |- isIdentityElement(G)(op)(op(y)(x))) by Substitution.Apply(step11Eq)(step10)
    have(isIdentityElement(G)(op)(op(y)(x))) by Tautology.from(step11, step9)
  }

  val inverseProperty = Theorem(
    (group(G)(op), x ∈ G) |- isIdentityElement(G)(op)(op(inverseOf(G)(op)(x))(x))
  ) {
    sorry
  }

  val lagrangesLemma1 = Theorem(
    (group(G)(op), subgroup(H)(G)(op))
      |- partition(G)((rightCoset(H)(op)(x) | x ∈ G))
  ) {
    assume(group(G)(op), subgroup(H)(G)(op))

    val subthm1 = have(y ∈ (rightCoset(H)(op)(x) | x ∈ G) |- y ⊆ G) subproof {
      assume(y ∈ (rightCoset(H)(op)(x) | x ∈ G))
      val obs1 = have(∃(x ∈ G, rightCoset(H)(op)(x) === y)) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(op)(x)), A := G, y := y)
      )
      val obs2 = have((x ∈ G, rightCoset(H)(op)(x) === y) |- rightCoset(H)(op)(x) ⊆ G) by Tautology.from(
        rightCosetStaysInGroupLemma
      )
      val obs3 = have((x ∈ G, rightCoset(H)(op)(x) === y) |- y ⊆ G) by Substitution.Apply(rightCoset(H)(op)(x) === y)(obs2)
      val obs4 = thenHave(((x ∈ G) /\ (rightCoset(H)(op)(x) === y)) |- y ⊆ G) by Restate
      val obs5 = thenHave(∃(x, (x ∈ G) /\ (rightCoset(H)(op)(x) === y)) |- y ⊆ G) by LeftExists
      val obs6 = thenHave(∃(x ∈ G, rightCoset(H)(op)(x) === y) |- y ⊆ G) by Restate
      have(y ⊆ G) by Tautology.from(obs1, obs6)
    }

    val thm1 = have(y ∈ (rightCoset(H)(op)(x) | x ∈ G) ==> y ⊆ G) by Restate.from(subthm1)
    val thm2 = thenHave(∀(y, y ∈ (rightCoset(H)(op)(x) | x ∈ G) ==> y ⊆ G)) by RightForall
    val thm3 = thenHave(∀(y ∈ (rightCoset(H)(op)(x) | x ∈ G), y ⊆ G)) by Restate

    val subthm2 = have(y ∈ G |- ∃(z ∈ (rightCoset(H)(op)(x) | x ∈ G), y ∈ z)) subproof {
      // Prove every element of G is in some right coset
      assume(y ∈ G)
      val obs1 = have(identityElement(G)(op)) by Tautology.from(group.definition)
      val obs2 = have(∃(e, isIdentityElement(G)(op)(e))) by Tautology.from(obs1, identityElement.definition)

      val obs3 = have(isIdentityElement(G)(op)(e) |- ∀(y ∈ G, ((op(e)(y) === y) /\ (op(y)(e) === y)))) by Tautology.from(isIdentityElement.definition of (G := G, op := op, x := e))
      val obs4 = thenHave(isIdentityElement(G)(op)(e) |- (y ∈ G) ==> ((op(e)(y) === y) /\ (op(y)(e) === y))) by InstantiateForall(y)
      val obs5 = have(isIdentityElement(G)(op)(e) |- (op(e)(y) === y)) by Tautology.from(obs4)

      val cosetSet = (rightCoset(H)(op)(x) | x ∈ G)

      // KEY OBSERVATION
      val obs6 = have(rightCoset(H)(op)(y) ∈ cosetSet) by Tautology.from(Replacement.map of (F := lambda(x, rightCoset(H)(op)(x)), A := G, x := y))

      val obs7 = have(isIdentityElement(G)(op)(e) |- isIdentityElement(H)(op)(e)) by Tautology.from(
        subgroupHasTheSameIdentity
      )
      val obs8 = have(isIdentityElement(G)(op)(e) |- e ∈ H) by Tautology.from(
        obs7,
        isIdentityElement.definition of (G := H, op := op, x := e)
      )

      val obs9 = have(isIdentityElement(G)(op)(e) |- e ∈ H /\ (op(e)(y) === op(e)(y))) by Tautology.from(obs8)
      val obs10 = have(isIdentityElement(G)(op)(e) |- e ∈ H /\ (op(e)(y) === op(e)(y))) by Tautology.from(obs8)
      val obs11 = thenHave(isIdentityElement(G)(op)(e) |- ∃(h, h ∈ H /\ (op(h)(y) === op(e)(y)))) by RightExists
      val obs12 = thenHave(isIdentityElement(G)(op)(e) |- ∃(h ∈ H, op(h)(y) === op(e)(y))) by Restate
      val obs13 = have(isIdentityElement(G)(op)(e) |- op(e)(y) ∈ (op(h)(y) | h ∈ H)) by Tautology.from(
        obs12,
        Replacement.membership of (F := λ(h, op(h)(y)), A := H, y := op(e)(y))
      )
      val obs14 = have((op(h)(y) | h ∈ H) === rightCoset(H)(op)(y)) by Tautology.from(
        rightCoset.definition of (H := H, op := op, g := y)
      )
      val obs15 = have(((op(h)(y) | h ∈ H) === rightCoset(H)(op)(y), isIdentityElement(G)(op)(e)) |- op(e)(y) ∈ rightCoset(H)(op)(y)) by Substitution.Apply(
        (op(h)(y) | h ∈ H) === rightCoset(H)(op)(y)
      )(obs13)

      // KEY OBSERVATION
      val obs16 = have(isIdentityElement(G)(op)(e) |- op(e)(y) ∈ rightCoset(H)(op)(y)) by Tautology.from(obs14, obs15)

      val obs17 = have((y === op(e)(y), isIdentityElement(G)(op)(e)) |- y ∈ rightCoset(H)(op)(y)) by Substitution.Apply(y === op(e)(y))(obs16)
      val obs18 = have(isIdentityElement(G)(op)(e) |- y ∈ rightCoset(H)(op)(y)) by Tautology.from(obs17, obs5)
      val obs19 = have(isIdentityElement(G)(op)(e) |- y ∈ rightCoset(H)(op)(y) /\ rightCoset(H)(op)(y) ∈ cosetSet) by Tautology.from(obs18, obs6)
      val obs20 = thenHave(isIdentityElement(G)(op)(e) |- ∃(z, y ∈ z /\ z ∈ cosetSet)) by RightExists
      val obs21 = thenHave(isIdentityElement(G)(op)(e) |- ∃(z ∈ cosetSet, y ∈ z)) by Restate
      val obs22 = thenHave(∃(e, isIdentityElement(G)(op)(e)) |- ∃(z ∈ cosetSet, y ∈ z)) by LeftExists

      val obs23 = have(∃(e, isIdentityElement(G)(op)(e))) by Tautology.from(
        group.definition,
        identityElement.definition
      )

      val obs24 = have(∃(z ∈ cosetSet, y ∈ z)) by Tautology.from(obs22, obs23)
    }

    val thm4 = have(y ∈ G ==> ∃(z ∈ (rightCoset(H)(op)(x) | x ∈ G), y ∈ z)) by Restate.from(subthm2)
    val thm5 = thenHave(∀(y, y ∈ G ==> ∃(z ∈ (rightCoset(H)(op)(x) | x ∈ G), y ∈ z))) by RightForall
    val thm6 = thenHave(∀(y ∈ G, ∃(z ∈ (rightCoset(H)(op)(x) | x ∈ G), y ∈ z))) by Restate

    val rcSet = (rightCoset(H)(op)(x) | x ∈ G)

    val subthm3 = have((y ∈ rcSet, z ∈ rcSet, (y ∩ z) ≠ ∅) |- y === z) subproof {
      assume(y ∈ rcSet, z ∈ rcSet, (y ∩ z) ≠ ∅)
      val obs1 = have(∃(x, x ∈ (y ∩ z))) by Tautology.from(EmptySet.nonEmptyHasElement of (x := (y ∩ z), y := x))

      val x0 = ε(x, x ∈ (y ∩ z))
      val xThm = have(x0 ∈ (y ∩ z)) by Tautology.from(obs1, Quantifiers.existsEpsilon of (x := x, P := lambda(x, x ∈ (y ∩ z))))

      val obs2 = have(x0 ∈ y) by Tautology.from(
        Intersection.membership of (z := x0, x := y, y := z),
        xThm
      )

      val obs3 = have(x0 ∈ z) by Tautology.from(
        Intersection.membership of (z := x0, x := y, y := z),
        xThm
      )

      val interlude1a = have(∃(a ∈ G, y === rightCoset(H)(op)(a))) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(op)(x)), A := G, y := y)
      )

      val a0 = ε(a, (a ∈ G) /\ (y === rightCoset(H)(op)(a)))
      val aThm = have((a0 ∈ G) /\ (y === rightCoset(H)(op)(a0))) by Tautology.from(
        interlude1a,
        Quantifiers.existsEpsilon of (x := a, P := lambda(a, (a ∈ G) /\ (y === rightCoset(H)(op)(a))))
      )

      val interlude1b = have(∃(b ∈ G, z === rightCoset(H)(op)(b))) by Tautology.from(
        Replacement.membership of (F := lambda(y, rightCoset(H)(op)(y)), A := G, y := z)
      )

      val b0 = ε(b, (b ∈ G) /\ (z === rightCoset(H)(op)(b)))
      val bThm = have((b0 ∈ G) /\ (z === rightCoset(H)(op)(b0))) by Tautology.from(
        interlude1b,
        Quantifiers.existsEpsilon of (x := b, P := lambda(b, (b ∈ G) /\ (z === rightCoset(H)(op)(b))))
      )

      val auxEq1 = (y === rightCoset(H)(op)(a0))
      val obs5 = have(auxEq1 |- x0 ∈ rightCoset(H)(op)(a0)) by Substitution.Apply(auxEq1)(obs2)
      val obs6 = have(auxEq1) by Tautology.from(aThm)
      val obs7 = have(x0 ∈ rightCoset(H)(op)(a0)) by Tautology.from(obs5, obs6)

      val auxEq2 = (z === rightCoset(H)(op)(b0))
      val obs8 = have(auxEq2 |- x0 ∈ rightCoset(H)(op)(b0)) by Substitution.Apply(auxEq2)(obs3)
      val obs9 = have(auxEq2) by Tautology.from(bThm)
      val obs10 = have(x0 ∈ rightCoset(H)(op)(b0)) by Tautology.from(obs8, obs9)

      val auxEq3 = rightCoset(H)(op)(a0) === (op(h)(a0) | h ∈ H)
      val obs7a = have(auxEq3 |- x0 ∈ (op(h)(a0) | h ∈ H)) by Substitution.Apply(auxEq3)(obs7)
      val obs7b = have(auxEq3) by Tautology.from(rightCoset.definition of (H := H, op := op, g := a0))
      val obs7Unfold = have(x0 ∈ (op(h)(a0) | h ∈ H)) by Tautology.from(obs7a, obs7b)
      val h1Ex = have(∃(h ∈ H, op(h)(a0) === x0)) by Tautology.from(
        obs7Unfold,
        Replacement.membership of (F := lambda(h, op(h)(a0)), A := H, y := x0)
      )
      val h1 = ε(h, (h ∈ H) /\ (op(h)(a0) === x0))
      val h1Thm = have((h1 ∈ H) /\ (op(h1)(a0) === x0)) by Tautology.from(
        h1Ex,
        Quantifiers.existsEpsilon of (x := h1, P := lambda(h, (h ∈ H) /\ (op(h)(a0) === x0)))
      )

      val auxEq4 = rightCoset(H)(op)(b0) === (op(h)(b0) | h ∈ H)
      val obs10a = have(auxEq4 |- x0 ∈ (op(h)(b0) | h ∈ H)) by Substitution.Apply(auxEq4)(obs10)
      val obs10b = have(auxEq4) by Tautology.from(rightCoset.definition of (H := H, op := op, g := b0))
      val obs10Unfold = have(x0 ∈ (op(h)(b0) | h ∈ H)) by Tautology.from(obs10a, obs10b)
      val h2Ex = have(∃(h ∈ H, op(h)(b0) === x0)) by Tautology.from(
        obs10Unfold,
        Replacement.membership of (F := lambda(h, op(h)(b0)), A := H, y := x0)
      )
      val h2 = ε(h, (h ∈ H) /\ (op(h)(b0) === x0))
      val h2Thm = have((h2 ∈ H) /\ (op(h2)(b0) === x0)) by Tautology.from(
        h2Ex,
        Quantifiers.existsEpsilon of (x := h, P := lambda(h, (h ∈ H) /\ (op(h)(b0) === x0)))
      )

      val obs11 = have(op(h1)(a0) === op(h2)(b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := op(h1)(a0), y := x0, z := op(h2)(b0)),
        h1Thm,
        h2Thm
      )

      val h1Inv = inverseOf(H)(op)(h1)

      val hGroup = have(group(H)(op)) by Tautology.from(subgroup.definition)
      val obs12 = have(op(h1Inv)(op(h1)(a0)) === op(h1Inv)(op(h2)(b0))) by Tautology.from(obs11, congruence of (G := H, op := op, x := op(h1)(a0), y := op(h2)(b0), z := h1Inv), hGroup)

      val obs13 = have(h1Inv ∈ H) by Tautology.from(
        inverseStaysInGroup of (G := H, op := op, x := h1),
        hGroup,
        h1Thm
      )
      val obs14 = have(h1Inv ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, op := op, x := h1Inv),
        obs13
      )
      val obs15 = have(h1 ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, op := op, x := h1),
        h1Thm
      )

      val assocG = have(associativity(G)(op)) by Tautology.from(group.definition)
      val obs16 = have(op(h1Inv)(op(h1)(a0)) === op(op(h1Inv)(h1))(a0)) by Tautology.from(
        associativityThm of (x := h1Inv, y := h1, z := a0),
        assocG,
        obs14,
        obs15,
        aThm
      )

      val aux = op(h1Inv)(h1)
      val invProp = have(isIdentityElement(H)(op)(aux)) by Tautology.from(
        inverseProperty of (G := H, op := op, x := h1),
        hGroup,
        h1Thm
      )

      val invProp2 = have(isIdentityElement(G)(op)(aux)) by Tautology.from(
        invProp,
        groupHasTheSameIdentityAsSubgroup of (e := aux)
      )

      val invH1 = have(isIdentityElement(G)(op)(x) |- (∀(y ∈ G, ((op(x)(y) === y) /\ (op(y)(x) === y))))) by Tautology.from(isIdentityElement.definition of (G := G))
      val invH2 = thenHave(isIdentityElement(G)(op)(x) |- ∀(y, (y ∈ G) ==> (((op(x)(y) === y) /\ (op(y)(x) === y))))) by Restate
      val invH3 = thenHave(isIdentityElement(G)(op)(x) |- (a0 ∈ G) ==> (((op(x)(a0) === a0) /\ (op(a0)(x) === a0)))) by InstantiateForall(a0)
      val invH4 = have(isIdentityElement(G)(op)(x) |- (((op(x)(a0) === a0) /\ (op(a0)(x) === a0)))) by Tautology.from(invH3, aThm)
      val invH5 = have(isIdentityElement(G)(op)(x) |- op(x)(a0) === a0) by Tautology.from(invH4)
      val invH6 = have(isIdentityElement(G)(op)(x) ==> (op(x)(a0) === a0)) by Tautology.from(invH5)
      val invH7 = thenHave(∀(x, isIdentityElement(G)(op)(x) ==> (op(x)(a0) === a0))) by RightForall
      val invH8 = thenHave(isIdentityElement(G)(op)(aux) ==> (op(aux)(a0) === a0)) by InstantiateForall(aux)
      val invH9 = have(op(aux)(a0) === a0) by Tautology.from(invH8, invProp2)

      val obs17 = have(op(h1Inv)(op(h1)(a0)) === a0) by Tautology.from(
        Utils.equalityTransitivity of (x := op(h1Inv)(op(h1)(a0)), y := op(op(h1Inv)(h1))(a0), z := a0),
        obs16,
        invH9
      )

      val obs17Sym = have(a0 === op(h1Inv)(op(h1)(a0))) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(op(h1Inv)(h1))(a0), z := op(h1Inv)(op(h1)(a0))),
        invH9,
        obs16
      )
      val obs18 = have(a0 === op(h1Inv)(op(h2)(b0))) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(h1Inv)(op(h1)(a0)), z := op(h1Inv)(op(h2)(b0))),
        obs17Sym,
        obs12
      )

      val obs19 = have(h2 ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, op := op, x := h2),
        h2Thm
      )
      val obs20 = have(b0 ∈ G) by Tautology.from(bThm)

      val obs21 = have(op(h1Inv)(op(h2)(b0)) === op(op(h1Inv)(h2))(b0)) by Tautology.from(
        associativityThm of (x := h1Inv, y := h2, z := b0),
        assocG,
        obs14,
        obs19,
        obs20
      )

      val obs22 = have(a0 === op(op(h1Inv)(h2))(b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(h1Inv)(op(h2)(b0)), z := op(op(h1Inv)(h2))(b0)),
        obs18,
        obs21
      )

      val obs23 = have(op(h1Inv)(h2) ∈ H) by Tautology.from(
        binaryOperationThm of (G := H, op := op, x := h1Inv, y := h2),
        hGroup,
        group.definition of (G := H, op := op),
        obs13,
        h2Thm
      )

      val obs24Eq = (op(h)(b0) | (h ∈ H)) === rightCoset(H)(op)(b0)
      val obs24a1 = have((op(h)(g) | (h ∈ H)) === rightCoset(H)(op)(g)) by Tautology.from(rightCoset.definition)
      val obs24a2 = thenHave(∀(g, (op(h)(g) | (h ∈ H)) === rightCoset(H)(op)(g))) by RightForall
      val obs24a3 = thenHave((op(h)(b0) | (h ∈ H)) === rightCoset(H)(op)(b0)) by InstantiateForall(b0)
      val obs24a = thenHave(obs24Eq) by Restate

      val obs24b1 = have((∃(h ∈ H, op(h)(b0) === a0)) ==> (a0 ∈ { op(h)(b0) | h ∈ H })) by Tautology.from(Replacement.membership of (A := H, y := a0, F := lambda(h, op(h)(b0))))
      val obs24b2 = have((op(h1Inv)(h2) ∈ H) /\ (a0 === op(op(h1Inv)(h2))(b0))) by Tautology.from(obs23, obs22)
      val obs24b3 = thenHave(∃(h, (h ∈ H) /\ (a0 === op(h)(b0)))) by RightExists
      val obs24b4 = have(∃(h, (h ∈ H) /\ (op(h)(b0) === a0))) by Tautology.from(obs24b3)
      val obs24b = have(a0 ∈ (op(h)(b0) | (h ∈ H))) by Tautology.from(obs24b1, obs24b4)

      val obs25c = have(obs24Eq |- a0 ∈ rightCoset(H)(op)(b0)) by Substitution.Apply(obs24Eq)(obs24b)
      val obs25 = have(a0 ∈ rightCoset(H)(op)(b0)) by Tautology.from(obs25c, obs24a)
      val obs26 = have(rightCoset(H)(op)(a0) === rightCoset(H)(op)(b0)) by Tautology.from(cosetEqualityTheorem of (a := a0, b := b0), aThm, bThm, obs25)
      val obs27a = have(y === rightCoset(H)(op)(b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := y, y := rightCoset(H)(op)(a0), z := rightCoset(H)(op)(b0)),
        aThm,
        obs26
      )
      val obs27 = have(y === z) by Tautology.from(
        Utils.equalityTransitivity of (x := y, y := rightCoset(H)(op)(b0), z := z),
        obs27a,
        bThm
      )
    }

    val subthm4 = have((y ∈ rcSet, z ∈ rcSet, y ≠ z) |- y ∩ z === ∅) by Tautology.from(subthm3)

    val thm7 = thenHave((y ∈ rcSet) |- (z ∈ rcSet) ==> ((y ≠ z) ==> ((y ∩ z) === ∅))) by Restate
    val thm8 = thenHave((y ∈ rcSet) |- ∀(z, (z ∈ rcSet) ==> ((y ≠ z) ==> ((y ∩ z) === ∅)))) by RightForall
    val thm9 = thenHave((y ∈ rcSet) ==> (∀(z, (z ∈ rcSet) ==> ((y ≠ z) ==> ((y ∩ z) === ∅))))) by Restate
    val thm10 = thenHave(∀(y, (y ∈ rcSet) ==> (∀(z, (z ∈ rcSet) ==> ((y ≠ z) ==> ((y ∩ z) === ∅)))))) by RightForall
    val thm11 = thenHave(∀(y ∈ rcSet, (∀(z, (z ∈ rcSet) ==> ((y ≠ z) ==> ((y ∩ z) === ∅)))))) by Restate

    have(partition(G)((rightCoset(H)(op)(x) | x ∈ G))) by Tautology.from(
      thm3,
      thm6,
      thm11,
      partition.definition of (G := G, Pr := (rightCoset(H)(op)(x) | x ∈ G))
    )
  }

  val lagrangesLemma2 = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ G) |-
      ∃(f, bijective(f)(H)(rightCoset(H)(op)(x)))
  ) {
    sorry
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
