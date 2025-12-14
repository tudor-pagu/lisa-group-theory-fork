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

object Groups extends lisa.Main:
  val a = variable[Ind]
  val b = variable[Ind]
  val c = variable[Ind]
  val d = variable[Ind]

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
  val identityOf = DEF(λ(G, λ(op, ε(e, isIdentityElement(G)(op)(e)))))

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
    assume(group(G)(op), x ∈ G)
    val auxP = lambda(y,
      (y ∈ G) /\ isIdentityElement(G)(op)(op(x)(y))
    )

    val inv = have(inverseElement(G)(op)) by Tautology.from(group.definition)

    val _1 = have(∀(x, x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))) by Tautology.from(inv, inverseElement.definition)
    val _2 = thenHave(x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by InstantiateForall(x)
    val _3 = thenHave(∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by Tautology
    val _4 = thenHave(∃(y, auxP(y))) by Tautology
    
    val eps = have(auxP(ε(y, auxP(y)))) by Tautology.from(_4, Quantifiers.existsEpsilon of (P := auxP))

    val _invDef = inverseOf(G)(op)(x) === ε(y, auxP(y))
    val invDef = have(_invDef) by Tautology.from(inverseOf.definition)

    val _5 = have(_invDef |- auxP(inverseOf(G)(op)(x))) by Substitution.Apply(_invDef)(eps)
    have(thesis) by Tautology.from(invDef, _5)
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
    assume(binaryOperation(G)(op), x ∈ G, y ∈ G)
    have(∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G))) by Tautology.from(binaryOperation.definition)
    thenHave(∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)) by InstantiateForall(x)
    thenHave(x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G) by InstantiateForall(y)
    thenHave(thesis) by Tautology
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

  val elementInSubgroupMeansItsInGroup = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ H) |- x ∈ G
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), x ∈ H)

    // From subgroup definition, we have H ⊆ G
    val step1 = have(H ⊆ G) by Tautology.from(subgroup.definition)

    // Apply subset axiom: H ⊆ G means ∀(z, (z ∈ H) ==> (z ∈ G))
    val step2 = have(∀(z, (z ∈ H) ==> (z ∈ G))) by Tautology.from(
      step1,
      Subset.subsetAxiom of (x := H, y := G)
    )

    // Instantiate with x
    val step3 = thenHave((x ∈ H) ==> (x ∈ G)) by InstantiateForall(x)

    have(x ∈ G) by Tautology.from(step3)
  }

  val rightCosetStaysInGroupLemma = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ G) |-
      (rightCoset(H)(op)(x) ⊆ G)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), x ∈ G)
    val rc = rightCoset(H)(op)(x)
    val thm1 = have(rc === (op(h)(x) | (h ∈ H))) by Tautology.from(rightCoset.definition of (g := x))
    val obs1 = have(h ∈ H |- h ∈ G) by Tautology.from(elementInSubgroupMeansItsInGroup of (x := h))
    val eq1 = rc === (op(h)(x) | (h ∈ H))

    val step2a = have(y ∈ (op(h)(x) | (h ∈ H)) <=> ∃(h ∈ H, op(h)(x) === y)) by Tautology.from(Replacement.membership of (F := lambda(h, op(h)(x)), A := H, y := y))
    val step2b = have(eq1 |- y ∈ rc <=> ∃(h ∈ H, op(h)(x) === y)) by Substitution.Apply(eq1)(step2a)
    val step2c = have(y ∈ rc <=> ∃(h ∈ H, op(h)(x) === y)) by Tautology.from(step2b, thm1)
    val step2 = have(y ∈ rc |- ∃(h ∈ H, op(h)(x) === y)) by Tautology.from(step2b, thm1)

    val goal = have(y ∈ rc |- y ∈ G) subproof {
      assume(y ∈ rc)
      val substep1 = have(∃(h ∈ H, op(h)(x) === y)) by Tautology.from(step2)
      val auxP = lambda(z, (z ∈ H) /\ (op(z)(x) === y))

      val h1 = ε(h, auxP(h))
      val hThm = have(auxP(h1)) by Tautology.from(
        substep1,
        Quantifiers.existsEpsilon of (x := h, P := auxP)
      )
      val substep2 = have(op(h1)(x) ∈ G) by Tautology.from(
        binaryOperationThm of (G := G, op := op, x := h1, y := x),
        group.definition,
        elementInSubgroupMeansItsInGroup of (x := h1),
        hThm
      )
      val substep3Eq = op(h1)(x) === y
      val substep3 = have(substep3Eq |- y ∈ G) by Substitution.Apply(substep3Eq)(substep2)
      have(y ∈ G) by Tautology.from(substep3, hThm)
    }

    val goal1 = have((y ∈ rc) ==> (y ∈ G)) by Tautology.from(goal)
    val goal2 = thenHave(∀(y, (y ∈ rc) ==> (y ∈ G))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := rc, y := G), goal2)
  }

  val identityIsUnique = Theorem(
    (group(G)(op), isIdentityElement(G)(op)(x), isIdentityElement(G)(op)(y)) |- x === y
  ) {
    assume(group(G)(op), isIdentityElement(G)(op)(x), isIdentityElement(G)(op)(y))
    val w = op(x)(y)

    // x is an identity, so op(x)(y) === y
    val step1a = have(isIdentityElement(G)(op)(x) |- ∀(a ∈ G, (op(x)(a) === a) /\ (op(a)(x) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := x)
    )
    val step1b = have(isIdentityElement(G)(op)(x) |- x ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := x)
    )
    val step1c = have(isIdentityElement(G)(op)(y) |- y ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := y)
    )
    val step1d = have(isIdentityElement(G)(op)(x) |- (y ∈ G) ==> ((op(x)(y) === y) /\ (op(y)(x) === y))) by InstantiateForall(y)(step1a)
    val step1 = have(w === y) by Tautology.from(step1d, step1c)

    // y is an identity, so op(x)(y) === x
    val step2a = have(isIdentityElement(G)(op)(y) |- ∀(a ∈ G, (op(y)(a) === a) /\ (op(a)(y) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := y)
    )
    val step2b = have(isIdentityElement(G)(op)(y) |- (x ∈ G) ==> ((op(y)(x) === x) /\ (op(x)(y) === x))) by InstantiateForall(x)(step2a)
    val step2 = have(w === x) by Tautology.from(step2b, step1b)

    // Transitivity: x === w === y
    have(x === y) by Tautology.from(
      equalityTransitivity of (x := x, y := w, z := y),
      step2,
      step1
    )
  }

  // we can multiply to both sides of an equality
  val congruence = Theorem(
    (group(G)(op), x === y) |-
      op(z)(x) === op(z)(y)
  ) {
    have(thesis) by Congruence
  }

  val congruenceRight = Theorem(
    (group(G)(op), x === y) |-
      op(x)(z) === op(y)(z)
  ) {
    have(thesis) by Congruence
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
    assume(group(G)(op), x ∈ G)
    val thm1 = have(isIdentityElement(G)(op)(op(x)(inverseOf(G)(op)(x)))) by Tautology.from(inverseProperty2)
    val thm1a = have(inverseOf(G)(op)(x) ∈ G) by Tautology.from(inverseStaysInGroup)
    val thm2 = have(isIdentityElement(G)(op)(op(inverseOf(G)(op)(x))(x))) by Tautology.from(thm1a, inverseCommutability of (x := x, y := inverseOf(G)(op)(x)), thm1)
  }

  val groupHasTheSameIdentityAsSubgroup = Theorem(
    (group(G)(op), subgroup(H)(G)(op), isIdentityElement(H)(op)(e)) |- isIdentityElement(G)(op)(e)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), isIdentityElement(H)(op)(e))
    
    val step1 = have(group(H)(op)) by Tautology.from(subgroup.definition)
    
    val step2 = have(e ∈ H) by Tautology.from(
      isIdentityElement.definition of (G := H, x := e)
    )
    
    val step3 = have(e ∈ G) by Tautology.from(
      elementInSubgroupMeansItsInGroup of (x := e),
      step2
    )
    
    val step4a = have(∀(h ∈ H, (op(e)(h) === h) /\ (op(h)(e) === h))) by Tautology.from(
      isIdentityElement.definition of (G := H, x := e)
    )
    val step4b = have((e ∈ H) ==> ((op(e)(e) === e) /\ (op(e)(e) === e))) by InstantiateForall(e)(step4a)
    val step4 = have(op(e)(e) === e) by Tautology.from(step4b, step2)
    
    val invH = inverseOf(G)(op)(e)
    val step4c = have(invH ∈ G) by Tautology.from(
      inverseStaysInGroup of (G := G, op := op, x := e),
      step3
    )
    
    val step5 = have(op(invH)(op(e)(e)) === op(invH)(e)) by Tautology.from(
      congruence of (G := G, op := op, x := op(e)(e), y := e, z := invH),
      step4
    )
    
    val eG = identityOf(G)(op)
    val step6a = have(isIdentityElement(G)(op)(op(invH)(e))) by Tautology.from(
      inverseProperty of (G := G, op := op, x := e),
      step3
    )
    val step6b = have(∃(z, isIdentityElement(G)(op)(z))) by Tautology.from(
      group.definition,
      identityElement.definition of (G := G)
    )
    val eGDef = have(eG === ε(z, isIdentityElement(G)(op)(z))) by Tautology.from(
      identityOf.definition of (G := G, op := op)
    )
    val eGEps = have(isIdentityElement(G)(op)(ε(z, isIdentityElement(G)(op)(z)))) by Tautology.from(
      step6b,
      Quantifiers.existsEpsilon of (x := z, P := lambda(z, isIdentityElement(G)(op)(z)))
    )
    val eGEq = eG === ε(z, isIdentityElement(G)(op)(z))
    val eGThmA = have(eGEq |- isIdentityElement(G)(op)(eG)) by Substitution.Apply(eGEq)(eGEps)
    val eGThm = have(isIdentityElement(G)(op)(eG)) by Tautology.from(eGThmA, eGDef)
    
    val step6 = have(op(invH)(e) === eG) by Tautology.from(
      identityIsUnique of (x := op(invH)(e), y := eG),
      step6a,
      eGThm
    )
    
    val step7 = have(op(invH)(op(e)(e)) === eG) by Tautology.from(
      equalityTransitivity of (x := op(invH)(op(e)(e)), y := op(invH)(e), z := eG),
      step5,
      step6
    )
    
    val assocG = have(associativity(G)(op)) by Tautology.from(group.definition)
    val step8 = have(op(op(invH)(e))(e) === eG) by Tautology.from(
      equalityTransitivity of (x := op(op(invH)(e))(e), y := op(invH)(op(e)(e)), z := eG),
      associativityThm of (x := invH, y := e, z := e),
      assocG,
      step4c,
      step3,
      step7
    )
    
    val step9Eq = op(invH)(e) === eG
    val step9a = have(step9Eq |- op(op(invH)(e))(e) === op(eG)(e)) by Substitution.Apply(step9Eq)(
      have(op(eG)(e) === op(eG)(e)) by Restate
    )
    val step9 = have(op(eG)(e) === eG) by Tautology.from(
      equalityTransitivity of (x := op(eG)(e), y := op(op(invH)(e))(e), z := eG),
      step9a,
      step6,
      step8
    )
    
    val step10a = have(isIdentityElement(G)(op)(eG) |- ∀(a ∈ G, (op(eG)(a) === a) /\ (op(a)(eG) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := eG)
    )
    val step10b = have(isIdentityElement(G)(op)(eG) |- (e ∈ G) ==> ((op(eG)(e) === e) /\ (op(e)(eG) === e))) by InstantiateForall(e)(step10a)
    val step10c = have(op(eG)(e) === e) by Tautology.from(step10b, eGThm, step3)
    val step10 = have(e === eG) by Tautology.from(
      equalityTransitivity of (x := e, y := op(eG)(e), z := eG),
      step10c,
      step9
    )
    
    val step11Eq = e === eG
    val step11 = have(step11Eq |- isIdentityElement(G)(op)(e)) by Substitution.Apply(step11Eq)(eGThm)
    have(thesis) by Tautology.from(step11, step10)
  }

  val subgroupHasTheSameIdentity = Theorem(
    (group(G)(op), subgroup(H)(G)(op), isIdentityElement(G)(op)(e)) |- isIdentityElement(H)(op)(e)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), isIdentityElement(G)(op)(e))
    // T.P. (e ∈ H) /\ (∀(y ∈ H, ((op(e)(y) === y) /\ (op(y)(e) === y))))

    // H is a group, so it has inverse elements
    val step1 = have(group(H)(op)) by Tautology.from(subgroup.definition)
    val step2 = have(inverseElement(H)(op)) by Tautology.from(step1, group.definition of (G := H))

    // H is non-empty (has at least one element)
    val step3 = have(identityElement(H)(op)) by Tautology.from(step1, group.definition of (G := H))

    val step4 = have(∃(e, isIdentityElement(H)(op)(e))) by Tautology.from(
      step3,
      identityElement.definition of (G := H)
    )
    val eH = identityOf(H)(op)
    val eHDef = have(eH === ε(e, isIdentityElement(H)(op)(e))) by Tautology.from(
      identityOf.definition of (G := H, op := op)
    )
    val eHEps = have(isIdentityElement(H)(op)(ε(e, isIdentityElement(H)(op)(e)))) by Tautology.from(
      step4,
      Quantifiers.existsEpsilon of (x := e, P := lambda(e, isIdentityElement(H)(op)(e)))
    )
    val eHEq = eH === ε(e, isIdentityElement(H)(op)(e))
    val eHThmA = have(eHEq |- isIdentityElement(H)(op)(eH)) by Substitution.Apply(eHEq)(eHEps)
    val eHThm = have(isIdentityElement(H)(op)(eH)) by Tautology.from(eHThmA, eHDef)

    val eHThm2 = have(isIdentityElement(G)(op)(eH)) by Tautology.from(
      groupHasTheSameIdentityAsSubgroup of (e := eH),
      eHThm
    )

    val step5 = have(eH === e) by Tautology.from(
      identityIsUnique of (x := eH, y := e),
      eHThm2
    )
    val step6Eq = eH === e
    val step6 = have(step6Eq |- isIdentityElement(H)(op)(e)) by Substitution.Apply(step6Eq)(eHThm)
    have(thesis) by Tautology.from(step6, step5)
  }

  val rightCosetMembershipTest = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, h ∈ H, a === op(h)(b))
      |- a ∈ rightCoset(H)(op)(b)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, h ∈ H, a === op(h)(b))

    val rc_def = (op(h)(b) | (h ∈ H)) === rightCoset(H)(op)(b)

    val _map = have(op(h)(b) ∈ (op(h)(b) | (h ∈ H))) by Tautology.from(
      Replacement.map of (A := H, x := h, F := lambda(h, op(h)(b)))
    )
    val _rel = have(a === op(h)(b)) by Restate
    have(a === op(h)(b) |- a ∈ (op(h)(b) | (h ∈ H))) by Substitution.Apply(a === op(h)(b))(_map)
    val _h = thenHave(a ∈ (op(h)(b) | (h ∈ H))) by Tautology.fromLastStep(_rel)

    val _1 = have(rc_def) by Tautology.from(rightCoset.definition of (g := b))
    val _2 = have(rc_def |- a ∈ rightCoset(H)(op)(b)) by Substitution.Apply(rc_def)(_h)
    have(thesis) by Tautology.from(_1, _2)
  }

  val rightCosetMembership = Theorem(
    (
      group(G)(op),
      subgroup(H)(G)(op),
      a ∈ G,
      b ∈ G,
      a ∈ rightCoset(H)(op)(b)
    )
    |- ∃(h ∈ H, a === op(h)(b))
  ) {
    assume(group(G)(op),
      subgroup(H)(G)(op),
      a ∈ G,
      b ∈ G,
      a ∈ rightCoset(H)(op)(b))
    val _h = have(a ∈ rightCoset(H)(op)(b)) by Restate
    val rc_def = (op(h)(b) | (h ∈ H)) === rightCoset(H)(op)(b)
    val _1 = have(rc_def) by Tautology.from(rightCoset.definition of (g := b))
    val _2 = have(rc_def |- a ∈ (op(h)(b) | (h ∈ H))) by Substitution.Apply(rc_def)(_h)

    /// there exists h such that a = h*b
    val _3 = have(∃(h ∈ H, a === op(h)(b))) by Tautology.from(
      _1, _2,
      Replacement.membership of (F := lambda(x, op(x)(b)), A := H, x := h, y := a)
    )
  }

  val rightCosetSubsetFromMembership = Theorem(
    ( group(G)(op),
      subgroup(H)(G)(op),
      a ∈ G,
      b ∈ G,
      a ∈ rightCoset(H)(op)(b)
    )
    |- rightCoset(H)(op)(a) ⊆ rightCoset(H)(op)(b)
  ) {
    assume(group(G)(op),
      subgroup(H)(G)(op),
      a ∈ G,
      b ∈ G,
      a ∈ rightCoset(H)(op)(b))
    
    val Ha = rightCoset(H)(op)(a)
    val Hb = rightCoset(H)(op)(b)

    have(Ha ⊆ G) by Tautology.from(
      rightCosetStaysInGroupLemma of (x := a)
    )
    thenHave(∀(x, x ∈ Ha ==> x ∈ G)) by Tautology.fromLastStep(
      ⊆.definition of (z := x, x := Ha, y := G)
    )
    thenHave(x ∈ Ha ==> x ∈ G) by InstantiateForall(x)
    val _0 = thenHave(x ∈ Ha |- x ∈ G) by Restate

    val _1 = have(∃(h ∈ H, a === op(h)(b))) by Tautology.from(rightCosetMembership)
    val _2 = have(x ∈ Ha |- ∃(h ∈ H, x === op(h)(a))) by Tautology.from(
      rightCosetMembership of (a := x, b := a),
      _0
    )

    val auxP = lambda(h, (h ∈ H) /\ (op(h)(b) === a))
    val h0 = ε(h, auxP(h))
    val _3 = have((h0 ∈ H) /\ (op(h0)(b) === a)) by Tautology.from(
      _1, Quantifiers.existsEpsilon of (P := auxP))
    val h0inH = thenHave(h0 ∈ H) by Tautology
    val h0inG = have(h0 ∈ G) by Tautology.from(
      subgroup.definition, Subset.membership of (z := h0, x := H, y := G), h0inH)

    val auxP1 = lambda(h, (h ∈ H) /\ (op(h)(a) === x))
    val h1 = ε(h, auxP1(h))
    val _4 = have(x ∈ Ha |- (h1 ∈ H) /\ (op(h1)(a) === x)) by Tautology.from(
    _2, Quantifiers.existsEpsilon of (P := auxP1))
    val h1inH = thenHave(x ∈ Ha |- h1 ∈ H) by Tautology
    val h1inG = have(x ∈ Ha |- h1 ∈ G) by Tautology.from(
      subgroup.definition, Subset.membership of (z := h1, x := H, y := G), h1inH)

    val subst = op(h0)(b) === a
    have((subst, x ∈ Ha) |- (h1 ∈ H) /\ (op(h1)(op(h0)(b)) === x)) by Substitution.Apply(subst)(_4)
    val _5 = thenHave(x ∈ Ha |- x === op(h1)(op(h0)(b))) by Tautology.fromLastStep(_3)

    val assoc = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Tautology.from(
      group.definition, associativity.definition
    )
    thenHave(h1 ∈ G |- ∀(y ∈ G, ∀(z ∈ G, op(h1)(op(y)(z)) === op(op(h1)(y))(z)))) by InstantiateForall(h1)
    thenHave((h1 ∈ G, h0 ∈ G) |- ∀(z ∈ G, op(h1)(op(h0)(z)) === op(op(h1)(h0))(z))) by InstantiateForall(h0)
    thenHave((h1 ∈ G, h0 ∈ G, b ∈ G) |- op(h1)(op(h0)(b)) === op(op(h1)(h0))(b)) by InstantiateForall(b)
    val _6 = thenHave(x ∈ Ha |- op(h1)(op(h0)(b)) === op(op(h1)(h0))(b)) by Tautology.fromLastStep(
      h1inG, h0inG
    )
    val s1 = x
    val s2 = op(h1)(op(h0)(b))
    val s3 = op(op(h1)(h0))(b)
    val _7 = have(x ∈ Ha |- x === op(op(h1)(h0))(b)) by Tautology.from(
      _5, _6, equalityTransitivity of (x := s1, y := s2, z := s3)
    )

    val h2 = op(h1)(h0)
    val h2inH = have(x ∈ Ha |- h2 ∈ H) by Tautology.from(
      h0inH, h1inH, subgroup.definition, group.definition of (G := H),
      binaryOperationThm of (G := H, x := h1, y := h0)
    )
    
    val _8 = have(x ∈ Ha |- x ∈ Hb) by Tautology.from(
      _0, _7, h2inH, rightCosetMembershipTest of (a := x, h := h2, b := b)
    )

    thenHave(x ∈ Ha ==> x ∈ Hb) by Restate
    thenHave(∀(x, x ∈ Ha ==> x ∈ Hb)) by RightForall
    thenHave(Ha ⊆ Hb) by Tautology.fromLastStep(
      ⊆.definition of (z := x, x := Ha, y := Hb)
    )
  }
  
  val cosetEqualityTheorem = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))
      |- rightCoset(H)(op)(a) === rightCoset(H)(op)(b)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))
    val _h = have(a ∈ rightCoset(H)(op)(b)) by Restate
    val rc_def = (op(h)(b) | (h ∈ H)) === rightCoset(H)(op)(b)
    val _1 = have(rc_def) by Tautology.from(rightCoset.definition of (g := b))
    val _2 = have(rc_def |- a ∈ (op(h)(b) | (h ∈ H))) by Substitution.Apply(rc_def)(_h)

    /// there exists h such that a = h*b
    val _3 = have(∃(h ∈ H, a === op(h)(b))) by Tautology.from(
      _1, _2,
      Replacement.membership of (F := lambda(x, op(x)(b)), A := H, x := h, y := a)
    )
    val auxP = lambda(h, (h ∈ H) /\ (op(h)(b) === a))
    val h0 = ε(h, auxP(h))

    val _4 = have((h0 ∈ H) /\ (op(h0)(b) === a)) by Tautology.from(
      _3, Quantifiers.existsEpsilon of (P := auxP))
    val h0inH = thenHave(h0 ∈ H) by Tautology
    
    val hInv = inverseOf(H)(op)(h0)
    val _5 = have(group(H)(op)) by Tautology.from(subgroup.definition)
    val _6 = have(hInv ∈ H) by Tautology.from(
      inverseStaysInGroup of (G := H, x := h0), _5, h0inH)
    
    val h1 = variable[Ind]
    val invRight = lambda(h1, (h1 ∈ H) /\ (isIdentityElement(H)(op)(op(h0)(h1))))
    val _hInv = hInv === ε(h1, invRight(h1))
    val _7 = have(_hInv) by Tautology.from(
      inverseOf.definition of (G := H, x := h0, y := h1)
    )
    val eps = have(∃(h1, invRight(h1)) |- invRight(ε(h1, invRight(h1)))) by Tautology.from(
      Quantifiers.existsEpsilon of (P := invRight, y := h1))
    val _8 = have(inverseElement(H)(op)) by Tautology.from(_5, group.definition of (G := H))
    
    val _9 = have(h0 ∈ H |- ∀(x ∈ H, ∃(h1 ∈ H, isIdentityElement(H)(op)(op(x)(h1))))) by Tautology.from(
      inverseElement.definition of (G := H, y := h1),
      _8
    )
    val _10 = thenHave(h0 ∈ H |- ∃(h1 ∈ H, isIdentityElement(H)(op)(op(h0)(h1)))) by InstantiateForall(h0)
    val _11 = have(∃(h1, invRight(h1))) by Tautology.from(_10, h0inH)
    val _12 = have(invRight(ε(h1, invRight(h1)))) by Tautology.from(eps, _11)
    val _13 = have(_hInv |- invRight(hInv)) by Substitution.Apply(_hInv)(_12)
    val _14 = have(invRight(hInv)) by Tautology.from(_13, _7)

    val invLeft = lambda(h1, isIdentityElement(H)(op)(op(h1)(h0)))
    
    val _15 = have(invLeft(hInv)) by Tautology.from(
      h0inH, _5, inverseProperty of (G := H, x := h0))

    val _16 = have(op(hInv)(op(h0)(b)) === op(hInv)(a)) by Tautology.from(
      _4, _5, congruence of (G := H, x := op(h0)(b), y := a, z := hInv)
    )
    val assoc = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Tautology.from(
      group.definition, associativity.definition
    )
    thenHave(hInv ∈ G |- ∀(y ∈ G, ∀(z ∈ G, op(hInv)(op(y)(z)) === op(op(hInv)(y))(z)))) by InstantiateForall(hInv)
    thenHave((hInv ∈ G, h0 ∈ G) |- ∀(z ∈ G, op(hInv)(op(h0)(z)) === op(op(hInv)(h0))(z))) by InstantiateForall(h0)
    val _17 = thenHave((hInv ∈ G, h0 ∈ G, b ∈ G) |- op(hInv)(op(h0)(b)) === op(op(hInv)(h0))(b)) by InstantiateForall(b)
    
    val h0inG = have(h0 ∈ G) by Tautology.from(
      subgroup.definition, Subset.membership of (z := h0, x := H, y := G), h0inH)
    val hInvinG = have(hInv ∈ G) by Tautology.from(
      subgroup.definition, Subset.membership of (z := hInv, x := H, y := G), _6)
    
    val _18 = have(op(hInv)(op(h0)(b)) === op(op(hInv)(h0))(b)) by Tautology.from(
      _17, h0inG, hInvinG
    )
    val s1 = op(hInv)(op(h0)(b))
    val s2 = op(op(hInv)(h0))(b)
    val s3 = op(hInv)(a)

    val _19 = have(op(op(hInv)(h0))(b) === op(hInv)(a)) by Tautology.from(
      _18, _16, Utils.equalityTransitivity of (Utils.x := s2 , Utils.y := s1, Utils.z := s3))
    val e0 = op(hInv)(h0)
    val _20 = have(isIdentityElement(H)(op)(e0)) by Tautology.from(_15)
    val _21 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
      _20, 
      groupHasTheSameIdentityAsSubgroup of (e := e0)
    )

    have(∀(y ∈ G, (op(e0)(y) === y) /\ (op(y)(e0) === y))) by Tautology.from(
      _21, isIdentityElement.definition of (x := e0)
    )
    val _22 = thenHave((op(e0)(b) === b) /\ (op(b)(e0) === b)) by InstantiateForall(b)
    
    val _23 = have(b === op(hInv)(a)) by Tautology.from(
      _22, _19, Utils.equalityTransitivity of (Utils.x := b, Utils.y := op(e0)(b), Utils.z := op(hInv)(a))
    )

    val _24 = have(b ∈ rightCoset(H)(op)(a)) by Tautology.from(
      _23,
      _6,
      rightCosetMembershipTest of (a := b, b := a, h := hInv)
    )
    
    val Ha = rightCoset(H)(op)(a)
    val Hb = rightCoset(H)(op)(b)
    have(Ha ⊆ Hb /\ Hb ⊆ Ha) by Tautology.from(
      _h, _24,
      rightCosetSubsetFromMembership,
      rightCosetSubsetFromMembership of (a := b, b := a)
    )
    thenHave(thesis) by Tautology.fromLastStep(
      doubleInclusion of (x := Ha, y := Hb)
    )
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
