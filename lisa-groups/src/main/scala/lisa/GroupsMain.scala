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
  val h1 = variable[Ind]
  val h2 = variable[Ind]

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

  val isIdentityElement = DEF(λ(G, λ(op, λ(x, x ∈ G /\ ∀(y ∈ G, ((op(x)(y) === y) /\ (op(y)(x) === y)))))))

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

  val subgroupHasTheSameIdentity = Theorem(
    (group(G)(op), subgroup(H)(G)(op), isIdentityElement(G)(op)(e)) |- isIdentityElement(H)(op)(e)
  ) {
    sorry
  }

  val cosetEqualityTheorem = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))
      |- rightCoset(H)(op)(a) === rightCoset(H)(op)(b)
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

    // have(∀(y ∈ rcSet, ∀(z ∈ rcSet, y ≠ z ==> (y ∩ z === ∅)))) by Sorry

    val rcSet = (rightCoset(H)(op)(x) | x ∈ G)

    val subthm3 = have((y ∈ rcSet, z ∈ rcSet, (y ∩ z) ≠ ∅) |- y === z) subproof {
      assume(y ∈ rcSet, z ∈ rcSet, (y ∩ z) ≠ ∅)
      val obs1 = have(∃(x, x ∈ (y ∩ z))) by Tautology.from(EmptySet.nonEmptyHasElement of (x := (y ∩ z), y := x))

      // we're gonna write our proof assuming
      // this, then we're gonna left exists it out
      val assump = x ∈ (y ∩ z)

      val obs2 = have(assump |- x ∈ y) by Tautology.from(
        Intersection.membership of (z := x, x := y, y := z)
      )

      val obs3 = have(assump |- x ∈ z) by Tautology.from(
        Intersection.membership of (z := x, x := y, y := z)
      )

      // val obs4 = have(∃(h1 ∈ H, x === op(h1)(a) )) by ...
      val obs4 = have((x ∈ (y ∩ z), y ∈ rcSet) |- ∃(a ∈ G, y === rightCoset(H)(op)(a))) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(op)(x)), A := G, y := y)
      )
      val obs5 = have((x ∈ (y ∩ z), y ∈ rcSet, y === rightCoset(H)(op)(a)) |- x ∈ rightCoset(H)(op)(a)) by Substitution.Apply(y === rightCoset(H)(op)(a))(obs2)
      val obs6 = have(rightCoset(H)(op)(a) === (op(h)(a) | h ∈ H)) by Tautology.from(
        rightCoset.definition of (H := H, op := op, g := a)
      )
      val obs7 = have((rightCoset(H)(op)(a) === (op(h)(a) | h ∈ H), x ∈ (y ∩ z), y ∈ rcSet, y === rightCoset(H)(op)(a)) |- x ∈ (op(h)(a) | h ∈ H)) by Substitution.Apply(
        rightCoset(H)(op)(a) === (op(h)(a) | h ∈ H)
      )(obs5)
      val obs8 = have((rightCoset(H)(op)(a) === (op(h)(a) | h ∈ H), x ∈ (y ∩ z), y ∈ rcSet, y === rightCoset(H)(op)(a)) |- ∃(h1 ∈ H, op(h1)(a) === x)) by Tautology.from(
        obs7,
        Replacement.membership of (F := lambda(h, op(h)(a)), A := H, y := x)
      )

      val obs9 = have(rightCoset(H)(op)(a) === (op(h)(a) | h ∈ H)) by Tautology.from(
        rightCoset.definition of (H := H, op := op, g := a)
      )

      val obs10 = have((assump, y === rightCoset(H)(op)(a)) |- ∃(h1 ∈ H, op(h1)(a) === x)) by Tautology.from(
        obs9,
        obs8
      )

      val obs11 = have((x ∈ (y ∩ z), z ∈ rcSet) |- ∃(b ∈ G, z === rightCoset(H)(op)(b))) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(op)(x)), A := G, y := z)
      )
      val obs12 = have((x ∈ (y ∩ z), z ∈ rcSet, z === rightCoset(H)(op)(b)) |- x ∈ rightCoset(H)(op)(b)) by Substitution.Apply(z === rightCoset(H)(op)(b))(obs3)
      val obs13 = have(rightCoset(H)(op)(b) === (op(h)(b) | h ∈ H)) by Tautology.from(
        rightCoset.definition of (H := H, op := op, g := b)
      )
      val obs14 = have((rightCoset(H)(op)(b) === (op(h)(b) | h ∈ H), x ∈ (y ∩ z), z ∈ rcSet, z === rightCoset(H)(op)(b)) |- x ∈ (op(h)(b) | h ∈ H)) by Substitution.Apply(
        rightCoset(H)(op)(b) === (op(h)(b) | h ∈ H)
      )(obs12)
      val obs15 = have((rightCoset(H)(op)(b) === (op(h)(b) | h ∈ H), x ∈ (y ∩ z), z ∈ rcSet, z === rightCoset(H)(op)(b)) |- ∃(h2 ∈ H, op(h2)(b) === x)) by Tautology.from(
        obs14,
        Replacement.membership of (F := lambda(h, op(h)(b)), A := H, y := x)
      )
      val obs16 = have(rightCoset(H)(op)(b) === (op(h)(b) | h ∈ H)) by Tautology.from(
        rightCoset.definition of (H := H, op := op, g := b)
      )
      val obs17 = have((assump, z === rightCoset(H)(op)(b)) |- ∃(h2 ∈ H, op(h2)(b) === x)) by Tautology.from(
        obs16,
        obs15
      )

      val assump2 = (assump, y === rightCoset(H)(op)(a), z === rightCoset(H)(op)(b))

      val obs18 = have(assump2 |- ∃(h1 ∈ H, op(h1)(a) === x)) by Tautology.from(obs10)
      val obs19 = thenHave(assump2 |- ∃(h1, (h1 ∈ H) /\ (op(h1)(a) === x))) by Restate
      val obs20 = have(assump2 |- ∃(h2 ∈ H, op(h2)(b) === x)) by Tautology.from(obs17)
      val obs21 = thenHave(assump2 |- ∃(h2, (h2 ∈ H) /\ (op(h2)(b) === x))) by Restate

      val obs22 = have(assump2 |- (∃(h1, (h1 ∈ H) /\ (op(h1)(a) === x))) /\ (∃(h2, (h2 ∈ H) /\ (op(h2)(b) === x)))) by Tautology.from(obs19, obs21)

      val niceResult = (h1 ∈ H) /\ (op(h1)(a) === x) /\ (h2 ∈ H) /\ (op(h2)(b) === x)
      val obs23 = have(assump2 |- ∃(h1, ∃(h2, niceResult))) by Tautology.from(
        obs22,
        Quantifiers.existentialConjunctionReverseDistribution of (
          P := lambda(h1, (h1 ∈ H) /\ (op(h1)(a) === x)),
          Q := lambda(h2, (h2 ∈ H) /\ (op(h2)(b) === x))
        )
      )

      val nicerResult = (h1 ∈ H) /\ (h2 ∈ H) /\ (op(h1)(a) === op(h2)(b))

      val eq = ((op(h1)(a) === x) /\ (op(h2)(b) === x) ==> (op(h1)(a) === op(h2)(b)))
      val obs24 = have(eq) by Tautology.from(Utils.equalityTransitivity of (x := op(h1)(a), y := x, z := op(h2)(b)))

      // h1 * a = h2 *b
      val obs25 = have(niceResult |- nicerResult) by Tautology.from(obs24)

      // we wanna get to

      // a = h1^{-1} * ( h2 * b )
      val goal1 = have((assump2, nicerResult) |- (a === op(inverseOf(G)(op)(h1))(op(h2)(b)))) by Sorry
      val obs26 = have((assump2, nicerResult) |- op(inverseOf(G)(op)(h1))(op(h2)(b)) === op(op(inverseOf(G)(op)(h1))(h2))(b)) by Tautology.from(
        goal1,
        associativityThm of (x := inverseOf(G)(op)(h1), y := h2, z := b)
      )

      // do these later
      // val obs26 = thenHave(niceResult |- ∃(h2, nicerResult)) by RightExists
      // val obs27 = thenHave(niceResult |- ∃(h1, ∃(h2, nicerResult))) by RightExists
      // val obs28 = thenHave(∃(h2, niceResult) |- ∃(h1, ∃(h2, nicerResult))) by LeftExists
      // val obs29 = thenHave(∃(h1, ∃(h2, niceResult)) |- ∃(h1, ∃(h2, nicerResult))) by LeftExists
      //
      // val obs30 = have(assump2 |- ∃(h1, ∃(h2, niceResult)) ) by Tautology.from(obs29, obs23)

      // val obs4 = have(assump |- x ∈ y) by Cut(obs1, LeftExists(obs2))
      // val obs5 = have(assump |- x ∈ z) by Cut(obs1, LeftExists(obs3))

      sorry
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
