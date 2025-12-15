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
import lisa.maths.GroupTheory.Groups.*
import lisa.maths.GroupTheory.Subgroups.*
import lisa.maths.GroupTheory.Cosets.*
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

object Lagrange extends lisa.Main:
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

  val P, Q = variable[Ind >>: Prop]

  val G = variable[Ind]
  val Pr = variable[Ind]
  val H = variable[Ind]
  val C = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]

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
      val obs26 = have(rightCoset(H)(op)(a0) === rightCoset(H)(op)(b0)) by Tautology.from(rightCosetEqualityTheorem of (a := a0, b := b0), aThm, bThm, obs25)
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