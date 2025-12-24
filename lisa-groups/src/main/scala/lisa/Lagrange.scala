package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}
import Symbols._

import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.Base.Symbols._
import lisa.maths.Quantifiers
import lisa.automation.Substitution
import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween}
import lisa.maths.SetTheory.Functions.BasicTheorems.{functionBetweenDomain, functionBetweenIsFunction, appDefinition}
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.Main
import lisa.maths.SetTheory.Relations.Relation.{relationBetween, range, dom}
import lisa.maths.SetTheory.Relations.Relation
import lisa.maths.SetTheory.Base.Replacement.map
import lisa.maths.SetTheory.Base.Replacement
import lisa.SetTheoryLibrary.{extensionalityAxiom, subsetAxiom}
import lisa.maths.SetTheory.Base.CartesianProduct.{membershipSufficientCondition, ×, membership}
import lisa.maths.SetTheory.Base.Pair.{pairSnd, extensionality}
import lisa.maths.Quantifiers.{existsOneAlternativeDefinition, ∃!}

import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.GroupTheory.Groups.*
import lisa.maths.GroupTheory.Subgroups.*
import lisa.maths.GroupTheory.Cosets.*
import lisa.maths.GroupTheory.NormalSubgroups.*
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.{InstantiateForall, Generalize}

object Lagrange extends lisa.Main:

  val lagrangesLemma1 = Theorem(
    (group(G)(*), subgroup(H)(G)(*))
      |- partition(G)((rightCoset(H)(*)(x) | x ∈ G))
  ) {
    assume(group(G)(*), subgroup(H)(G)(*))

    val subthm1 = have(y ∈ (rightCoset(H)(*)(x) | x ∈ G) |- y ⊆ G) subproof {
      assume(y ∈ (rightCoset(H)(*)(x) | x ∈ G))
      val obs1 = have(∃(x ∈ G, rightCoset(H)(*)(x) === y)) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(*)(x)), A := G, y := y)
      )
      val obs2 = have((x ∈ G, rightCoset(H)(*)(x) === y) |- rightCoset(H)(*)(x) ⊆ G) by Tautology.from(
        rightCosetStaysInGroupLemma
      )
      val obs3 = have((x ∈ G, rightCoset(H)(*)(x) === y) |- y ⊆ G) by Substitution.Apply(rightCoset(H)(*)(x) === y)(obs2)
      val obs4 = thenHave(((x ∈ G) /\ (rightCoset(H)(*)(x) === y)) |- y ⊆ G) by Restate
      val obs5 = thenHave(∃(x, (x ∈ G) /\ (rightCoset(H)(*)(x) === y)) |- y ⊆ G) by LeftExists
      val obs6 = thenHave(∃(x ∈ G, rightCoset(H)(*)(x) === y) |- y ⊆ G) by Restate
      have(y ⊆ G) by Tautology.from(obs1, obs6)
    }

    val thm1 = have(y ∈ (rightCoset(H)(*)(x) | x ∈ G) ==> y ⊆ G) by Restate.from(subthm1)
    val thm2 = thenHave(∀(y, y ∈ (rightCoset(H)(*)(x) | x ∈ G) ==> y ⊆ G)) by RightForall
    val thm3 = thenHave(∀(y ∈ (rightCoset(H)(*)(x) | x ∈ G), y ⊆ G)) by Restate

    val subthm2 = have(y ∈ G |- ∃(z ∈ (rightCoset(H)(*)(x) | x ∈ G), y ∈ z)) subproof {
      // Prove every element of G is in some right coset
      assume(y ∈ G)
      val obs1 = have(identityElement(G)(*)) by Tautology.from(group.definition)
      val obs2 = have(∃(e, isIdentityElement(G)(*)(e))) by Tautology.from(obs1, identityElement.definition)

      val obs3 = have(isIdentityElement(G)(*)(e) |- ∀(y ∈ G, ((op(e, *, y) === y) /\ (op(y, *, e) === y)))) by Tautology.from(isIdentityElement.definition of (G := G, * := *, x := e))
      val obs4 = thenHave(isIdentityElement(G)(*)(e) |- (y ∈ G) ==> ((op(e, *, y) === y) /\ (op(y, *, e) === y))) by InstantiateForall(y)
      val obs5 = have(isIdentityElement(G)(*)(e) |- (op(e, *, y) === y)) by Tautology.from(obs4)

      val cosetSet = (rightCoset(H)(*)(x) | x ∈ G)

      // KEY OBSERVATION
      val obs6 = have(rightCoset(H)(*)(y) ∈ cosetSet) by Tautology.from(Replacement.map of (F := lambda(x, rightCoset(H)(*)(x)), A := G, x := y))

      val obs7 = have(isIdentityElement(G)(*)(e) |- isIdentityElement(H)(*)(e)) by Tautology.from(
        subgroupHasTheSameIdentity
      )
      val obs8 = have(isIdentityElement(G)(*)(e) |- e ∈ H) by Tautology.from(
        obs7,
        isIdentityElement.definition of (G := H, * := *, x := e)
      )

      val obs9 = have(isIdentityElement(G)(*)(e) |- e ∈ H /\ (op(e, *, y) === op(e, *, y))) by Tautology.from(obs8)
      val obs10 = have(isIdentityElement(G)(*)(e) |- e ∈ H /\ (op(e, *, y) === op(e, *, y))) by Tautology.from(obs8)
      val obs11 = thenHave(isIdentityElement(G)(*)(e) |- ∃(h, h ∈ H /\ (op(h, *, y) === op(e, *, y)))) by RightExists
      val obs12 = thenHave(isIdentityElement(G)(*)(e) |- ∃(h ∈ H, op(h, *, y) === op(e, *, y))) by Restate
      val obs13 = have(isIdentityElement(G)(*)(e) |- op(e, *, y) ∈ (op(h, *, y) | h ∈ H)) by Tautology.from(
        obs12,
        Replacement.membership of (F := λ(h, op(h, *, y)), A := H, y := op(e, *, y))
      )
      val obs14 = have((op(h, *, y) | h ∈ H) === rightCoset(H)(*)(y)) by Tautology.from(
        rightCoset.definition of (H := H, * := *, g := y)
      )
      val obs15 = have(((op(h, *, y) | h ∈ H) === rightCoset(H)(*)(y), isIdentityElement(G)(*)(e)) |- op(e, *, y) ∈ rightCoset(H)(*)(y)) by Substitution.Apply(
        (op(h, *, y) | h ∈ H) === rightCoset(H)(*)(y)
      )(obs13)

      // KEY OBSERVATION
      val obs16 = have(isIdentityElement(G)(*)(e) |- op(e, *, y) ∈ rightCoset(H)(*)(y)) by Tautology.from(obs14, obs15)

      val obs17 = have((y === op(e, *, y), isIdentityElement(G)(*)(e)) |- y ∈ rightCoset(H)(*)(y)) by Substitution.Apply(y === op(e, *, y))(obs16)
      val obs18 = have(isIdentityElement(G)(*)(e) |- y ∈ rightCoset(H)(*)(y)) by Tautology.from(obs17, obs5)
      val obs19 = have(isIdentityElement(G)(*)(e) |- y ∈ rightCoset(H)(*)(y) /\ rightCoset(H)(*)(y) ∈ cosetSet) by Tautology.from(obs18, obs6)
      val obs20 = thenHave(isIdentityElement(G)(*)(e) |- ∃(z, y ∈ z /\ z ∈ cosetSet)) by RightExists
      val obs21 = thenHave(isIdentityElement(G)(*)(e) |- ∃(z ∈ cosetSet, y ∈ z)) by Restate
      val obs22 = thenHave(∃(e, isIdentityElement(G)(*)(e)) |- ∃(z ∈ cosetSet, y ∈ z)) by LeftExists

      val obs23 = have(∃(e, isIdentityElement(G)(*)(e))) by Tautology.from(
        group.definition,
        identityElement.definition
      )

      val obs24 = have(∃(z ∈ cosetSet, y ∈ z)) by Tautology.from(obs22, obs23)
    }

    val thm4 = have(y ∈ G ==> ∃(z ∈ (rightCoset(H)(*)(x) | x ∈ G), y ∈ z)) by Restate.from(subthm2)
    val thm5 = thenHave(∀(y, y ∈ G ==> ∃(z ∈ (rightCoset(H)(*)(x) | x ∈ G), y ∈ z))) by RightForall
    val thm6 = thenHave(∀(y ∈ G, ∃(z ∈ (rightCoset(H)(*)(x) | x ∈ G), y ∈ z))) by Restate

    val rcSet = (rightCoset(H)(*)(x) | x ∈ G)

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

      val interlude1a = have(∃(a ∈ G, y === rightCoset(H)(*)(a))) by Tautology.from(
        Replacement.membership of (F := lambda(x, rightCoset(H)(*)(x)), A := G, y := y)
      )

      val a0 = ε(a, (a ∈ G) /\ (y === rightCoset(H)(*)(a)))
      val aThm = have((a0 ∈ G) /\ (y === rightCoset(H)(*)(a0))) by Tautology.from(
        interlude1a,
        Quantifiers.existsEpsilon of (x := a, P := lambda(a, (a ∈ G) /\ (y === rightCoset(H)(*)(a))))
      )

      val interlude1b = have(∃(b ∈ G, z === rightCoset(H)(*)(b))) by Tautology.from(
        Replacement.membership of (F := lambda(y, rightCoset(H)(*)(y)), A := G, y := z)
      )

      val b0 = ε(b, (b ∈ G) /\ (z === rightCoset(H)(*)(b)))
      val bThm = have((b0 ∈ G) /\ (z === rightCoset(H)(*)(b0))) by Tautology.from(
        interlude1b,
        Quantifiers.existsEpsilon of (x := b, P := lambda(b, (b ∈ G) /\ (z === rightCoset(H)(*)(b))))
      )

      val auxEq1 = (y === rightCoset(H)(*)(a0))
      val obs5 = have(auxEq1 |- x0 ∈ rightCoset(H)(*)(a0)) by Substitution.Apply(auxEq1)(obs2)
      val obs6 = have(auxEq1) by Tautology.from(aThm)
      val obs7 = have(x0 ∈ rightCoset(H)(*)(a0)) by Tautology.from(obs5, obs6)

      val auxEq2 = (z === rightCoset(H)(*)(b0))
      val obs8 = have(auxEq2 |- x0 ∈ rightCoset(H)(*)(b0)) by Substitution.Apply(auxEq2)(obs3)
      val obs9 = have(auxEq2) by Tautology.from(bThm)
      val obs10 = have(x0 ∈ rightCoset(H)(*)(b0)) by Tautology.from(obs8, obs9)

      val auxEq3 = rightCoset(H)(*)(a0) === (op(h, *, a0) | h ∈ H)
      val obs7a = have(auxEq3 |- x0 ∈ (op(h, *, a0) | h ∈ H)) by Substitution.Apply(auxEq3)(obs7)
      val obs7b = have(auxEq3) by Tautology.from(rightCoset.definition of (H := H, * := *, g := a0))
      val obs7Unfold = have(x0 ∈ (op(h, *, a0) | h ∈ H)) by Tautology.from(obs7a, obs7b)
      val h1Ex = have(∃(h ∈ H, op(h, *, a0) === x0)) by Tautology.from(
        obs7Unfold,
        Replacement.membership of (F := lambda(h, op(h, *, a0)), A := H, y := x0)
      )
      val h1 = ε(h, (h ∈ H) /\ (op(h, *, a0) === x0))
      val h1Thm = have((h1 ∈ H) /\ (op(h1, *, a0) === x0)) by Tautology.from(
        h1Ex,
        Quantifiers.existsEpsilon of (x := h1, P := lambda(h, (h ∈ H) /\ (op(h, *, a0) === x0)))
      )

      val auxEq4 = rightCoset(H)(*)(b0) === (op(h, *, b0) | h ∈ H)
      val obs10a = have(auxEq4 |- x0 ∈ (op(h, *, b0) | h ∈ H)) by Substitution.Apply(auxEq4)(obs10)
      val obs10b = have(auxEq4) by Tautology.from(rightCoset.definition of (H := H, * := *, g := b0))
      val obs10Unfold = have(x0 ∈ (op(h, *, b0) | h ∈ H)) by Tautology.from(obs10a, obs10b)
      val h2Ex = have(∃(h ∈ H, op(h, *, b0) === x0)) by Tautology.from(
        obs10Unfold,
        Replacement.membership of (F := lambda(h, op(h, *, b0)), A := H, y := x0)
      )
      val h2 = ε(h, (h ∈ H) /\ (op(h, *, b0) === x0))
      val h2Thm = have((h2 ∈ H) /\ (op(h2, *, b0) === x0)) by Tautology.from(
        h2Ex,
        Quantifiers.existsEpsilon of (x := h, P := lambda(h, (h ∈ H) /\ (op(h, *, b0) === x0)))
      )

      val obs11 = have(op(h1, *, a0) === op(h2, *, b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := op(h1, *, a0), y := x0, z := op(h2, *, b0)),
        h1Thm,
        h2Thm
      )

      val h1Inv = inverseOf(H)(*)(h1)

      val hGroup = have(group(H)(*)) by Tautology.from(subgroup.definition)
      val obs12 = have(op(h1Inv, *, op(h1, *, a0)) === op(h1Inv, *, op(h2, *, b0))) by Tautology.from(obs11, congruence of (G := H, * := *, x := op(h1, *, a0), y := op(h2, *, b0), z := h1Inv), hGroup)

      val obs13 = have(h1Inv ∈ H) by Tautology.from(
        inverseStaysInGroup of (G := H, * := *, x := h1),
        hGroup,
        h1Thm
      )
      val obs14 = have(h1Inv ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, * := *, x := h1Inv),
        obs13
      )
      val obs15 = have(h1 ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, * := *, x := h1),
        h1Thm
      )

      val assocG = have(associativity(G)(*)) by Tautology.from(group.definition)
      val obs16 = have(op(h1Inv, *, op(h1, *, a0)) === op(op(h1Inv, *, h1), *, a0)) by Tautology.from(
        associativityThm of (x := h1Inv, y := h1, z := a0),
        assocG,
        obs14,
        obs15,
        aThm
      )

      val aux = op(h1Inv, *, h1)
      val invProp = have(isIdentityElement(H)(*)(aux)) by Tautology.from(
        inverseProperty of (G := H, * := *, x := h1),
        hGroup,
        h1Thm
      )

      val invProp2 = have(isIdentityElement(G)(*)(aux)) by Tautology.from(
        invProp,
        groupHasTheSameIdentityAsSubgroup of (e := aux)
      )

      val invH1 = have(isIdentityElement(G)(*)(x) |- (∀(y ∈ G, ((op(x, *, y) === y) /\ (op(y, *, x) === y))))) by Tautology.from(isIdentityElement.definition of (G := G))
      val invH2 = thenHave(isIdentityElement(G)(*)(x) |- ∀(y, (y ∈ G) ==> (((op(x, *, y) === y) /\ (op(y, *, x) === y))))) by Restate
      val invH3 = thenHave(isIdentityElement(G)(*)(x) |- (a0 ∈ G) ==> (((op(x, *, a0) === a0) /\ (op(a0, *, x) === a0)))) by InstantiateForall(a0)
      val invH4 = have(isIdentityElement(G)(*)(x) |- (((op(x, *, a0) === a0) /\ (op(a0, *, x) === a0)))) by Tautology.from(invH3, aThm)
      val invH5 = have(isIdentityElement(G)(*)(x) |- op(x, *, a0) === a0) by Tautology.from(invH4)
      val invH6 = have(isIdentityElement(G)(*)(x) ==> (op(x, *, a0) === a0)) by Tautology.from(invH5)
      val invH7 = thenHave(∀(x, isIdentityElement(G)(*)(x) ==> (op(x, *, a0) === a0))) by RightForall
      val invH8 = thenHave(isIdentityElement(G)(*)(aux) ==> (op(aux, *, a0) === a0)) by InstantiateForall(aux)
      val invH9 = have(op(aux, *, a0) === a0) by Tautology.from(invH8, invProp2)

      val obs17 = have(op(h1Inv, *, op(h1, *, a0)) === a0) by Tautology.from(
        Utils.equalityTransitivity of (x := op(h1Inv, *, op(h1, *, a0)), y := op(op(h1Inv, *, h1), *, a0), z := a0),
        obs16,
        invH9
      )

      val obs17Sym = have(a0 === op(h1Inv, *, op(h1, *, a0))) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(op(h1Inv, *, h1), *, a0), z := op(h1Inv, *, op(h1, *, a0))),
        invH9,
        obs16
      )
      val obs18 = have(a0 === op(h1Inv, *, op(h2, *, b0))) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(h1Inv, *, op(h1, *, a0)), z := op(h1Inv, *, op(h2, *, b0))),
        obs17Sym,
        obs12
      )

      val obs19 = have(h2 ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (H := H, G := G, * := *, x := h2),
        h2Thm
      )
      val obs20 = have(b0 ∈ G) by Tautology.from(bThm)

      val obs21 = have(op(h1Inv, *, op(h2, *, b0)) === op(op(h1Inv, *, h2), *, b0)) by Tautology.from(
        associativityThm of (x := h1Inv, y := h2, z := b0),
        assocG,
        obs14,
        obs19,
        obs20
      )

      val obs22 = have(a0 === op(op(h1Inv, *, h2), *, b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := a0, y := op(h1Inv, *, op(h2, *, b0)), z := op(op(h1Inv, *, h2), *, b0)),
        obs18,
        obs21
      )

      val obs23 = have(op(h1Inv, *, h2) ∈ H) by Tautology.from(
        binaryOperationThm of (G := H, * := *, x := h1Inv, y := h2),
        hGroup,
        group.definition of (G := H, * := *),
        obs13,
        h2Thm
      )

      val obs24Eq = (op(h, *, b0) | (h ∈ H)) === rightCoset(H)(*)(b0)
      val obs24a1 = have((op(h, *, g) | (h ∈ H)) === rightCoset(H)(*)(g)) by Tautology.from(rightCoset.definition)
      val obs24a2 = thenHave(∀(g, (op(h, *, g) | (h ∈ H)) === rightCoset(H)(*)(g))) by RightForall
      val obs24a3 = thenHave((op(h, *, b0) | (h ∈ H)) === rightCoset(H)(*)(b0)) by InstantiateForall(b0)
      val obs24a = thenHave(obs24Eq) by Restate

      val obs24b1 = have((∃(h ∈ H, op(h, *, b0) === a0)) ==> (a0 ∈ { op(h, *, b0) | h ∈ H })) by Tautology.from(Replacement.membership of (A := H, y := a0, F := lambda(h, op(h, *, b0))))
      val obs24b2 = have((op(h1Inv, *, h2) ∈ H) /\ (a0 === op(op(h1Inv, *, h2), *, b0))) by Tautology.from(obs23, obs22)
      val obs24b3 = thenHave(∃(h, (h ∈ H) /\ (a0 === op(h, *, b0)))) by RightExists
      val obs24b4 = have(∃(h, (h ∈ H) /\ (op(h, *, b0) === a0))) by Tautology.from(obs24b3)
      val obs24b = have(a0 ∈ (op(h, *, b0) | (h ∈ H))) by Tautology.from(obs24b1, obs24b4)

      val obs25c = have(obs24Eq |- a0 ∈ rightCoset(H)(*)(b0)) by Substitution.Apply(obs24Eq)(obs24b)
      val obs25 = have(a0 ∈ rightCoset(H)(*)(b0)) by Tautology.from(obs25c, obs24a)
      val obs26 = have(rightCoset(H)(*)(a0) === rightCoset(H)(*)(b0)) by Tautology.from(rightCosetEqualityTheorem of (a := a0, b := b0), aThm, bThm, obs25)
      val obs27a = have(y === rightCoset(H)(*)(b0)) by Tautology.from(
        Utils.equalityTransitivity of (x := y, y := rightCoset(H)(*)(a0), z := rightCoset(H)(*)(b0)),
        aThm,
        obs26
      )
      val obs27 = have(y === z) by Tautology.from(
        Utils.equalityTransitivity of (x := y, y := rightCoset(H)(*)(b0), z := z),
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

    have(partition(G)((rightCoset(H)(*)(x) | x ∈ G))) by Tautology.from(
      thm3,
      thm6,
      thm11,
      partition.definition of (G := G, Pr := (rightCoset(H)(*)(x) | x ∈ G))
    )
  }

  val lagrangesLemma2 = Theorem(
    (group(G)(*), subgroup(H)(G)(*), x ∈ G) |-
      ∃(f, bijective(f)(H)(rightCoset(H)(*)(x)))
  ) {

    val pairInReplacement = have((group(G)(*), subgroup(H)(G)(*), x ∈ G, y ∈ H) |- (y,op(y, *, x)) ∈ ((h,op(h, *, x)) | (h ∈ H))) subproof {
      assume(group(G)(*), subgroup(H)(G)(*), x ∈ G, y ∈ H)
      val func = ((h,op(h, *, x)) | (h ∈ H))
      val membFunc = λ(h, (h,op(h, *, x)))
      val yPair = (y, op(y, *, x))

      have(y ∈ H /\ (membFunc(y) === yPair)) by Tautology
      val existsH = thenHave(∃(h ∈ H, membFunc(h) === yPair)) by RightExists.withParameters(y)
      
      val replacementEq = have(func === (membFunc(h) | (h ∈ H))) by Tautology
      val membEquiv = have((yPair ∈ func) <=> existsH.statement.right.head) by Tautology.from(
        Replacement.membership of (
          F := membFunc,
          x := h,
          y := yPair,
          A := H
        ),
        replacementEq
      )
      have(thesis) by Tautology.from(membEquiv, existsH)
    }
    
    val functionF = have(
      (group(G)(*), subgroup(H)(G)(*), x ∈ G) |- (((h,op(h, *, x)) | (h ∈ H)) :: H -> rightCoset(H)(*)(x))
      ) subproof {
        //prove relation
        val step1 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∀(z, z ∈ rightCoset(H)(*)(x) <=> z ∈ (op(h, *, x) | (h ∈ H))) <=> (rightCoset(H)(*)(x) === (op(h, *, x) | (h ∈ H)))) by Tautology.from(
          extensionalityAxiom of (x := rightCoset(H)(*)(x), y := (op(h, *, x) | (h ∈ H)))
        )
        val step2 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∀(z, z ∈ rightCoset(H)(*)(x) <=> z ∈ (op(h, *, x) | (h ∈ H)))) by Tautology.from(
          step1,
          rightCoset.definition of (g := x)
        )
        val step3 = thenHave((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- z ∈ rightCoset(H)(*)(x) <=> z ∈ (op(h, *, x) | (h ∈ H))) by InstantiateForall(z)
        val step4 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ((h ∈ H) ==> (h ∈ H /\ op(h, *, x) ∈ rightCoset(H)(*)(x)))) by Tautology.from(
          map of (x := h, F := λ(h, op(h, *, x)), A := H),
          step3 of (z := op(h, *, x))
        )
        val step5 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- (h ∈ H) ==> (h,op(h, *, x)) ∈ (H × rightCoset(H)(*)(x))) by Tautology.from(
          membershipSufficientCondition of (x := h, y := op(h, *, x), A := H, B := rightCoset(H)(*)(x)),
          step4
        )
        val step6 = thenHave((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∀(h, (h ∈ H) ==> (h,op(h, *, x)) ∈ (H × rightCoset(H)(*)(x)))) by RightForall
        val step7 = thenHave((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∀((h ∈ H), (h,op(h, *, x)) ∈ (H × rightCoset(H)(*)(x)))) by Tautology
        val step8 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∃(h ∈ H, (h,op(h, *, x)) === z) ==> (z ∈ (H × rightCoset(H)(*)(x)))) subproof {
          assume(group(G)(*), subgroup(H)(G)(*), x ∈ G, ∃(h ∈ H, (h,op(h, *, x)) === z))
          val hxz = λ(h, h ∈ H /\ ((h,op(h, *, x)) === z))
          val eps = ε(h, hxz(h))
          have(∃(h, hxz(h)) |- hxz(eps)) by Tautology.from(Quantifiers.existsEpsilon of (x := h, P := hxz))
          val epsValid = thenHave(hxz(eps)) by Tautology
          val epsEq = have(((eps,op(eps, *, x)) === z)) by Tautology.from(epsValid)
          val epsInH = have(eps ∈ H) by Tautology.from(epsValid)
          val epsInCrossCond = have(eps ∈ H ==> (eps,op(eps, *, x)) ∈ (H × rightCoset(H)(*)(x))) by InstantiateForall(eps)(step7)
          val epsInCross = have((eps,op(eps, *, x)) ∈ (H × rightCoset(H)(*)(x))) by Tautology.from(epsInH, epsInCrossCond)
          val zInCross = have(z ∈ (H × rightCoset(H)(*)(x))) by Substitution.Apply(epsEq)(epsInCross)
        }
        val step9 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- z ∈ ((h,op(h, *, x)) | (h ∈ H)) ==> z ∈ (H × rightCoset(H)(*)(x))) by Tautology.from(
          step8,
          Replacement.membership of (
            y := z, 
            F := λ(h, (h, op(h, *, x))), 
            A := H,
            x := h
          )
        )
        val step10 = thenHave((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ∀(z, z ∈ ((h,op(h, *, x)) | (h ∈ H)) ==> z ∈ (H × rightCoset(H)(*)(x)))) by RightForall
        val step11 = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- ((h,op(h, *, x)) | (h ∈ H)) ⊆ (H × rightCoset(H)(*)(x))) by Tautology.from(step10, subsetAxiom of (x := ((h,op(h, *, x)) | (h ∈ H)), y := (H × rightCoset(H)(*)(x))))
        val isRelation = have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- relationBetween(((h,op(h, *, x)) | (h ∈ H)))(H)(rightCoset(H)(*)(x))) by Tautology.from(step11, relationBetween.definition of (Relation.R := ((h,op(h, *, x)) | (h ∈ H)), X := H, Y := rightCoset(H)(*)(x)))


        // prove uniqueness
        val func = ((h,op(h, *, x)) | (h ∈ H))
        val membFunc = λ(h, (h, op(h, *, x)))
        assume(group(G)(*), subgroup(H)(G)(*), x ∈ G)
        have(y ∈ H |- (y,op(y, *, x)) ∈ func) by Tautology.from(pairInReplacement)
        val existsPair = thenHave(y ∈ H |- ∃(z, (y,z) ∈ func)) by RightExists.withParameters(op(y, *, x))

        val ifInFuncThenOp = have((y ∈ H, (y,z) ∈ func) |- z === op(y, *, x)) subproof {
          assume(y ∈ H, (y,z) ∈ func)
          val pairExists = have(∃(h ∈ H, (h,op(h, *, x)) === (y,z))) by Tautology.from(
            Replacement.membership of (F := membFunc, A := H, y := (y,z), x := h)
          )
          val hyz = λ(h, h ∈ H /\ ((h,op(h, *, x)) === (y,z)))
          val eps = ε(h, hyz(h))
          val epsCond = have(∃(h, hyz(h)) |- hyz(eps)) by Tautology.from(Quantifiers.existsEpsilon of (x := h, P := hyz))
          val epsValid = have(hyz(eps)) by Tautology.from(epsCond, pairExists)
          val epsEq = have((eps,op(eps, *, x)) === (y,z)) by Tautology.from(epsValid)

          val pairEq = have((eps === y) /\ (op(eps, *, x) === z)) by Tautology.from(
            extensionality of (a := eps, b := op(eps, *, x), c := y, d := z),
            epsEq
          )

          val epsIsY = thenHave((eps === y)) by Tautology
          have((eps === y) /\ (op(y, *, x) === z)) by Substitution.Apply(epsIsY)(pairEq)
          thenHave(thesis) by Tautology
        }

        val ifInFuncThenOpH = have((y ∈ H, (y,h) ∈ func) |- h === op(y, *, x)) by Tautology.from(ifInFuncThenOp of (z := h))

        have((y ∈ H, (y,z) ∈ func, (y,h) ∈ func) |- z === op(y, *, x)) by Tautology.from(ifInFuncThenOp)
        val hZEq = thenHave((y ∈ H, (y,z) ∈ func, (y,h) ∈ func) |- z === h) by Substitution.Apply(ifInFuncThenOpH)

        thenHave(y ∈ H |- ((y,z) ∈ func /\ (y,h) ∈ func) ==> (z === h)) by Tautology
        val uniqueForall = thenHave(y ∈ H |- ∀(z, ∀(h, ((y,z) ∈ func /\ (y,h) ∈ func) ==> (z === h)))) by Generalize
        val pred = λ(z, (y,z) ∈ func)
        val uniqueE = have(y ∈ H |- ∃!(z, (y,z) ∈ func)) by Tautology.from(
          existsOneAlternativeDefinition of (
            P := pred
          ),
          existsPair,
          uniqueForall
        )
        thenHave(y ∈ H ==> ∃!(z, (y,z) ∈ func)) by Tautology
        val uniqueEForall = thenHave(∀(y ∈ H, ∃!(z, (y,z) ∈ func))) by RightForall
        have(thesis) by Tautology.from(
          isRelation,
          uniqueEForall,
          functionBetween.definition of (
            A := H,
            B := rightCoset(H)(*)(x),
            f := func
          )
        )
      }

    val surjectiveF = have(
      (group(G)(*), subgroup(H)(G)(*), x ∈ G) |- surjective(((h,op(h, *, x)) | (h ∈ H)))(rightCoset(H)(*)(x))
      ) subproof {
        assume(group(G)(*), subgroup(H)(G)(*), x ∈ G)
        val rel = ((h,op(h, *, x)) | (h ∈ H))
        val relFunc = λ(h, (h, op(h, *, x)))
        val rangeDef = have({ snd(h) | h ∈ rel } === range(rel)) by Tautology.from(range.definition of (Relation.R := rel, z := h))
        have(y ∈ range(rel) <=> y ∈ range(rel)) by Restate
        val rangeMemEq = thenHave(y ∈ range(rel) <=> y ∈ { snd(h) | h ∈ rel }) by Substitution.Apply(rangeDef)

        val dir1 = have(y ∈ rightCoset(H)(*)(x) ==> y ∈ range(rel)) subproof {  
          val subsetImpl = have((y ∈ rightCoset(H)(*)(x), rightCoset(H)(*)(x) ⊆ G) |- (y ∈ G)) by Tautology.from(Subset.membership of (x := rightCoset(H)(*)(x), y := G, z := y))
          val yInG = have((y ∈ rightCoset(H)(*)(x)) |- y ∈ G) by Tautology.from(
            rightCosetStaysInGroupLemma,
            subsetImpl
          )  
          val step1 = have((y ∈ rightCoset(H)(*)(x)) |- ∃(h ∈ H, op(h, *, x) === y)) by Tautology.from(
            rightCosetMembership of (
              a := y,
              b := x
            ),
            yInG
          )
          val hxy = λ(h, h ∈ H /\ (op(h, *, x) === y))
          val eps = ε(h, hxy(h))
          val epsCond = have(∃(h, hxy(h)) |- hxy(eps)) by Tautology.from(Quantifiers.existsEpsilon of (x := h, P := hxy))
          val epsValid = have((y ∈ rightCoset(H)(*)(x)) |- hxy(eps)) by Tautology.from(epsCond, step1)
          val epsEq = have((y ∈ rightCoset(H)(*)(x)) |- (op(eps, *, x) === y)) by Tautology.from(epsValid)
          

          val sndIsOp = have(snd((eps,op(eps, *, x))) === op(eps, *, x)) by Tautology.from(pairSnd of (x := eps, y := op(eps, *, x)))
          val step2 = have((y ∈ rightCoset(H)(*)(x)) |- snd((eps,op(eps, *, x))) === y) by Substitution.Apply(epsEq)(sndIsOp)

          val existsBuildup = have((y ∈ rightCoset(H)(*)(x)) |- eps ∈ H /\ ((eps,op(eps, *, x)) === (eps,op(eps, *, x)))) by Tautology.from(epsValid)
          val existsInRange = thenHave((y ∈ rightCoset(H)(*)(x)) |- ∃(h ∈ H, (h,op(h, *, x)) === (eps,op(eps, *, x)))) by RightExists.withParameters(eps)

          val pairInRel = have((y ∈ rightCoset(H)(*)(x)) |- (eps,op(eps, *, x)) ∈ rel /\ (snd((eps,op(eps, *, x))) === y)) by Tautology.from(
            step2,
            Replacement.membership of (F := relFunc, A := H, y := (eps,op(eps, *, x)), x := h),
            existsInRange
          )

          val range1 = thenHave((y ∈ rightCoset(H)(*)(x)) |- ∃(h ∈ rel, snd(h) === y)) by RightExists.withParameters((eps,op(eps, *, x)))
          val range2 = have((y ∈ rightCoset(H)(*)(x)) |- y ∈ { snd(h) | h ∈ rel }) by Tautology.from(
            Replacement.membership of (
              F := snd, 
              A := rel, 
              x := h), 
            range1
          )
          have(thesis) by Tautology.from(range2,rangeMemEq)
        }

        val dir2 = have(y ∈ range(rel) ==> y ∈ rightCoset(H)(*)(x)) subproof {
          val step1 = have(y ∈ range(rel) |- ∃(h ∈ rel, snd(h) === y)) by Tautology.from(
            rangeMemEq, 
            Replacement.membership of (
              F := snd, 
              A := rel, 
              x := h
            )
          )

          val hsy = λ(h, h ∈ rel /\ (snd(h) === y))
          val eps1 = ε(h, hsy(h))
          val epsCond1 = have(∃(h, hsy(h)) |- hsy(eps1)) by Tautology.from(Quantifiers.existsEpsilon of (x := h, P := hsy))
          val epsValid1 = have((y ∈ range(rel)) |- hsy(eps1)) by Tautology.from(epsCond1, step1)
          val epsEq1 = have((y ∈ range(rel)) |- snd(eps1) === y) by Tautology.from(epsValid1)
          val epsInRel1 = have((y ∈ range(rel)) |- eps1 ∈ rel) by Tautology.from(epsValid1)

          val sndExists = have(h ∈ rel |- ∃(a ∈ H, (a, op(a, *, x)) === h)) by Tautology.from(
            Replacement.membership of (
              F := relFunc, 
              A := H, 
              x := a,
              y := h
            )
          )

          val aoh = λ(a, a ∈ H /\ ((a, op(a, *, x)) === h))
          val eps2 = ε(a, aoh(a))
          val epsCond2 = have(∃(a, aoh(a)) |- aoh(eps2)) by Tautology.from(Quantifiers.existsEpsilon of (x := a, P := aoh))
          val epsValid2 = have((h ∈ rel) |- aoh(eps2)) by Tautology.from(epsCond2, sndExists)
          val epsEq2 = have((h ∈ rel) |- (eps2, op(eps2, *, x)) === h) by Tautology.from(epsValid2)
          val epsInH2 = have((h ∈ rel) |- eps2 ∈ H) by Tautology.from(epsValid2)

          val sndRefl = have((h ∈ rel) |- snd(h) === snd(h)) by Restate
          val congruence = have((h ∈ rel) |- snd(h) === snd((eps2, op(eps2, *, x))) ) by Substitution.Apply(epsEq2)(sndRefl)
          val pairExtr = have(snd((eps2, op(eps2, *, x))) === op(eps2, *, x)) by Tautology.from(pairSnd of (x := eps2, y := op(eps2, *, x)))
          val pairExtrEq = have((h ∈ rel) |- snd(h) === op(eps2, *, x) ) by Substitution.Apply(congruence)(pairExtr)

          val hSubsG = have(H ⊆ G) by Tautology.from(subgroup.definition)
          val subsetAxiomRestate = have((H ⊆ G) |- ∀(z, (z ∈ H) ==> (z ∈ G))) by Tautology.from(subsetAxiom of (x := H, y := G))
          val epsSubsetAxiom = thenHave((H ⊆ G) |- (eps2 ∈ H) ==> (eps2 ∈ G)) by InstantiateForall(eps2)
          val eps2InG = have((h ∈ rel) |- eps2 ∈ G) by Tautology.from(epsInH2, hSubsG, epsSubsetAxiom)

          val restateBinaryOp = have(∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x, *, y) ∈ G))) by Tautology.from(binaryOperation.definition, group.definition)
          val binaryOpInstX = thenHave(∀(y, eps2 ∈ G /\ y ∈ G ==> op(eps2, *, y) ∈ G)) by InstantiateForall(eps2)
          val binaryOpInstY = thenHave(eps2 ∈ G /\ x ∈ G ==> op(eps2, *, x) ∈ G) by InstantiateForall(x)

          val opInG = have((h ∈ rel) |- op(eps2, *, x) ∈ G) by Tautology.from(binaryOpInstY, eps2InG)

          val sndInG = have(h ∈ rel |- snd(h) ∈ G) by Substitution.Apply(pairExtrEq)(opInG)
          val sndInCoset = have(h ∈ rel |- snd(h) ∈ rightCoset(H)(*)(x)) by Tautology.from(
            pairExtrEq,
            rightCosetMembershipTest of (a := snd(h), b := x, h := eps2),
            epsInH2,
            sndInG
          )
          val sndEps1InCoset = have((y ∈ range(rel)) |- snd(eps1) ∈ rightCoset(H)(*)(x)) by Tautology.from(
            epsInRel1, 
            sndInCoset of (h := eps1)
          )

          have(y ∈ range(rel) |- y ∈ rightCoset(H)(*)(x)) by Substitution.Apply(epsEq1)(sndEps1InCoset)
        }
        have(y ∈ range(rel) <=> y ∈ rightCoset(H)(*)(x)) by Tautology.from(dir1,dir2)
        val forallMemb = thenHave(∀(y,y ∈ range(rel) <=> y ∈ rightCoset(H)(*)(x))) by RightForall
        val rangeCosetEq = have(range(rel) === rightCoset(H)(*)(x)) by Tautology.from(extensionalityAxiom of (x := range(rel), y := rightCoset(H)(*)(x)), forallMemb)
        have(thesis) by Tautology.from(surjective.definition of (f := rel, B := rightCoset(H)(*)(x)), rangeCosetEq)
      }

    val injectiveF = have(
      (group(G)(*), subgroup(H)(G)(*), x ∈ G) |- injective(((h,op(h, *, x)) | (h ∈ H)))(H)
      ) subproof {
        assume(group(G)(*), subgroup(H)(G)(*), x ∈ G)
        val func = ((h,op(h, *, x)) | (h ∈ H))

        val funcBridge = have(y ∈ H |- ((app(func)(y) === op(y, *, x)))) subproof {
          assume(y ∈ H)
          val yInH = have(y ∈ H) by Tautology
          val funcFunc = have(function(func)) by Tautology.from(functionF, functionBetweenIsFunction of (f := func, A:=H, B:= rightCoset(H)(*)(x)))
          val domH = have(dom(func) === H) by Tautology.from(functionF, functionBetweenDomain of (f := func, A:=H, B:= rightCoset(H)(*)(x)))
          val yInDomH = have(y ∈ dom(func)) by Substitution.Apply(domH)(yInH)
          val pairInReplacementInst = have((y,op(y, *, x)) ∈ func) by Tautology.from(pairInReplacement)
          have(thesis) by Tautology.from(
            funcFunc,
            yInDomH,
            pairInReplacement,
            appDefinition of (
              f := func,
              x := y,
              y := op(y, *, x)
            )
          )
        }

        val opEq = have((y ∈ H, z ∈ H) |-((app(func)(y) === app(func)(z)) ==> (op(y, *, x) === op(z, *, x)))) subproof {
          assume(y ∈ H, z ∈ H)
          have((app(func)(y) === app(func)(z)) ==> (app(func)(y) === app(func)(z))) by Restate
          thenHave((app(func)(y) === app(func)(z)) ==> (op(y, *, x) === app(func)(z))) by Substitution.Apply(funcBridge)
          thenHave((app(func)(y) === app(func)(z)) ==> (op(y, *, x) === op(z, *, x))) by Substitution.Apply(funcBridge of (y := z))
        }
        val yInG = have(y ∈ H |- y ∈ G) by Tautology.from(elementInSubgroupMeansItsInGroup of (x := y))
        val zInG = have(z ∈ H |- z ∈ G) by Tautology.from(elementInSubgroupMeansItsInGroup of (x := z))
        val elimination = have((y ∈ H , z ∈ H) |- ((op(y, *, x) === op(z, *, x)) ==> (y===z))) by Tautology.from(eliminateRight of (z := x, x := y, y := z), yInG, zInG)
        have((y ∈ H, z ∈ H) |- ((app(func)(y) === app(func)(z)) ==> (y===z))) by Tautology.from(opEq, elimination)
        thenHave((y ∈ H) |- z ∈ H ==> ((app(func)(y) === app(func)(z)) ==> (y===z))) by Tautology
        thenHave(y ∈ H |- ∀(z ∈ H, ((app(func)(y) === app(func)(z)) ==> (y===z)))) by RightForall
        thenHave((y ∈ H) ==> ∀(z ∈ H, ((app(func)(y) === app(func)(z)) ==> (y===z)))) by Tautology
        val fEq = thenHave(∀(y ∈ H, ∀(z ∈ H, (app(func)(y) === app(func)(z)) ==> (y===z)))) by RightForall
        have(thesis) by Tautology.from(fEq, injective.definition of (f := func, A := H, x := y, y := z))
      }
    val bijectiveF = have(
      (group(G)(*), subgroup(H)(G)(*), x ∈ G) |- bijective(((h,op(h, *, x)) | (h ∈ H)))(H)(rightCoset(H)(*)(x))
      ) subproof {
        have(thesis) by Tautology.from(functionF, surjectiveF,injectiveF, bijective.definition of (f := ((h,op(h, *, x)) | (h ∈ H)), A := H, B := rightCoset(H)(*)(x)))
      }
    have((group(G)(*), subgroup(H)(G)(*), x ∈ G) |- bijective(((h,op(h, *, x)) | (h ∈ H)))(H)(rightCoset(H)(*)(x))) by Restate.from(bijectiveF)
    thenHave(thesis) by RightExists
  }