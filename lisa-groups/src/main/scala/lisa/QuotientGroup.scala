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
import lisa.maths.GroupTheory.Utils.*
import lisa.maths.GroupTheory.Groups.*
import lisa.maths.GroupTheory.Subgroups.*
import lisa.maths.GroupTheory.Cosets.*
import lisa.maths.GroupTheory.NormalSubgroups.*
import lisa.maths.GroupTheory.QuotientGroup.*
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall
import lisa.utils.prooflib.BasicStepTactic.RightForall

object QuotientGroup extends lisa.Main:
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
  val R = variable[Ind >>: Ind >>: Prop]

  val G = variable[Ind]
  val Pr = variable[Ind]
  val H = variable[Ind]
  val C = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]
  val op2 = variable[Ind >>: Ind >>: Ind]

  val quotientGroupMembership = Theorem(
    (x ∈ quotientGroup(G)(H)(op)) |- (equivalenceClass(G)(H)(op)(x) ∈ G) /\ (x === leftCoset(equivalenceClass(G)(H)(op)(x))(op)(H))
  ) {
    assume(x ∈ quotientGroup(G)(H)(op))
    val G_H = quotientGroup(G)(H)(op)
    val auxF = lambda(x, leftCoset(x)(op)(H))
    val G_Hdef = { leftCoset(x)(op)(H) | x ∈ G }
    val _1 = have(G_H === G_Hdef) by Tautology.from(
        quotientGroup.definition of (g := x)
    )
    val _2 = have((x ∈ G_Hdef) ==> ∃(y ∈ G, leftCoset(y)(op)(H) === x)) by Tautology.from(
        Replacement.membership of (x := y, y := x, A := G, F := auxF)
    )
    val _3 = have(G_H === G_Hdef |- (x ∈ G_H) ==> ∃(y ∈ G, leftCoset(y)(op)(H) === x)) by Substitution.Apply(G_H === G_Hdef)(_2)
    val auxP = lambda(y, (y ∈ G) /\ (leftCoset(y)(op)(H) === x))
    val _4 = have(∃(y, auxP(y))) by Tautology.from(
        _1, _3
    )
    val eps = ε(y, (y ∈ G) /\ (x === leftCoset(y)(op)(H)))
    val eq = equivalenceClass(G)(H)(op)(x)
    val _5 = have(auxP(eps)) by Tautology.from(
        _4, Quantifiers.existsEpsilon of (x := y, P := auxP)
    )
    val _6 = have(eq ∈ G) by Tautology.from(
        equalitySetMembership2 of (x := eps, y := eq, A := G),
        equivalenceClass.definition, _5
    )
    val _7 = have(x === leftCoset(eps)(op)(H)) by Tautology.from(_5)
    val _8 = have(x === leftCoset(eq)(op)(H)) by Congruence.from(
        _7, equivalenceClass.definition
    )
    have(thesis) by Tautology.from(_6, _8)
  }

  val quotientGroupMembershipTest = Theorem(
    (x === leftCoset(y)(op)(H), y ∈ G) |- x ∈ quotientGroup(G)(H)(op)
  ) {
    assume(x === leftCoset(y)(op)(H), y ∈ G)
    val yH = leftCoset(y)(op)(H)
    val G_H = quotientGroup(G)(H)(op)
    val G_Hdef = { leftCoset(x)(op)(H) | x ∈ G }
    val _1 = have(G_H === G_Hdef) by Tautology.from(
        quotientGroup.definition of (g := x)
    )

    val _2 = have(yH ∈ G_Hdef) by Tautology.from(
        Replacement.map of (x := y, A := G, F := lambda(y, leftCoset(y)(op)(H)))
    )
    val _3 = have(x === yH |- x ∈ G_Hdef) by Substitution.Apply(x === yH)(_2)
    val _4 = have(x ∈ G_Hdef) by Tautology.from(_3)
    val _5 = have(G_H === G_Hdef |- x ∈ G_H) by Substitution.Apply(G_H === G_Hdef)(_4)
    have(thesis) by Tautology.from(_1, _5)
  }

  val cosetOperationProperty = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2), a ∈ G, b ∈ G)
    |- op2(leftCoset(a)(op)(H))(leftCoset(b)(op)(H)) === leftCoset(op(a)(b))(op)(H)
  ) {
    assume(group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2), a ∈ G, b ∈ G)
    val aH = leftCoset(a)(op)(H)
    val bH = leftCoset(b)(op)(H)
    val G_H = quotientGroup(G)(H)(op)
    have(∀(A ∈ quotientGroup(G)(H)(op), ∀(B ∈ quotientGroup(G)(H)(op), 
      op2(A)(B) === ⋃{ {op(a)(b) | a ∈ A} | b ∈ B }
    ))) by Tautology.from(isCosetOperation.definition)

    thenHave(aH ∈ G_H |- ∀(B ∈ quotientGroup(G)(H)(op), 
      op2(aH)(B) === ⋃{ {op(a)(b) | a ∈ aH} | b ∈ B }
    )) by InstantiateForall(aH)

    thenHave((aH ∈ G_H, bH ∈ G_H) |- (op2(aH)(bH) === ⋃{ {op(a)(b) | a ∈ aH} | b ∈ bH })) by InstantiateForall(bH)
    val _1 = thenHave(op2(aH)(bH) === ⋃{ {op(a)(b) | a ∈ aH} | b ∈ bH }) by Tautology.fromLastStep(
        quotientGroupMembershipTest of (x := aH, y := a),
        quotientGroupMembershipTest of (x := bH, y := b)
    )
    val LHS = op2(aH)(bH)
    val RHS = ⋃{ {op(a)(b) | a ∈ aH} | b ∈ bH }

    sorry
  }

  val cosetOperationIsWellDefined = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2))
    |- binaryOperation(quotientGroup(G)(H)(op))(op2)
  ) {
    sorry
  }

  val cosetOperationIsAssociative = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2))
    |- associativity(quotientGroup(G)(H)(op))(op2)
  ) {
    sorry
  }

  val cosetOperationHasIdentityElement = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2))
    |- identityElement(quotientGroup(G)(H)(op))(op2)
  ) {
    sorry
  }

  val cosetOperationHasInverseElement = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2))
    |- inverseElement(quotientGroup(G)(H)(op))(op2)
  ) {
    sorry
  }

  val quotientGroupIsGroup = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2))
    |- group(quotientGroup(G)(H)(op))(op2)
  ) {
    have(thesis) by Tautology.from(
        cosetOperationIsWellDefined,
        cosetOperationIsAssociative,
        cosetOperationHasIdentityElement,
        cosetOperationHasInverseElement,
        group.definition of (G := quotientGroup(G)(H)(op), op := op2)
    )
  }