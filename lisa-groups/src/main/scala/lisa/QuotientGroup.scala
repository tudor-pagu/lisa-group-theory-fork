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
import lisa.maths.GroupTheory.NormalSubgroups.*
import lisa.maths.GroupTheory.QuotientGroup.*
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

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

  val G = variable[Ind]
  val Pr = variable[Ind]
  val H = variable[Ind]
  val C = variable[Ind]
  val op = variable[Ind >>: Ind >>: Ind]
  val op2 = variable[Ind >>: Ind >>: Ind]

  val cosetOperationProperty = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), isCosetOperation(G)(H)(op)(op2), a ∈ G, b ∈ G)
    |- op2(leftCoset(a)(op)(H))(leftCoset(b)(op)(H)) === leftCoset(op(a)(b))(op)(H)
  ) {
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