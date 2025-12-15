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
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

object NormalSubgroups extends lisa.Main:
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

  val normalSubgroupProperty = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), x ∈ G, y ∈ H)
    |- conjugation(G)(op)(y)(x) ∈ H
  ) {
    assume(group(G)(op), normalSubgroup(H)(G)(op), x ∈ G, y ∈ H)
    val xH = leftCoset(x)(op)(H)
    val Hx = rightCoset(H)(op)(x)

    have(∀(x ∈ G, xH === Hx)) by Tautology.from(
        normalSubgroup.definition of (g := x)
    )
    val _1 = thenHave(xH === Hx) by InstantiateForall(x)

    have(∀(z, z ∈ xH <=> z ∈ Hx)) by Tautology.from(
        _1, extensionalityAxiom of (x := xH, y := Hx)
    )
    val xy = op(x)(y)
    val _2 = thenHave(xy ∈ xH <=> xy ∈ Hx) by InstantiateForall(xy)
    
    val yinG = have(y ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (x := y),
        normalSubgroup.definition
    )
    val xyinG = have(xy ∈ G) by Tautology.from(
        binaryOperationThm of (x := x, y := y),
        yinG,
        group.definition
    )
    have(xy === op(x)(y)) by Tautology
    val _3 = thenHave(xy ∈ xH) by Tautology.fromLastStep(
        leftCosetMembershipTest of (a := xy, b := x, h := y),
        xyinG,
        normalSubgroup.definition
    )

    val _4 = have(xy ∈ Hx) by Tautology.from(_2, _3)

    val _5 = have(∃(h ∈ H, xy === op(h)(x))) by Tautology.from(
        rightCosetMembership of (a := xy, b := x),
        _4, xyinG, normalSubgroup.definition 
    )

    val auxP = lambda(h, (h ∈ H) /\ (xy === op(h)(x)))
    val h0 = ε(h, auxP(h))
    val _6 = have((h0 ∈ H) /\ (xy === op(h0)(x))) by Tautology.from(
        _5, Quantifiers.existsEpsilon of (P := auxP)
    )
    val h0inH = thenHave(h0 ∈ H) by Tautology
    val h0inG = have(h0 ∈ G) by Tautology.from(
        normalSubgroup.definition,
        subgroup.definition, 
        Subset.membership of (z := h0, x := H, y := G), h0inH
    )

    val xi = inverseOf(G)(op)(x)
    val _7 = have(op(xy)(xi) === h0) by Tautology.from(
        xyinG, h0inG, _6, applyInverseRight of (x := xy, y := x, z := h0)
    )

    have(op(xy)(xi) === h0 |- op(xy)(xi) ∈ H) by Substitution.Apply(op(xy)(xi) === h0)(h0inH)
    val _8 = thenHave(op(xy)(xi) ∈ H) by Tautology.fromLastStep(_7)

    val _9 = thenHave(op(op(x)(y))(inverseOf(G)(op)(x)) ∈ H) by Tautology
    val _10 = have(conjugation(G)(op)(y)(x) === op(op(x)(y))(inverseOf(G)(op)(x))) by Tautology.from(conjugation.definition of (x := y, y := x))

    have(thesis) by Congruence.from(_9, _10)
  }

  val conjugationDistributivity = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G)
    |- op(conjugation(G)(op)(x)(z))(conjugation(G)(op)(y)(z)) === conjugation(G)(op)(op(x)(y))(z)
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)
    val LHS = op(conjugation(G)(op)(x)(z))(conjugation(G)(op)(y)(z))
    val RHS = conjugation(G)(op)(op(x)(y))(z)

    val zi = inverseOf(G)(op)(z)
    val ziinG = have(zi ∈ G) by Tautology.from(inverseStaysInGroup of (x := z))
    val zx = op(z)(x)
    val zxinG = have(zx ∈ G) by Tautology.from(group.definition, binaryOperationThm of (x := z, y := x))
    val zxz = op(zx)(zi)
    val zxzinG = have(zxz ∈ G) by Tautology.from(group.definition, ziinG, zxinG, binaryOperationThm of (x := zx, y := zi))
    val zy = op(z)(y)
    val zyinG = have(zy ∈ G) by Tautology.from(group.definition, binaryOperationThm of (x := z, y := y))
    val zyz = op(zy)(zi)
    val zyzinG = have(zyz ∈ G) by Tautology.from(group.definition, ziinG, zyinG, binaryOperationThm of (x := zy, y := zi))

    val _1 = have(zxz === conjugation(G)(op)(x)(z)) by Tautology.from(
        conjugation.definition of (x := x, y := z)
    )
    val _2 = have(zyz === conjugation(G)(op)(y)(z)) by Tautology.from(
        conjugation.definition of (x := y, y := z)
    )

    val _3 = have(LHS === op(zxz)(zyz)) by Congruence.from(_1, _2)

    val _4 = have(LHS === op(op(zxz)(zy))(zi)) by Tautology.from(
        _3,
        applyAssociativity of (a := LHS, x := zxz, y := zy, z := zi),
        zxzinG, zyinG, ziinG
    )

    have(op(zxz)(zy) === op(zxz)(zy)) by Tautology
    val _5 = thenHave(op(zxz)(zy) === op(zx)(op(zi)(zy))) by Tautology.fromLastStep(
        applyAssociativity of (a := op(zxz)(zy), x := zx, y := zi, z := zy),
        zxinG, ziinG, zyinG
    )

    have(op(zi)(zy) === op(zi)(zy)) by Tautology
    val _6 = thenHave(op(zi)(zy) === y) by Tautology.fromLastStep(
        inverseCancelsOut of (x := z, y := y),
        ziinG
    )

    val _7 = have(LHS === op(op(zx)(y))(zi)) by Congruence.from(_4, _5, _6)
    val xy = op(x)(y)
    val _8 = have(op(zx)(y) === op(z)(xy)) by Tautology.from(
        associativityThm of (x := z, y := x, z := y),
        group.definition
    )
    
    val xyinG = have(xy ∈ G) by Tautology.from(group.definition, binaryOperationThm of (x := x, y := y))
    val _9 = have(RHS === op(op(z)(xy))(zi)) by Tautology.from(
        conjugation.definition of (x := xy, y := z),
        xyinG
    )

    have(thesis) by Congruence.from(_7, _8, _9)
  }

  val leftRightCosetEquivalenceNormalSubgroup = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), x ∈ G) 
    |- leftCoset(x)(op)(H) === rightCoset(H)(op)(x)
  ) {
    assume(group(G)(op), normalSubgroup(H)(G)(op), x ∈ G)
    val xH = leftCoset(x)(op)(H)
    val Hx = rightCoset(H)(op)(x)

    have(∀(x ∈ G, xH === Hx)) by Tautology.from(
        normalSubgroup.definition of (g := x)
    )
    val _1 = thenHave(xH === Hx) by InstantiateForall(x)
  }

  val leftCosetMultiplicationWellDefined = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), a ∈ G, b ∈ G, c ∈ G, d ∈ G,
    leftCoset(a)(op)(H) === leftCoset(c)(op)(H), leftCoset(b)(op)(H) === leftCoset(d)(op)(H))
    |- leftCoset(op(a)(b))(op)(H) === leftCoset(op(c)(d))(op)(H)
  ) {
    sorry
  }