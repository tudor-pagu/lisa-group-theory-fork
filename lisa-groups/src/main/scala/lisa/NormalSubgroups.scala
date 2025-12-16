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

  val conjugationInverse = Theorem(
    (group(G)(op), x ∈ G, y ∈ G)
    |- conjugation(G)(op)(y)(inverseOf(G)(op)(x)) === op(inverseOf(G)(op)(x))(op(y)(x))
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G)
    val xi = inverseOf(G)(op)(x)
    val LHS = conjugation(G)(op)(y)(xi)
    val _1 = have(LHS === op(op(xi)(y))(x)) by Congruence.from(
        doubleInverse of (x := x),
        conjugation.definition of (x := y, y := inverseOf(G)(op)(x))
    )
    val _2 = have(xi ∈ G) by Tautology.from(
        inverseStaysInGroup of (x := x)
    )
    have(thesis) by Tautology.from(
        _1, _2, applyAssociativity of (a := LHS, x := xi, y := y, z := x)
    )
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

  val conjugationInversionLeft = Theorem(
    (group(G)(op), x ∈ G, h ∈ G) 
    |- op(x)(h) === op(conjugation(G)(op)(h)(x))(x)
  ) {
    assume(group(G)(op), x ∈ G, h ∈ G) 
    val xi = inverseOf(G)(op)(x)
    val e0 = op(xi)(x)
    val xh = op(x)(h)
    val xhinG = have(xh ∈ G) by Tautology.from(
        binaryOperationThm of (x := x, y := h),
        group.definition, normalSubgroup.definition,
        elementInSubgroupMeansItsInGroup of (x := h)
    )
    val xhxi = op(xh)(xi)
    val xiinG = have(xi ∈ G) by Tautology.from(inverseStaysInGroup of (x := x))
    val _1 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
        inverseProperty of (x := x)
    )
    val _2 = have(op(xh)(op(xi)(x)) === xh) by Tautology.from(
        _1, xhinG, identityProperty of (e := e0, x := xh)
    )
    
    val _3 = have(xh === op(xhxi)(x)) by Tautology.from(
        _2, applyAssociativity of (a := xh, x := xh, y := xi, z := x),
        xhinG, xiinG
    )

    val _4 = have(conjugation(G)(op)(h)(x) === xhxi) by Tautology.from(
        conjugation.definition of (x := h, y := x)
    )
    have(thesis) by Congruence.from(_3, _4)
  }

  val conjugationInversionRight = Theorem(
  (group(G)(op), x ∈ G, h ∈ G) 
  |- op(h)(x) === op(x)(conjugation(G)(op)(h)(inverseOf(G)(op)(x)))
  ) {
    assume(group(G)(op), x ∈ G, h ∈ G)

    val xi = inverseOf(G)(op)(x)
    val xiinG = have(xi ∈ G) by Tautology.from(
        inverseStaysInGroup of (x := x)
    )

    val hx = op(h)(x)
    val hxinG = have(hx ∈ G) by Tautology.from(
        binaryOperationThm of (x := h, y := x),
        group.definition,
        normalSubgroup.definition,
        elementInSubgroupMeansItsInGroup of (x := h)
    )

    val xih = op(xi)(h)
    val xihinG = have(xih ∈ G) by Tautology.from(
        binaryOperationThm of (x := xi, y := h),
        group.definition,
        normalSubgroup.definition,
        elementInSubgroupMeansItsInGroup of (x := h),
        xiinG
    )

    val xihx = op(xih)(x)

    val e0 = op(x)(xi)
    val _1 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
        inverseProperty2 of (x := x)
    )

    val _2 = have(op(op(x)(xi))(hx) === hx) by Tautology.from(
        _1,
        identityProperty of (e := e0, x := hx),
        elementInSubgroupMeansItsInGroup of (x := hx),
        normalSubgroup.definition, hxinG
    )

    val _3 = have(op(x)(op(xi)(hx)) === hx) by Tautology.from(
        _2,
        applyAssociativity of (a := hx, x := x, y := xi, z := hx),
        xiinG,
        hxinG
    )

    val _4 = have(conjugation(G)(op)(h)(xi) === op(xi)(hx)) by Tautology.from(
        conjugationInverse of (y := h, x := x), 
        normalSubgroup.definition, elementInSubgroupMeansItsInGroup of (x := h)
    )

    have(thesis) by Congruence.from(_3, _4)
  }

  val leftCosetMultiplicationWellDefined = Theorem(
    (group(G)(op), normalSubgroup(H)(G)(op), a ∈ G, b ∈ G, c ∈ G, d ∈ G,
    leftCoset(a)(op)(H) === leftCoset(c)(op)(H), leftCoset(b)(op)(H) === leftCoset(d)(op)(H))
    |- leftCoset(op(a)(b))(op)(H) === leftCoset(op(c)(d))(op)(H)
  ) {
    assume(group(G)(op), normalSubgroup(H)(G)(op), a ∈ G, b ∈ G, c ∈ G, d ∈ G,
    leftCoset(a)(op)(H) === leftCoset(c)(op)(H), leftCoset(b)(op)(H) === leftCoset(d)(op)(H))

    val aH = leftCoset(a)(op)(H)
    val bH = leftCoset(b)(op)(H)
    val cH = leftCoset(c)(op)(H)
    val dH = leftCoset(d)(op)(H)

    val ci = inverseOf(G)(op)(c)
    val ciinG = have(ci ∈ G) by Tautology.from(inverseStaysInGroup of (x := c))
    val di = inverseOf(G)(op)(d)
    val diinG = have(di ∈ G) by Tautology.from(inverseStaysInGroup of (x := d))
    
    val cia = op(ci)(a)
    val dib = op(di)(b)
    val h1 = cia
    val h2 = dib

    val _1 = have(h1 ∈ H) by Tautology.from(
        leftCosetEqualityCondition of (a := a, b := c),
        normalSubgroup.definition
    )
    val h1inG = thenHave(h1 ∈ G) by Tautology.fromLastStep(elementInSubgroupMeansItsInGroup of (x := h1), normalSubgroup.definition)
    val _2 = have(h2 ∈ H) by Tautology.from(
        leftCosetEqualityCondition of (a := b, b := d),
        normalSubgroup.definition
    )
    val h2inG = thenHave(h2 ∈ G) by Tautology.fromLastStep(elementInSubgroupMeansItsInGroup of (x := h2), normalSubgroup.definition)

    val _3 = have(op(ci)(a) === h1) by Tautology
    val _4 = have(op(di)(b) === h2) by Tautology

    val _5 = have(a === op(c)(h1)) by Tautology.from(
        _3, applyInverseLeft of (x := a, y := c, z := h1), h1inG
    )
    val _6 = have(b === op(d)(h2)) by Tautology.from(
        _3, applyInverseLeft of (x := b, y := d, z := h2), h2inG
    )

    val _7 = have(op(a)(b) === op(op(c)(h1))(op(d)(h2))) by Congruence.from(_5, _6)

    val dh2 = op(d)(h2)
    val dh2inG = have(dh2 ∈ G) by Tautology.from(h2inG, group.definition, binaryOperationThm of (x := d, y := h2))
    val h1dh2 = op(h1)(dh2)
    val h1dh2inG = have(h1dh2 ∈ G) by Tautology.from(dh2inG, h1inG, group.definition, binaryOperationThm of (x := h1, y := dh2))
    val ab = op(a)(b)
    val abinG = have(ab ∈ G) by Tautology.from(binaryOperationThm of (x := a, y := b), group.definition)
    
    val _8 = have(ab === op(c)(h1dh2)) by Tautology.from(
        _7, applyAssociativity of (a := ab, x := c, y := h1, z := dh2),
        h1inG, dh2inG
    )
    val h1d = op(h1)(d)
    val _9 = have(h1dh2 === op(h1d)(h2)) by Tautology.from(
        associativityThm of (x := h1, y := d, z := h2), group.definition, h1inG, h2inG
    )
    val h3 = conjugation(G)(op)(h1)(di)
    val h3inH = have(h3 ∈ H) by Tautology.from(
        normalSubgroupProperty of (x := di, y := h1),
        _1, diinG
    )
    val h3inG = have(h3 ∈ G) by Tautology.from(
        h3inH, elementInSubgroupMeansItsInGroup of (x := h3), normalSubgroup.definition
    )
    
    val _10 = have(h1d === op(d)(h3)) by Tautology.from(
        conjugationInversionRight of (h := h1, x := d),
        h1inG
    )

    val _11 = have(h1dh2 === op(op(d)(h3))(h2)) by Congruence.from(_9, _10)
    val h3h2 = op(h3)(h2)
    val _12 = have(h1dh2 === op(d)(h3h2)) by Tautology.from(
        _11,
        applyAssociativity of (a := h1dh2, x := d, y := h3, z := h2),
        h2inG, h3inG
    )

    val h3h2inH = have(h3h2 ∈ H) by Tautology.from(
        binaryOperationThm of (G := H, x := h3, y := h2),
        _2, h3inH, normalSubgroup.definition, subgroup.definition, group.definition of (G := H)
    )
    val h3h2inG = have(h3h2 ∈ G) by Tautology.from(
        h3h2inH, elementInSubgroupMeansItsInGroup of (x := h3h2), normalSubgroup.definition
    )

    val _13 = have(ab === op(c)(op(d)(h3h2))) by Congruence.from(_8, _12)
    val cd = op(c)(d)
    val cdinG = have(cd ∈ G) by Tautology.from(binaryOperationThm of (x := c, y := d), group.definition)
    val _14 = have(ab === op(cd)(h3h2)) by Tautology.from(
        _13, h3h2inG, applyAssociativity of (a := ab, x := c, y := d, z := h3h2)
    )

    val cdH = leftCoset(cd)(op)(H)
    val _15 = have(ab ∈ cdH) by Tautology.from(
        _14, leftCosetMembershipTest of (a := ab, b := cd, h := h3h2),
        h3h2inH, abinG, cdinG, normalSubgroup.definition
    )
    
    have(thesis) by Tautology.from(
        _15, leftCosetEqualityTheorem of (a := ab, b := cd), normalSubgroup.definition,
        abinG, cdinG
    )
  }