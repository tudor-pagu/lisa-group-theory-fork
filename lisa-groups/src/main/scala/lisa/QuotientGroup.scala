package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}
import Symbols._

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
import lisa.utils.prooflib.SimpleDeducedSteps.{InstantiateForall, Generalize}
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.GroupTheory.NormalSubgroups.normalSubgroupProperty

import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween}
import lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.BasicTheorems.*
import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.Pair
// import lisa.maths.SetTheory.Relations.Predef.{_, given}
import lisa.maths.Quantifiers.∃!

object QuotientGroup extends lisa.Main:

  val quotientGroupMembership = Theorem(
    (x ∈ quotientGroup(G)(H)(*)) |- (equivalenceClass(G)(H)(*)(x) ∈ G) /\ (x === leftCoset(equivalenceClass(G)(H)(*)(x))(*)(H))
  ) {
    assume(x ∈ quotientGroup(G)(H)(*))
    val G_H = quotientGroup(G)(H)(*)
    val auxF = lambda(x, leftCoset(x)(*)(H))
    val G_Hdef = { leftCoset(x)(*)(H) | x ∈ G }
    val _1 = have(G_H === G_Hdef) by Tautology.from(
        quotientGroup.definition of (g := x)
    )
    val _2 = have((x ∈ G_Hdef) ==> ∃(y ∈ G, leftCoset(y)(*)(H) === x)) by Tautology.from(
        Replacement.membership of (x := y, y := x, A := G, F := auxF)
    )
    val _3 = have(G_H === G_Hdef |- (x ∈ G_H) ==> ∃(y ∈ G, leftCoset(y)(*)(H) === x)) by Substitution.Apply(G_H === G_Hdef)(_2)
    val auxP = lambda(y, (y ∈ G) /\ (leftCoset(y)(*)(H) === x))
    val _4 = have(∃(y, auxP(y))) by Tautology.from(
        _1, _3
    )
    val eps = ε(y, (y ∈ G) /\ (x === leftCoset(y)(*)(H)))
    val eq = equivalenceClass(G)(H)(*)(x)
    val _5 = have(auxP(eps)) by Tautology.from(
        _4, Quantifiers.existsEpsilon of (x := y, P := auxP)
    )
    val _6 = have(eq ∈ G) by Tautology.from(
        equalitySetMembership2 of (x := eps, y := eq, A := G),
        equivalenceClass.definition, _5
    )
    val _7 = have(x === leftCoset(eps)(*)(H)) by Tautology.from(_5)
    val _8 = have(x === leftCoset(eq)(*)(H)) by Congruence.from(
        _7, equivalenceClass.definition
    )
    have(thesis) by Tautology.from(_6, _8)
  }

  val quotientGroupMembershipTest = Theorem(
    (x === leftCoset(y)(*)(H), y ∈ G) |- x ∈ quotientGroup(G)(H)(*)
  ) {
    assume(x === leftCoset(y)(*)(H), y ∈ G)
    val yH = leftCoset(y)(*)(H)
    val G_H = quotientGroup(G)(H)(*)
    val G_Hdef = { leftCoset(x)(*)(H) | x ∈ G }
    val _1 = have(G_H === G_Hdef) by Tautology.from(
        quotientGroup.definition of (g := x)
    )

    val _2 = have(yH ∈ G_Hdef) by Tautology.from(
        Replacement.map of (x := y, A := G, F := lambda(y, leftCoset(y)(*)(H)))
    )
    val _3 = have(x === yH |- x ∈ G_Hdef) by Substitution.Apply(x === yH)(_2)
    val _4 = have(x ∈ G_Hdef) by Tautology.from(_3)
    val _5 = have(G_H === G_Hdef |- x ∈ G_H) by Substitution.Apply(G_H === G_Hdef)(_4)
    have(thesis) by Tautology.from(_1, _5)
  }

  val isCosetOperationAlternativeDefinition = Theorem(
    isCosetOperation(G)(H)(*)(**) <=> 
        ∀(A ∈ quotientGroup(G)(H)(*), ∀(B ∈ quotientGroup(G)(H)(*), 
            op(A, **, B) === { op(fst(z), *, snd(z)) | z ∈ (A × B) }
        ))
  ) {
    val G_H = quotientGroup(G)(H)(*)
    val LHS = isCosetOperation(G)(H)(*)(**)
    val S1 = ⋃{ {op(c, *, d) | c ∈ A} | d ∈ B }
    val S2 = { op(fst(z), *, snd(z)) | z ∈ (A × B) }

    val _h = have(LHS <=> ∀(A ∈ G_H, ∀(B ∈ G_H, 
      op(A, **, B) === S1
    ))) by Tautology.from(isCosetOperation.definition of (a := c, b := d))

    val _1 = have(S1 === S2) subproof {
        have(x ∈ S1 <=> x ∈ S2) by Tautology.from(doubleSetMembership, doubleSetMembership2)
        thenHave(∀(x, x ∈ S1 <=> x ∈ S2)) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(
            extensionalityAxiom of (z := x, x := S1, y := S2)
        )
    }

    val leftImplies = have(LHS |- ∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S2))) subproof {
        assume(LHS)
        have(∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S1))) by Tautology.from(_h)
        thenHave(A ∈ G_H |- ∀(B ∈ G_H, op(A, **, B) === S1)) by InstantiateForall(A)
        val _2 = thenHave((A ∈ G_H, B ∈ G_H) |- (op(A, **, B) === S1)) by InstantiateForall(B)
        have((A ∈ G_H, B ∈ G_H) |- op(A, **, B) === S2) by Congruence.from(_1, _2)
        thenHave(A ∈ G_H |- (B ∈ G_H) ==> (op(A, **, B) === S2)) by Restate
        thenHave(A ∈ G_H |- ∀(B ∈ G_H, op(A, **, B) === S2)) by RightForall
        thenHave((A ∈ G_H) ==> ∀(B ∈ G_H, op(A, **, B) === S2)) by Restate
        thenHave(thesis) by RightForall
    }
    val rightImplies = have(∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S2)) |- LHS) subproof {
        assume(∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S2)))
        have(∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S2))) by Restate
        thenHave(A ∈ G_H |- ∀(B ∈ G_H, op(A, **, B) === S2)) by InstantiateForall(A)
        val _2 = thenHave((A ∈ G_H, B ∈ G_H) |- (op(A, **, B) === S2)) by InstantiateForall(B)
        val _3 = have((A ∈ G_H, B ∈ G_H) |- (op(A, **, B) === S1)) by Congruence.from(_1, _2)
        thenHave(A ∈ G_H |- (B ∈ G_H) ==> (op(A, **, B) === S1)) by Restate
        thenHave(A ∈ G_H |- ∀(B ∈ G_H, op(A, **, B) === S1)) by RightForall
        thenHave((A ∈ G_H) ==> ∀(B ∈ G_H, op(A, **, B) === S1)) by Restate
        thenHave(∀(A ∈ G_H, ∀(B ∈ G_H, op(A, **, B) === S1))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(_h)
    }
    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val cosetOperationProperty = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**), a ∈ G, b ∈ G)
    |- op(leftCoset(a)(*)(H), **, leftCoset(b)(*)(H)) === leftCoset(op(a, *, b))(*)(H)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**), a ∈ G, b ∈ G)
    val aH = leftCoset(a)(*)(H)
    val bH = leftCoset(b)(*)(H)
    val G_H = quotientGroup(G)(H)(*)
    have(∀(A ∈ quotientGroup(G)(H)(*), ∀(B ∈ quotientGroup(G)(H)(*), 
      op(A, **, B) === ⋃{ {op(c, *, d) | c ∈ A} | d ∈ B }
    ))) by Tautology.from(isCosetOperation.definition of (a := c, b := d))

    thenHave(aH ∈ G_H |- ∀(B ∈ quotientGroup(G)(H)(*), 
      op(aH, **, B) === ⋃{ {op(c, *, d) | c ∈ aH} | d ∈ B }
    )) by InstantiateForall(aH)

    thenHave((aH ∈ G_H, bH ∈ G_H) |- (op(aH, **, bH) === ⋃{ {op(c, *, d) | c ∈ aH} | d ∈ bH })) by InstantiateForall(bH)
    val _1 = thenHave(op(aH, **, bH) === ⋃{ {op(c, *, d) | c ∈ aH} | d ∈ bH }) by Tautology.fromLastStep(
        quotientGroupMembershipTest of (x := aH, y := a),
        quotientGroupMembershipTest of (x := bH, y := b)
    )
    val LHS = op(aH, **, bH)
    val RHS = ⋃{ {op(c, *, d) | c ∈ aH} | d ∈ bH }

    val _2 = have((z ∈ RHS) <=> ∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d)))) by Tautology.from(
        doubleSetMembership of (A := aH, B := bH, a := c, b := d, x := z, * := *)
    )

    val _4 = have((z ∈ LHS) <=> ∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d)))) by Tautology.from(
        equalitySetMembership3 of (A := LHS, B := RHS, x := z),
        _1, _2
    )

    val abH = leftCoset(op(a, *, b))(*)(H)
    val ab = op(a, *, b)

    val _5 = have(∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d))) <=> z ∈ abH) subproof {
        val rightImplies = have(z ∈ abH |- ∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d)))) subproof {
            assume(z ∈ abH)
            have(∃(h ∈ H, z === op(ab, *, h))) by Tautology.from(
                leftCosetMembership of (a := z, b := ab),
                normalSubgroup.definition
            )
            val auxP = lambda(h, h ∈ H /\ (z === op(ab, *, h)))
            val h0 = ε(h, auxP(h))
            val _a1 = thenHave(h0 ∈ H /\ (z === op(ab, *, h0))) by Tautology.fromLastStep(
                Quantifiers.existsEpsilon of (x := h, P := auxP)
            )
            val h0inG = thenHave(h0 ∈ G) by Tautology.fromLastStep(
                elementInSubgroupMeansItsInGroup of (x := h0),
                normalSubgroup.definition, subgroup.definition
            )
            
            val bh0 = op(b, *, h0)
            val bh0inG = have(bh0 ∈ G) by Tautology.from(
                group.definition, binaryOperationThm of (x := b, y := h0),
                h0inG
            )
            val _a2 = have(a ∈ aH) by Tautology.from(cosetContainsRepresentative of (x := a), normalSubgroup.definition)
            val _a3 = have(bh0 ∈ bH) by Tautology.from(
                leftCosetMembershipTest of (a := bh0, h := h0, b := b), 
                normalSubgroup.definition,
                _a1, bh0inG
            )

            have(z === op(ab, *, h0)) by Tautology.from(_a1)
            val _a4 = thenHave(z === op(a, *, bh0)) by Tautology.fromLastStep(
                applyAssociativity of (a := z, x := a, y := b, z := h0), h0inG
            )
            have(a ∈ aH /\ (z === op(a, *, bh0))) by Tautology.from(_a2, _a4)
            val _a5 = thenHave(∃(c ∈ aH, z === op(c, *, bh0))) by RightExists

            have(bh0 ∈ bH /\ ∃(c ∈ aH, z === op(c, *, bh0))) by Tautology.from(_a5, _a3)
            thenHave(thesis) by RightExists
        }
        val leftImplies = have(∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d))) |- z ∈ abH) subproof {
            assume(∃(d ∈ bH, ∃(c ∈ aH, z === op(c, *, d))))
            val auxP1 = lambda(d, d ∈ bH /\ ∃(c ∈ aH, z === op(c, *, d)))
            val d0 = ε(d, auxP1(d))
            val _b1 = have(d0 ∈ bH /\ ∃(c ∈ aH, z === op(c, *, d0))) by Tautology.from(Quantifiers.existsEpsilon of (x := d, P := auxP1))
            val d0inbH = thenHave(d0 ∈ bH) by Tautology

            val auxP2  = lambda(c, c ∈ aH /\ (z === op(c, *, d0)))
            val c0 = ε(c, auxP2(c))
            val _b2 = have(c0 ∈ aH /\ (z === op(c0, *, d0))) by Tautology.from(_b1, Quantifiers.existsEpsilon of (x := c, P := auxP2))
            val c0inaH = thenHave(c0 ∈ aH) by Tautology
            
            val _b3 = have(∃(h ∈ H, c0 === op(a, *, h))) by Tautology.from(
                c0inaH, leftCosetMembership of (a := c0, b := a), normalSubgroup.definition
            )
            val auxP3 = lambda(h, h ∈ H /\ (c0 === op(a, *, h)))
            val h1 = ε(h, auxP3(h))
            val _b4 = have(h1 ∈ H /\ (c0 === op(a, *, h1))) by Tautology.from(_b3, Quantifiers.existsEpsilon of (x := h, P := auxP3))
            val h1inG = thenHave(h1 ∈ G) by Tautology.fromLastStep(normalSubgroup.definition, elementInSubgroupMeansItsInGroup of (x := h1))

            val bi = inverseOf(G)(*)(b)
            val biinG = have(bi ∈ G) by Tautology.from(inverseStaysInGroup of (x := b))
            val _b5 = have(∃(h ∈ H, d0 === op(b, *, h))) by Tautology.from(
                d0inbH, leftCosetMembership of (a := d0, b := b), normalSubgroup.definition
            )
            val auxP4 = lambda(h, h ∈ H /\ (d0 === op(b, *, h)))
            val h2 = ε(h, auxP4(h))
            val _b6 = have(h2 ∈ H /\ (d0 === op(b, *, h2))) by Tautology.from(_b5, Quantifiers.existsEpsilon of (x := h, P := auxP4))
            val h2inG = thenHave(h2 ∈ G) by Tautology.fromLastStep(normalSubgroup.definition, elementInSubgroupMeansItsInGroup of (x := h2))

            val _b7_1 = have(z === op(c0, *, d0)) by Tautology.from(_b2)
            val _b7_2 = have(c0 === op(a, *, h1)) by Tautology.from(_b4)
            val _b7_3 = have(d0 === op(b, *, h2)) by Tautology.from(_b6)
            val _b7 = have(z === op(op(a, *, h1), *, op(b, *, h2))) by Tautology.from(
                _b7_1, _b7_2, _b7_3, opSubstitution of (x := z, a := c0, b := d0, c := op(a, *, h1), d := op(b, *, h2))
            )

            val bh2 = op(b, *, h2)
            val bh2inG = have(bh2 ∈ G) by Tautology.from(binaryOperationThm of (x := b, y := h2), group.definition, h2inG)
            val h1b = op(h1, *, b)
            val h1binG = have(h1b ∈ G) by Tautology.from(binaryOperationThm of (x := h1, y := b), group.definition, h1inG)
            
            val _b8 = have(z === op(a, *, op(h1, *, bh2))) by Tautology.from(
                _b7, applyAssociativity of (a := z, x := a, y := h1, z := bh2), h1inG, bh2inG
            )
            val _b9 = have(op(h1b, *, h2) === op(h1, *, bh2)) by Tautology.from(
                _b8, associativityThm of (x := h1, y := b, z := h2), group.definition, h1inG, h2inG
            )
            val h3 = conjugation(G)(*)(h1)(bi)
            val _b10 = have(h1b === op(b, *, h3)) by Tautology.from(
                conjugationInversionRight of (h := h1, x := b), h1inG
            )

            val h3inH = have(h3 ∈ H) by Tautology.from(
                normalSubgroupProperty of (y := h1, x := bi), biinG, _b4
            )
            val h3inG = thenHave(h3 ∈ G) by Tautology.fromLastStep(
                elementInSubgroupMeansItsInGroup of (x := h3), normalSubgroup.definition
            )

            val bh3 = op(b, *, h3)
            val _b11 = have(op(h1b, *, h2) === op(bh3, *, h2)) by Tautology.from(
                opSubstitution of (x := op(h1b, *, h2), a := h1b, b := h2, c := bh3, d := h2),
                _b10
            )

            val h3h2 = op(h3, *, h2)
            val _b12 = have(op(h1b, *, h2) === op(b, *, h3h2)) by Tautology.from(
                _b11, applyAssociativity of (a := op(h1b, *, h2), x := b, y := h3, z := h2),
                h3inG, h2inG
            )

            val h3h2inH = have(h3h2 ∈ H) by Tautology.from(
                binaryOperationThm of (x := h3, y := h2, G := H),
                group.definition of (G := H), normalSubgroup.definition, subgroup.definition,
                h3inH, _b6
            )
            val h3h2inG = have(h3h2 ∈ G) by Tautology.from(
                h3h2inH, elementInSubgroupMeansItsInGroup of (x := h3h2), normalSubgroup.definition
            )

            val _b13 = have(op(h1, *, bh2) === op(b, *, h3h2)) by Tautology.from(
                _b12, _b9, equalityTransitivity of (x := op(h1, *, bh2), y := op(h1b, *, h2), z := op(b, *, h3h2))
            )
            val _b14 = have(z === op(a, *, op(b, *, h3h2))) by Tautology.from(
                _b8, _b13, opSubstitution of (x := z, a := a, b := op(h1, *, bh2), c := a, d := op(b, *, h3h2))
            )
            val _b15 = have(z === op(op(a, *, b), *, h3h2)) by Tautology.from(
                _b14, applyAssociativity of (a := z, x := a, y := b, z := h3h2), h3h2inG
            )
            have(thesis) by Tautology.from(
                _b15, leftCosetMembershipTest of (a := z, b := op(a, *, b), h := h3h2),
                h3h2inH, normalSubgroup.definition
            )
        }
        have(thesis) by Tautology.from(leftImplies, rightImplies)
    }
    
    have(z ∈ LHS <=> z ∈ abH) by Tautology.from(_4, _5)
    thenHave(∀(z, z ∈ LHS <=> z ∈ abH)) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(extensionalityAxiom of (x := LHS, y := abH))
  }

  val cosetOperationIsWellDefined = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- binaryOperation(quotientGroup(G)(H)(*))(**)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    val G_H = quotientGroup(G)(H)(*)
    
    val x0 = equivalenceClass(G)(H)(*)(x)
    val y0 = equivalenceClass(G)(H)(*)(y)
    val x0H = leftCoset(x0)(*)(H)
    val y0H = leftCoset(y0)(*)(H)
    val _1 = have((x ∈ G_H, y ∈ G_H) |- x0 ∈ G /\ (x === x0H)) by Tautology.from(quotientGroupMembership)
    val eqx = thenHave((x ∈ G_H, y ∈ G_H) |- x === x0H) by Tautology
    val _2 = have((x ∈ G_H, y ∈ G_H) |- y0 ∈ G /\ (y === y0H)) by Tautology.from(quotientGroupMembership of (x := y))
    val eqy = thenHave((x ∈ G_H, y ∈ G_H) |- y === y0H) by Tautology

    have((x ∈ G_H, y ∈ G_H) |- op(x0H, **, y0H) === leftCoset(op(x0, *, y0))(*)(H)) by Tautology.from(_1, _2, cosetOperationProperty of (a := x0, b := y0))
    thenHave((x ∈ G_H, y ∈ G_H) |- op(x, **, y0H) === leftCoset(op(x0, *, y0))(*)(H)) by Substitute(eqx)
    val _3 = thenHave((x ∈ G_H, y ∈ G_H) |- op(x, **, y) === leftCoset(op(x0, *, y0))(*)(H)) by Substitute(eqy)
    val x0y0inG = have((x ∈ G_H, y ∈ G_H) |- op(x0, *, y0) ∈ G) by Tautology.from(
      _1, _2, binaryOperationThm of (x := x0, y := y0), group.definition
    )
    val _4 = have((x ∈ G_H, y ∈ G_H) |- op(x, **, y) ∈ G_H) by Tautology.from(
      quotientGroupMembershipTest of (x := op(x, **, y), y := op(x0, *, y0)),
      _3, x0y0inG
    )

    val x_y = Pair.pair(x)(y)
    val G_H2 = (G_H × G_H)
    val _5 = have((x_y ∈ G_H2) <=> (x ∈ G_H /\ y ∈ G_H)) by Tautology.from(
      CartesianProduct.pairMembership of (A := G_H, B := G_H)
    )
    
    sorry
  }

  val cosetOperationIsAssociative = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- associativity(quotientGroup(G)(H)(*))(**)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    val G_H = quotientGroup(G)(H)(*)
    val assoc = have((x ∈ G_H, y ∈ G_H, z ∈ G_H) |- op(x, **, op(y, **, z)) === op(op(x, **, y), **, z)) subproof {
        assume(x ∈ G_H, y ∈ G_H, z ∈ G_H)
        val x0 = equivalenceClass(G)(H)(*)(x)
        val y0 = equivalenceClass(G)(H)(*)(y)
        val z0 = equivalenceClass(G)(H)(*)(z)

        val x0H = leftCoset(x0)(*)(H)
        val y0H = leftCoset(y0)(*)(H)
        val z0H = leftCoset(z0)(*)(H)

        val x0y0 = op(x0, *, y0)
        val y0z0 = op(y0, *, z0)

        val x0y0H = leftCoset(x0y0)(*)(H)
        val y0z0H = leftCoset(y0z0)(*)(H)

        val _1 = have(x0 ∈ G /\ (x === x0H)) by Tautology.from(quotientGroupMembership of (x := x))
        val eq1 = thenHave(x === x0H) by Tautology
        val _2 = have(y0 ∈ G /\ (y === y0H)) by Tautology.from(quotientGroupMembership of (x := y))
        val eq2 = thenHave(y === y0H) by Tautology
        val _3 = have(z0 ∈ G /\ (z === z0H)) by Tautology.from(quotientGroupMembership of (x := z))
        val eq3 = thenHave(z === z0H) by Tautology
        
        val x0y0inG = have(x0y0 ∈ G) by Tautology.from(_1, _2, binaryOperationThm of (x := x0, y := y0), group.definition)
        val y0z0inG = have(y0z0 ∈ G) by Tautology.from(_2, _3, binaryOperationThm of (x := y0, y := z0), group.definition)

        val _4 = have(op(x0H, **, y0H) === x0y0H) by Tautology.from(cosetOperationProperty of (a := x0, b := y0), _1, _2)
        val _5 = have(op(y0H, **, z0H) === y0z0H) by Tautology.from(cosetOperationProperty of (a := y0, b := z0), _2, _3)

        val LHS = op(x0y0H, **, z0H)
        val RHS = op(x0H, **, y0z0H)

        val _6 = have(LHS === leftCoset(op(x0y0, *, z0))(*)(H)) by Tautology.from(cosetOperationProperty of (a := x0y0, b := z0), _3, x0y0inG)
        val _7 = have(RHS === leftCoset(op(x0, *, y0z0))(*)(H)) by Tautology.from(cosetOperationProperty of (a := x0, b := y0z0), _1, y0z0inG)

        val _8 = have(op(x0y0, *, z0) === op(x0, *, y0z0)) by Tautology.from(associativityThm of (x := x0, y := y0, z := z0), group.definition, _1, _2, _3)

        have(thesis) by Congruence.from(eq1, eq2, eq3, _4, _5, _6, _7, _8)
    }
    thenHave((x ∈ G_H, y ∈ G_H) |- z ∈ G_H ==> (op(x, **, op(y, **, z)) === op(op(x, **, y), **, z))) by Restate
    thenHave((x ∈ G_H, y ∈ G_H) |- ∀(z ∈ G_H, op(x, **, op(y, **, z)) === op(op(x, **, y), **, z))) by RightForall
    thenHave((x ∈ G_H) |- y ∈ G_H ==> ∀(z ∈ G_H, op(x, **, op(y, **, z)) === op(op(x, **, y), **, z))) by Restate
    thenHave((x ∈ G_H) |- ∀(y ∈ G_H, ∀(z ∈ G_H, op(x, **, op(y, **, z)) === op(op(x, **, y), **, z)))) by RightForall
    thenHave(x ∈ G_H ==> ∀(y ∈ G_H, ∀(z ∈ G_H, op(x, **, op(y, **, z)) === op(op(x, **, y), **, z)))) by Restate
    thenHave(∀(x ∈ G_H, ∀(y ∈ G_H, ∀(z ∈ G_H, op(x, **, op(y, **, z)) === op(op(x, **, y), **, z))))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
        associativity.definition of (G := G_H, * := **)
    )
  }

  val cosetOperationIdentityElement = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- isIdentityElement(quotientGroup(G)(H)(*))(**)(H)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    val e = identityOf(G)(*)
    val eIsIdentity = have(isIdentityElement(G)(*)(e)) by Tautology.from(identityOfIsIdentity)

    val eInG = have(e ∈ G) by Tautology.from(
      eIsIdentity,
      isIdentityElement.definition of (x := e)
    )

    val E = leftCoset(e)(*)(H)

    val bigEInQ = have(E ∈ quotientGroup(G)(H)(*)) by Tautology.from(
      quotientGroupMembershipTest of (
        x := E,
        y := e
      ),
      eInG
    )

    val quotientGroupRestate = have(A ∈ quotientGroup(G)(H)(*) |- (equivalenceClass(G)(H)(*)(A) ∈ G) /\ (A === leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H))) by Tautology.from(
      quotientGroupMembership of (x := A)
    )

    val quotientGroupRestateEq = have(A ∈ quotientGroup(G)(H)(*) |- (A === leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H))) by Tautology.from(
      quotientGroupRestate
    )

    val identityInst = have(A ∈ quotientGroup(G)(H)(*) |- ((op(e, *, equivalenceClass(G)(H)(*)(A)) === equivalenceClass(G)(H)(*)(A)) /\ (op(equivalenceClass(G)(H)(*)(A), *, e) === equivalenceClass(G)(H)(*)(A)))) by Tautology.from(
      identityProperty of (
        x := equivalenceClass(G)(H)(*)(A),
        Symbols.e := identityOf(G)(*)
      ),
      eIsIdentity,
      quotientGroupRestate,
    )

    val identityInst1 = have(A ∈ quotientGroup(G)(H)(*) |- ((op(e, *, equivalenceClass(G)(H)(*)(A)) === equivalenceClass(G)(H)(*)(A)))) by Tautology.from(identityInst)
    val identityInst2 = have(A ∈ quotientGroup(G)(H)(*) |- ((op(equivalenceClass(G)(H)(*)(A), *, e)) === equivalenceClass(G)(H)(*)(A))) by Tautology.from(identityInst)

    val step1_a = have(A ∈ quotientGroup(G)(H)(*) |- op(E, **, leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H)) === leftCoset(op(e, *, equivalenceClass(G)(H)(*)(A)))(*)(H)) by Tautology.from(
      quotientGroupRestate,
      cosetOperationProperty of (
        a := e, 
        b := equivalenceClass(G)(H)(*)(A)
      ),
      eInG
    )
    val step1_b = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(E, **, leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H)) === leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H)) by Substitution.Apply(identityInst1)
    val step1_c = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(E, **, leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H)) === A) by Substitution.Apply(quotientGroupRestateEq)
    val step1_d = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(E, **, A) === A) by Substitution.Apply(quotientGroupRestateEq)
    
    val step2_a = have(A ∈ quotientGroup(G)(H)(*) |- op(leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H), **, E) === leftCoset(op(equivalenceClass(G)(H)(*)(A), *, e))(*)(H)) by Tautology.from(
      quotientGroupRestate,
      cosetOperationProperty of (
        b := e, 
        a := equivalenceClass(G)(H)(*)(A)
      ),
      eInG
    )
    val step2_b = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H), **, E) === leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H)) by Substitution.Apply(identityInst2)
    val step2_c = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(leftCoset(equivalenceClass(G)(H)(*)(A))(*)(H), **, E) === A) by Substitution.Apply(quotientGroupRestateEq)
    val step2_d = thenHave(A ∈ quotientGroup(G)(H)(*) |- op(A, **, E) === A) by Substitution.Apply(quotientGroupRestateEq)

    val step3_a = have(A ∈ quotientGroup(G)(H)(*) |- (op(E, **, A) === A) /\ (op(A, **, E) === A)) by Tautology.from(step1_d, step2_d)
    val step3_b = thenHave(A ∈ quotientGroup(G)(H)(*) ==> ((op(E, **, A) === A)/\ (op(A, **, E) === A))) by Tautology
    val step3_c = thenHave(∀(A ∈ quotientGroup(G)(H)(*), (op(E, **, A) === A) /\ (op(A, **, E) === A))) by RightForall
    val step3_d = have(isIdentityElement(quotientGroup(G)(H)(*))(**)(E)) by Tautology.from(
      bigEInQ,
      isIdentityElement.definition of (
        G := quotientGroup(G)(H)(*),
        * := **,
        x := E
      ),
      step3_c
    )

    val leftCosetIdentityRestate = have(leftCoset(e)(*)(H) === H) by Tautology.from(
      eIsIdentity,
      normalSubgroup.definition,
      leftCosetIdentity of (
        Symbols.e := identityOf(G)(*)
      )
    )

    have(thesis) by Substitution.Apply(leftCosetIdentityRestate)(step3_d)
  }

  val cosetOperationHasIdentityElement = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- identityElement(quotientGroup(G)(H)(*))(**)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    val identityIsH = have(isIdentityElement(quotientGroup(G)(H)(*))(**)(H)) by Restate.from(cosetOperationIdentityElement)

    val identityExistence = thenHave(∃(x, isIdentityElement(quotientGroup(G)(H)(*))(**)(x))) by RightExists.withParameters(H)
    have(thesis) by Tautology.from(
      identityExistence,
      identityElement.definition of (
        G := quotientGroup(G)(H)(*),
        * := **
      )
    )
  }

  val cosetOperationInverseElement = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**), x ∈ G)
    |- isIdentityElement(quotientGroup(G)(H)(*))(**)(op(leftCoset(x)(*)(H), **, leftCoset(inverseOf(G)(*)(x))(*)(H)))
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**), x ∈ G)
    val G_H = quotientGroup(G)(H)(*)
    val xH = leftCoset(x)(*)(H)
    val xi = inverseOf(G)(*)(x)
    val xiH = leftCoset(xi)(*)(H)

    val xxi = op(x, *, xi)
    val _1 = have(isIdentityElement(G)(*)(xxi)) by Tautology.from(inverseProperty2)

    val _2 = have(op(xH, **, xiH) === leftCoset(xxi)(*)(H)) by Tautology.from(
      cosetOperationProperty of (a := x, b := xi),
      inverseStaysInGroup of (x := x)
    )
    val _3 = have(leftCoset(xxi)(*)(H) === H) by Tautology.from(
      _1, leftCosetIdentity of (e := xxi), normalSubgroup.definition
    )
    val _4 = have(H === op(xH, **, xiH)) by Congruence.from(_2, _3)
    have(isIdentityElement(G_H)(**)(H)) by Tautology.from(cosetOperationIdentityElement)
    thenHave(thesis) by Substitute(_4)
  }

  val cosetOperationHasInverseElement = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- inverseElement(quotientGroup(G)(H)(*))(**)
  ) {
    assume(group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    val G_H = quotientGroup(G)(H)(*)
    val x0 = equivalenceClass(G)(H)(*)(x)
    val x0H = leftCoset(x0)(*)(H)
    val xi = inverseOf(G)(*)(x0)
    val xiH = leftCoset(xi)(*)(H)
    
    have(x ∈ G_H |- xiH ∈ G_H /\ isIdentityElement(G_H)(**)(op(x, **, xiH))) subproof {
      assume(x ∈ G_H)
      val _1 = have(x0 ∈ G /\ (leftCoset(x0)(*)(H) === x)) by Tautology.from(quotientGroupMembership)
      val _2 = have(isIdentityElement(G_H)(**)(op(x0H, **, xiH))) by Tautology.from(_1, cosetOperationInverseElement of (x := x0))
      val _3 = have(xi ∈ G) by Tautology.from(_1, inverseStaysInGroup of (x := x0))
      val _4 = have(xiH ∈ G_H) by Tautology.from(quotientGroupMembershipTest of (x := xiH, y := xi), _3)
      val _5 = have(x0H === x) by Tautology.from(_1)
      have(xiH ∈ G_H /\ isIdentityElement(G_H)(**)(op(x0H, **, xiH))) by Tautology.from(_2, _4)
      thenHave(thesis) by Substitute(_5)
    }
    thenHave(x ∈ G_H |- ∃(y ∈ G_H, isIdentityElement(G_H)(**)(op(x, **, y)))) by RightExists
    thenHave(x ∈ G_H ==> ∃(y ∈ G_H, isIdentityElement(G_H)(**)(op(x, **, y)))) by Restate
    thenHave(∀(x ∈ G_H, ∃(y ∈ G_H, isIdentityElement(G_H)(**)(op(x, **, y))))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      inverseElement.definition of (G := G_H, * := **)
    )
  }

  val quotientGroupIsGroup = Theorem(
    (group(G)(*), normalSubgroup(H)(G)(*), isCosetOperation(G)(H)(*)(**))
    |- group(quotientGroup(G)(H)(*))(**)
  ) {
    have(thesis) by Tautology.from(
        cosetOperationIsWellDefined,
        cosetOperationIsAssociative,
        cosetOperationHasIdentityElement,
        cosetOperationHasInverseElement,
        group.definition of (G := quotientGroup(G)(H)(*), * := **)
    )
  }