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

object Cosets extends lisa.Main:
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
