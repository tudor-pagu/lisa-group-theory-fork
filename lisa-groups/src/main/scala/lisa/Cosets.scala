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
import lisa.utils.fol 
import lisa.maths.GroupTheory.Subgroups.groupHasTheSameIdentityAsSubgroup

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

  val leftCosetStaysInGroupLemma = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ G) |-
      (leftCoset(x)(op)(H) ⊆ G)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), x ∈ G)

    val lc = leftCoset(x)(op)(H)
    val thm1 = have(lc === (op(x)(h) | (h ∈ H))) by Tautology.from(
        leftCoset.definition of (g := x))

    val obs1 = have(h ∈ H |- h ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup of (x := h))

    val eq1 = lc === (op(x)(h) | (h ∈ H))

    val step2a = have(y ∈ (op(x)(h) | (h ∈ H)) <=> ∃(h ∈ H, op(x)(h) === y)) by Tautology.from(
        Replacement.membership of (F := lambda(h, op(x)(h)), A := H, y := y)
    )

    val step2b = have(eq1 |- y ∈ lc <=> ∃(h ∈ H, op(x)(h) === y)) by Substitution.Apply(eq1)(step2a)

    val step2 = have(y ∈ lc |- ∃(h ∈ H, op(x)(h) === y)) by Tautology.from(step2b, thm1)

    val goal = have(y ∈ lc |- y ∈ G) subproof {
        assume(y ∈ lc)

        val substep1 =
        have(∃(h ∈ H, op(x)(h) === y)) by Tautology.from(step2)

        val auxP = lambda(z, (z ∈ H) /\ (op(x)(z) === y))
        val h1 = ε(h, auxP(h))

        val hThm =
        have(auxP(h1)) by Tautology.from(
            substep1,
            Quantifiers.existsEpsilon of (x := h, P := auxP)
        )

        val substep2 =
        have(op(x)(h1) ∈ G) by Tautology.from(
            binaryOperationThm of (G := G, op := op, x := x, y := h1),
            group.definition,
            elementInSubgroupMeansItsInGroup of (x := h1),
            hThm
        )

        val substep3Eq = op(x)(h1) === y
        val substep3 =
        have(substep3Eq |- y ∈ G) by Substitution.Apply(substep3Eq)(substep2)

        have(y ∈ G) by Tautology.from(substep3, hThm)
    }

    val goal1 = have((y ∈ lc) ==> (y ∈ G)) by Tautology.from(goal)
    val goal2 = thenHave(∀(y, (y ∈ lc) ==> (y ∈ G))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := lc, y := G), goal2)
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

  val leftCosetMembershipTest = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, h ∈ H, a === op(b)(h))
      |- a ∈ leftCoset(b)(op)(H)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, h ∈ H, a === op(b)(h))

    val lc_def = (op(b)(h) | (h ∈ H)) === leftCoset(b)(op)(H)

    val _map = have(op(b)(h) ∈ (op(b)(h) | (h ∈ H))) by Tautology.from(
        Replacement.map of (A := H, x := h, F := lambda(h, op(b)(h)))
    )

    val _rel = have(a === op(b)(h)) by Restate

    have(a === op(b)(h) |- a ∈ (op(b)(h) | (h ∈ H))) by
        Substitution.Apply(a === op(b)(h))(_map)

    val _h = thenHave(a ∈ (op(b)(h) | (h ∈ H))) by
        Tautology.fromLastStep(_rel)

    val _1 = have(lc_def) by Tautology.from(leftCoset.definition of (g := b))
    val _2 = have(lc_def |- a ∈ leftCoset(b)(op)(H)) by
        Substitution.Apply(lc_def)(_h)

    have(thesis) by Tautology.from(_1, _2)
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

  val leftCosetMembership = Theorem(
  (
    group(G)(op),
    subgroup(H)(G)(op),
    a ∈ G,
    b ∈ G,
    a ∈ leftCoset(b)(op)(H)
  )
  |- ∃(h ∈ H, a === op(b)(h))
  ) {
    assume(
        group(G)(op),
        subgroup(H)(G)(op),
        a ∈ G,
        b ∈ G,
        a ∈ leftCoset(b)(op)(H)
    )

    val _h = have(a ∈ leftCoset(b)(op)(H)) by Restate

    val lc_def = (op(b)(h) | (h ∈ H)) === leftCoset(b)(op)(H)
    val _1 = have(lc_def) by Tautology.from(
        leftCoset.definition of (g := b)
    )

    val _2 = have(lc_def |- a ∈ (op(b)(h) | (h ∈ H))) by
        Substitution.Apply(lc_def)(_h)

    have(∃(h ∈ H, a === op(b)(h))) by Tautology.from(
        _1,
        _2,
        Replacement.membership of (
        F := lambda(x, op(b)(x)),
        A := H,
        x := h,
        y := a
        )
    )
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

  val leftCosetSubsetFromMembership = Theorem(
  ( group(G)(op),
    subgroup(H)(G)(op),
    a ∈ G,
    b ∈ G,
    a ∈ leftCoset(b)(op)(H)
  )
    |- leftCoset(a)(op)(H) ⊆ leftCoset(b)(op)(H)
  ) {
    assume(group(G)(op),
        subgroup(H)(G)(op),
        a ∈ G,
        b ∈ G,
        a ∈ leftCoset(b)(op)(H))

    val Ha = leftCoset(a)(op)(H)
    val Hb = leftCoset(b)(op)(H)

    have(Ha ⊆ G) by Tautology.from(
        leftCosetStaysInGroupLemma of (x := a)
    )
    thenHave(∀(x, x ∈ Ha ==> x ∈ G)) by Tautology.fromLastStep(
        ⊆.definition of (z := x, x := Ha, y := G)
    )
    thenHave(x ∈ Ha ==> x ∈ G) by InstantiateForall(x)
    val _0 = thenHave(x ∈ Ha |- x ∈ G) by Restate

    val _1 = have(∃(h ∈ H, a === op(b)(h))) by Tautology.from(leftCosetMembership)
    val _2 = have(x ∈ Ha |- ∃(h ∈ H, x === op(a)(h))) by Tautology.from(
        leftCosetMembership of (a := x, b := a),
        _0
    )

    val auxP = lambda(h, (h ∈ H) /\ (op(b)(h) === a))
    val h0 = ε(h, auxP(h))
    val _3 = have((h0 ∈ H) /\ (op(b)(h0) === a)) by Tautology.from(
        _1, Quantifiers.existsEpsilon of (P := auxP))
    val h0inH = thenHave(h0 ∈ H) by Tautology
    val h0inG = have(h0 ∈ G) by Tautology.from(
        subgroup.definition, Subset.membership of (z := h0, x := H, y := G), h0inH)

    val auxP1 = lambda(h, (h ∈ H) /\ (op(a)(h) === x))
    val h1 = ε(h, auxP1(h))
    val _4 = have(x ∈ Ha |- (h1 ∈ H) /\ (op(a)(h1) === x)) by Tautology.from(
        _2, Quantifiers.existsEpsilon of (P := auxP1))
    val h1inH = thenHave(x ∈ Ha |- h1 ∈ H) by Tautology
    val h1inG = have(x ∈ Ha |- h1 ∈ G) by Tautology.from(
        subgroup.definition, Subset.membership of (z := h1, x := H, y := G), h1inH)

    val subst = op(b)(h0) === a
    have((subst, x ∈ Ha) |- (h1 ∈ H) /\ (op(op(b)(h0))(h1) === x)) by Substitution.Apply(subst)(_4)
    val _5 = thenHave(x ∈ Ha |- x === op(op(b)(h0))(h1)) by Tautology.fromLastStep(_3)

    val assoc = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(op(x)(y))(z) === op(x)(op(y)(z)))))) by Tautology.from(
        group.definition, associativity.definition
    )
    thenHave(b ∈ G |- ∀(y ∈ G, ∀(z ∈ G, op(op(b)(y))(z) === op(b)(op(y)(z))))) by InstantiateForall(b)
    thenHave((b ∈ G, h0 ∈ G) |- ∀(z ∈ G, op(op(b)(h0))(z) === op(b)(op(h0)(z)))) by InstantiateForall(h0)
    thenHave((b ∈ G, h0 ∈ G, h1 ∈ G) |- op(op(b)(h0))(h1) === op(b)(op(h0)(h1))) by InstantiateForall(h1)
    val _6 = thenHave(x ∈ Ha |- op(op(b)(h0))(h1) === op(b)(op(h0)(h1))) by Tautology.fromLastStep(h1inG, h0inG)
    val s1 = x
    val s2 = op(op(b)(h0))(h1)
    val s3 = op(b)(op(h0)(h1))
    val _7 = have(x ∈ Ha |- x === op(b)(op(h0)(h1))) by Tautology.from(_5, _6, equalityTransitivity of (x := s1, y := s2, z := s3))

    val h2 = op(h0)(h1)
    val h2inH = have(x ∈ Ha |- h2 ∈ H) by Tautology.from(
        h0inH, h1inH, subgroup.definition, group.definition of (G := H),
        binaryOperationThm of (G := H, x := h0, y := h1)
    )
        
    val _8 = have(x ∈ Ha |- x ∈ Hb) by Tautology.from(
        _0, _7, h2inH, leftCosetMembershipTest of (a := x, h := h2, b := b)
    )

    thenHave(x ∈ Ha ==> x ∈ Hb) by Restate
    thenHave(∀(x, x ∈ Ha ==> x ∈ Hb)) by RightForall
    thenHave(Ha ⊆ Hb) by Tautology.fromLastStep(
        ⊆.definition of (z := x, x := Ha, y := Hb)
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

  val leftCosetMembershipEquivalence = Theorem(
  (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    |- (a ∈ leftCoset(b)(op)(H)) <=> (b ∈ leftCoset(a)(op)(H))
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)

    val implication = have(a ∈ leftCoset(b)(op)(H) |- b ∈ leftCoset(a)(op)(H)) subproof {
        assume(a ∈ leftCoset(b)(op)(H))

        val aH = leftCoset(a)(op)(H)
        val bH = leftCoset(b)(op)(H)

        val _1 = have(∃(h ∈ H, a === op(b)(h))) by Tautology.from(leftCosetMembership)
        val auxP = lambda(h, (h ∈ H) /\ (a === op(b)(h)))
        val h0 = ε(h, auxP(h))

        val _2 = have((h0 ∈ H) /\ (a === op(b)(h0))) by Tautology.from(
        _1,
        Quantifiers.existsEpsilon of (P := auxP)
        )
        val h0inH = thenHave(h0 ∈ H) by Tautology
        val h0inG = thenHave(h0 ∈ G) by Tautology.fromLastStep(
        elementInSubgroupMeansItsInGroup of (x := h0)
        )

        val h1 = inverseOf(G)(op)(h0)
        val h1inG = have(h1 ∈ G) by Tautology.from(
        h0inG,
        inverseStaysInGroup of (x := h0)
        )

        val _3 = have(op(a)(h1) === b) by Tautology.from(
        applyInverseRight of (x := a, z := b, y := h0),
        _2,
        h0inG
        )

        val h1p = inverseOf(H)(op)(h0)
        val _4 = have(h1p === h1) by Tautology.from(
        inverseInSubgroupIsTheSame of (x := h0),
        h0inH
        )
        val _5 = have(h1p ∈ H) by Tautology.from(
        h0inH,
        inverseStaysInGroup of (G := H, x := h0),
        subgroup.definition
        )
        have(h1 === h1p |- h1 ∈ H) by Substitution.Apply(h1 === h1p)(_5)
        val h1inH = thenHave(h1 ∈ H) by Tautology.fromLastStep(_4)

        have(b ∈ aH) by Tautology.from(
        _3,
        leftCosetMembershipTest of (a := b, b := a, h := h1),
        h1inH
        )
    }

    have(thesis) by Tautology.from(
        implication,
        implication of (a := b, b := a)
    )
  }

  val rightCosetMembershipEquivalence = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G) |- (a ∈ rightCoset(H)(op)(b)) <=> (b ∈ rightCoset(H)(op)(a))
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    
    val implication = have(a ∈ rightCoset(H)(op)(b) |- b ∈ rightCoset(H)(op)(a)) subproof {
        assume(a ∈ rightCoset(H)(op)(b))
        val Ha = rightCoset(H)(op)(a)
        val Hb = rightCoset(H)(op)(b)

        val _1 = have(∃(h ∈ H, a === op(h)(b))) by Tautology.from(rightCosetMembership)
        val auxP = lambda(h, (h ∈ H) /\ (a === op(h)(b)))
        val h0 = ε(h, auxP(h))

        val _2 = have((h0 ∈ H) /\ (a === op(h0)(b))) by Tautology.from(
            _1,
            Quantifiers.existsEpsilon of (P := auxP)
        )
        val h0inH = thenHave(h0 ∈ H) by Tautology
        val h0inG = thenHave(h0 ∈ G) by Tautology.fromLastStep(
            elementInSubgroupMeansItsInGroup of (x := h0)
        )

        val h1 = inverseOf(G)(op)(h0)
        val h1inG = have(h1 ∈ G) by Tautology.from(
            h0inG,
            inverseStaysInGroup of (x := h0)
        )

        val _3 = have(op(h1)(a) === b) by Tautology.from(
            applyInverseLeft of (x := a, z := b, y := h0),
            _2,
            h0inG
        )

        val h1p = inverseOf(H)(op)(h0)
        val _4 = have(h1p === h1) by Tautology.from(
            inverseInSubgroupIsTheSame of (x := h0),
            h0inH
        )
        val _5 = have(h1p ∈ H) by Tautology.from(
            h0inH,
            inverseStaysInGroup of (G := H, x := h0),
            subgroup.definition
        )
        have(h1 === h1p |- h1 ∈ H) by Substitution.Apply(h1 === h1p)(_5)
        val h1inH = thenHave(h1 ∈ H) by Tautology.fromLastStep(_4)

        val _7 = have(b ∈ Ha) by Tautology.from(
            _3,
            rightCosetMembershipTest of (a := b, b := a, h := h1),
            h1inH
        )
    }

    have(thesis) by Tautology.from(
        implication,
        implication of (a := b, b := a)
    )
  }

  val leftCosetEqualityTheorem = Theorem(
  (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ leftCoset(b)(op)(H))
    |- leftCoset(a)(op)(H) === leftCoset(b)(op)(H)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ leftCoset(b)(op)(H))

    val aH = leftCoset(a)(op)(H)
    val bH = leftCoset(b)(op)(H)

    val _7 = have(b ∈ aH) by Tautology.from(
        leftCosetMembershipEquivalence
    )

    have(aH ⊆ bH /\ bH ⊆ aH) by Tautology.from(
        _7,
        leftCosetSubsetFromMembership,
        leftCosetSubsetFromMembership of (a := b, b := a)
    )
    thenHave(thesis) by Tautology.fromLastStep(
        doubleInclusion of (x := aH, y := bH)
    )
  }

  val rightCosetEqualityTheorem = Theorem(
  (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))
    |- rightCoset(H)(op)(a) === rightCoset(H)(op)(b)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b))

    val Ha = rightCoset(H)(op)(a)
    val Hb = rightCoset(H)(op)(b)

    val _7 = have(b ∈ Ha) by Tautology.from(
        rightCosetMembershipEquivalence
    )

    have(Ha ⊆ Hb /\ Hb ⊆ Ha) by Tautology.from(
        _7,
        rightCosetSubsetFromMembership,
        rightCosetSubsetFromMembership of (a := b, b := a)
    )
    thenHave(thesis) by Tautology.fromLastStep(
        doubleInclusion of (x := Ha, y := Hb)
    )
  }

  val cosetContainsRepresentative = Theorem(
    (group(G)(op), subgroup(H)(G)(op), x ∈ G)
    |- x ∈ leftCoset(x)(op)(H) /\ x ∈ rightCoset(H)(op)(x)
  ) {
    val e0 = identityOf(H)(op)
    have(thesis) by Tautology.from(
        leftCosetMembershipTest of (a := x, b := x, h := e0),
        rightCosetMembershipTest of (a := x, b := x, h := e0),
        identityOfIsIdentity of (G := H),
        group.definition, subgroup.definition,
        identityProperty of (e := e0, x := x),
        isIdentityElement.definition of (x := e0),
        isIdentityElement.definition of (x := e0, G := H),
        groupHasTheSameIdentityAsSubgroup of (e := e0)
    )
  }

  val leftCosetEqualityCondition = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    |- (leftCoset(a)(op)(H) === leftCoset(b)(op)(H)) <=> 
        (op(inverseOf(G)(op)(b))(a) ∈ H)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    val aH = leftCoset(a)(op)(H)
    val bH = leftCoset(b)(op)(H)
    val bi = inverseOf(G)(op)(b)

    val _1 = have((aH === bH) <=> ∀(z, z ∈ aH <=> z ∈ bH)) by Tautology.from(
        extensionalityAxiom of (x := aH, y := bH)
    )
    val _2 = have(a ∈ aH) by Tautology.from(
        cosetContainsRepresentative of (x := a)
    )

    val leftImplies = have(aH === bH |- op(bi)(a) ∈ H) subproof {
        assume(aH === bH)
        have(∀(z, z ∈ aH <=> z ∈ bH)) by Tautology.from(_1)
        thenHave(a ∈ aH <=> a ∈ bH) by InstantiateForall(a)
        thenHave(a ∈ bH) by Tautology.fromLastStep(_2)
        thenHave(∃(h ∈ H, a === op(b)(h))) by Tautology.fromLastStep(leftCosetMembership)
        val auxP = lambda(h, h ∈ H /\ (a === op(b)(h)))
        val h0 = ε(x, auxP(x))
        thenHave(h0 ∈ H /\ (a === op(b)(h0))) by Tautology.fromLastStep(
            Quantifiers.existsEpsilon of (P := auxP)
        )
        val _1a = thenHave((op(bi)(a) === h0) /\ h0 ∈ H) by Tautology.fromLastStep(
            applyInverseLeft of (x := a, y := b, z := h0),
            elementInSubgroupMeansItsInGroup of (x := h0)
        )
        val _1b = have(op(bi)(a) === h0 |- (op(bi)(a) === op(bi)(a)) /\ op(bi)(a) ∈ H) by Substitution.Apply(op(bi)(a) === h0)(_1a)
        have(thesis) by Tautology.from(_1a, _1b)
    }

    val rightImplies = have(op(bi)(a) ∈ H |- aH === bH) subproof {
        val h0 = op(bi)(a)
        assume(h0 ∈ H)
        val bii = inverseOf(G)(op)(bi)
        val biinG = have(bi ∈ G) by Tautology.from(
            inverseStaysInGroup of (x := b)
        )
        val h0inG = have(h0 ∈ G) by Tautology.from(
            elementInSubgroupMeansItsInGroup of (x := h0)
        )
        have(h0 === op(bi)(a)) by Tautology
        val _2a = thenHave(op(bii)(h0) === a) by Tautology.fromLastStep(
            applyInverseLeft of (x := h0, y := bi, z := a),
            biinG, h0inG
        )
        have(op(b)(h0) === a) by Congruence.from(
            _2a,
            doubleInverse of (x := b)
        )
        thenHave(a ∈ bH) by Tautology.fromLastStep(
            leftCosetMembershipTest of (h := h0)
        )
        thenHave(aH === bH) by Tautology.fromLastStep(
            leftCosetEqualityTheorem
        )
    }

    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val leftCosetMapsToRightCoset = Theorem(
    (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ leftCoset(b)(op)(H)) |-
        inverseOf(G)(op)(a) ∈ rightCoset(H)(op)(inverseOf(G)(op)(b))
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    assume(a ∈ leftCoset(b)(op)(H))

    val _1 = have(∃(h ∈ H, a === op(b)(h))) by Tautology.from(
        leftCosetMembership
    )
    val auxP = lambda(h, (h ∈ H) /\ (a === op(b)(h)))
    val h0 = ε(h, auxP(h))

    val _2 = have((h0 ∈ H) /\ (a === op(b)(h0))) by Tautology.from(
        _1,
        Quantifiers.existsEpsilon of (P := auxP)
    )
    val h0inH = thenHave(h0 ∈ H) by Tautology
    val h0inG = have(h0 ∈ G) by Tautology.from(
        subgroup.definition, Subset.membership of (z := h0, x := H, y := G), h0inH
    )
    val inva = inverseOf(G)(op)(a)
    val invb = inverseOf(G)(op)(b)
    val invainG = have(inva ∈ G) by Tautology.from(inverseStaysInGroup of (x := a))
    val invbinG = have(invb ∈ G) by Tautology.from(inverseStaysInGroup of (x := b))

    val _3 = have(op(invb)(a) === h0) by Tautology.from(
        _2,
        applyInverseLeft of (x := a, y := b, z := h0),
        h0inG
    )
    val _4 = thenHave(invb === op(h0)(inva)) by Tautology.fromLastStep(
        applyInverseRight of (x := h0, y := a, z := invb),
        invbinG,
        h0inG
    )
    
    have(inva ∈ rightCoset(H)(op)(invb)) by Tautology.from(
        _4,
        rightCosetMembershipEquivalence of (a := invb, b := inva),
        rightCosetMembershipTest of (a := invb, b := inva, h := h0),
        invainG,
        invbinG,
        h0inH
    )
  }

  val rightCosetMapsToLeftCoset = Theorem(
  (group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G, a ∈ rightCoset(H)(op)(b)) |-
    inverseOf(G)(op)(a) ∈ leftCoset(inverseOf(G)(op)(b))(op)(H)
  ) {
    assume(group(G)(op), subgroup(H)(G)(op), a ∈ G, b ∈ G)
    assume(a ∈ rightCoset(H)(op)(b))

    val _1 = have(∃(h ∈ H, a === op(h)(b))) by Tautology.from(
        rightCosetMembership
    )
    val auxP = lambda(h, (h ∈ H) /\ (a === op(h)(b)))
    val h0 = ε(h, auxP(h))

    val _2 = have((h0 ∈ H) /\ (a === op(h0)(b))) by Tautology.from(
        _1,
        Quantifiers.existsEpsilon of (P := auxP)
    )
    val h0inH = thenHave(h0 ∈ H) by Tautology
    val h0inG = have(h0 ∈ G) by Tautology.from(
        subgroup.definition,
        Subset.membership of (z := h0, x := H, y := G),
        h0inH
    )

    val inva = inverseOf(G)(op)(a)
    val invb = inverseOf(G)(op)(b)
    val invainG = have(inva ∈ G) by Tautology.from(
        inverseStaysInGroup of (x := a)
    )
    val invbinG = have(invb ∈ G) by Tautology.from(
        inverseStaysInGroup of (x := b)
    )

    val _3 = have(op(a)(invb) === h0) by Tautology.from(
        _2,
        applyInverseRight of (x := a, y := b, z := h0),
        h0inG
    )
    val _4 = thenHave(invb === op(inva)(h0)) by Tautology.fromLastStep(
        applyInverseLeft of (x := h0, y := a, z := invb),
        invbinG,
        h0inG
    )

    have(inva ∈ leftCoset(invb)(op)(H)) by Tautology.from(
        _4,
        leftCosetMembershipEquivalence of (a := invb, b := inva),
        leftCosetMembershipTest of (a := invb, b := inva, h := h0),
        invainG,
        invbinG,
        h0inH
    )
  }