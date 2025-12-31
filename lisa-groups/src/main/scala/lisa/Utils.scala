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
import lisa.maths.GroupTheory.Groups.*

import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween, functionOn}
import lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.BasicTheorems.*
import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Relations.Predef.{_, given}
import lisa.maths.Quantifiers.∃!

object Utils extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val p = variable[Prop]
  val Q = variable[Ind >>: Prop]
  val R = variable[Ind >>: Ind >>: Prop]

  val equalityTransitivity = Lemma((x === y, y === z) |- x === z) {
    have(thesis) by Congruence
  }

  val equalitySetMembership = Theorem((A === B, x ∈ A) |- x ∈ B) {
    assume(A === B, x ∈ A)
    val _1 = have(x ∈ A) by Restate
    have(B === A |- x ∈ B) by Substitution.Apply(B === A)(_1)
    thenHave(thesis) by Tautology
  }

  val equalitySetMembership2 = Theorem((x ∈ A, x === y) |- y ∈ A) {
    assume(x === y, x ∈ A)
    val _1 = have(x ∈ A) by Restate
    have(y === x |- y ∈ A) by Substitution.Apply(y === x)(_1)
    thenHave(thesis) by Tautology
  }

  val equalitySetMembership3 = Theorem((A === B) |- x ∈ A <=> x ∈ B) {
    have(thesis) by Tautology.from(
      equalitySetMembership,
      equalitySetMembership of (A := B, B := A)
    )
  }

  val equivalenceSubstitutionExists = Theorem(∀(x, P(x) <=> Q(x)) |- ∃(x, P(x)) <=> ∃(x, Q(x))) {
    have(thesis) by Tableau
  }

  val equivalenceSubstitutionExistsOne = Theorem(∀(x, P(x) <=> Q(x)) |- ∃!(x, P(x)) <=> ∃!(x, Q(x))) {
    assume(∀(x, P(x) <=> Q(x)))
    val _1 = have(∃!(x, P(x)) <=> ∃(x, P(x) /\ ∀(y, P(y) ==> (y === x)))) by Tautology.from(
      ∃!.definition
    )
    val _2 = have(∃!(x, Q(x)) <=> ∃(x, Q(x) /\ ∀(y, Q(y) ==> (y === x)))) by Tautology.from(
      ∃!.definition of (P := Q)
    )
    have(∀(x, P(x) <=> Q(x))) by Restate
    thenHave(P(y) <=> Q(y)) by InstantiateForall(y)
    thenHave((P(y) ==> (y === x)) <=> (Q(y) ==> (y === x))) by Tautology
    thenHave(∀(y, (P(y) ==> (y === x)) <=> (Q(y) ==> (y === x)))) by RightForall
    val _3 = thenHave(∀(y, (P(y) ==> (y === x))) <=> ∀(y, Q(y) ==> (y === x))) by Tableau

    have(∀(x, P(x) <=> Q(x))) by Restate
    thenHave(P(x) <=> Q(x)) by InstantiateForall(x)
    thenHave((P(x) /\ ∀(y, P(y) ==> (y === x))) <=> (Q(x) /\ ∀(y, Q(y) ==> (y === x)))) by Tautology.fromLastStep(_3)
    thenHave(∀(x, (P(x) /\ ∀(y, P(y) ==> (y === x))) <=> (Q(x) /\ ∀(y, Q(y) ==> (y === x))))) by RightForall
    val _4 = thenHave(∃(x, P(x) /\ ∀(y, P(y) ==> (y === x))) <=> ∃(x, Q(x) /\ ∀(y, Q(y) ==> (y === x)))) by Tableau

    have(thesis) by Tautology.from(_1, _2, _4)
  }

  val equivalenceSubstitutionForall = Theorem(∀(x, P(x) <=> Q(x)) |- ∀(x, P(x)) <=> ∀(x, Q(x))) {
    have(thesis) by Tableau
  }

  val equivalenceIntroduceExists = Theorem((∃(x, P(x)) /\ p) <=> ∃(x, P(x) /\ p)) {
    have(thesis) by Tableau
  }

  val swapExists = Theorem(∃(a ∈ A, ∃(b, (R(a)(b)))) <=> ∃(b, ∃(a ∈ A, (R(a)(b))))) {
    have(thesis) by Tableau
  }

  val existsMembershipSet = Theorem(x ∈ A <=> ∃(B, (A === B) /\ x ∈ B)) {
    val leftImplies = have(x ∈ A |- ∃(B, (A === B) /\ x ∈ B)) subproof {
      have(x ∈ A |- (A === A) /\ x ∈ A) by Tautology
      thenHave(thesis) by RightExists
    }
    val rightImplies = have(∃(B, (A === B) /\ x ∈ B) |- x ∈ A) subproof {
      assume(∃(B, (A === B) /\ x ∈ B))
      val auxP = lambda(B, (A === B) /\ x ∈ B)
      val B0 = ε(B, auxP(B))
      have((A === B0) /\ x ∈ B0) by Tautology.from(Quantifiers.existsEpsilon of (x := B, P := auxP))
      thenHave(thesis) by Tautology.fromLastStep(equalitySetMembership of (A := B0, B := A))
    }
    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val doubleSetMembership = Theorem(
    (x ∈ ⋃ { { op(a, *, b) | a ∈ A } | b ∈ B }) <=> ∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))
  ) {
    val SS = { { op(a, *, b) | a ∈ A } | b ∈ B }
    val LHS = ⋃(SS)
    val RHS = ∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))
    val _1 = have((x ∈ LHS) <=> ∃(y ∈ SS, x ∈ y)) by Tautology.from(
      unionAxiom of (x := SS, y := y, z := x)
    )
    val _2 = have(y ∈ SS <=> ∃(b ∈ B, y === { op(a, *, b) | a ∈ A })) by Tautology.from(
      Replacement.membership of (x := b, A := B, y := y, F := lambda(b, { op(a, *, b) | a ∈ A }))
    )
    val leftImplies = have(x ∈ LHS |- RHS) subproof {
      assume(x ∈ LHS)
      val _3 = have(∃(y, y ∈ SS /\ x ∈ y)) by Tautology.from(_1)
      val auxP = lambda(y, y ∈ SS /\ x ∈ y)
      val y0 = ε(y, y ∈ SS /\ x ∈ y)
      val _4 = have(auxP(y0)) by Tautology.from(
        _3,
        Quantifiers.existsEpsilon of (x := y, P := auxP)
      )

      val _5 = have(∃(b ∈ B, y0 === { op(a, *, b) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
        _2 of (y := y0),
        _4
      )

      val auxP2 = lambda(b, b ∈ B /\ (y0 === { op(a, *, b) | a ∈ A }))
      val b0 = ε(b, auxP2(b))
      val _6 = have(b0 ∈ B /\ (y0 === { op(a, *, b0) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
        _5,
        Quantifiers.existsEpsilon of (x := b, P := auxP2)
      )

      val _7 = have(b0 ∈ B /\ x ∈ { op(a, *, b0) | a ∈ A }) by Tautology.from(
        _6,
        equalitySetMembership of (x := x, A := y0, B := { op(a, *, b0) | a ∈ A })
      )
      val _8 = have(b0 ∈ B /\ ∃(a ∈ A, x === op(a, *, b0))) by Tautology.from(
        _7,
        Replacement.membership of (x := a, A := A, y := x, F := lambda(a, op(a, *, b0)))
      )
      thenHave(thesis) by RightExists
    }
    val rightImplies = have(RHS |- x ∈ LHS) subproof {
      val subst = y ∈ SS <=> ∃(b ∈ B, y === { op(a, *, b) | a ∈ A })
      val auxP = lambda(y, y ∈ SS /\ x ∈ y)
      val auxQ = lambda(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)
      val _3 = have(auxP(y) <=> auxQ(y)) by Tautology.from(_2)
      val _4 = thenHave(∀(y, auxP(y) <=> auxQ(y))) by RightForall

      val _5 = have(∃(y, auxP(y)) <=> ∃(y, auxQ(y))) by Tautology.from(
        _4,
        equivalenceSubstitutionExists of (x := y, P := auxP, Q := auxQ)
      )
      val _6 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
        _1,
        _5
      )

      val _7 = have(∃(a ∈ A, x === op(a, *, b)) <=> (x ∈ { op(a, *, b) | a ∈ A })) by Tautology.from(
        Replacement.membership of (x := a, y := x, A := A, F := lambda(a, op(a, *, b)))
      )
      val _7b = thenHave((b ∈ B /\ ∃(a ∈ A, x === op(a, *, b))) <=> ((b ∈ B) /\ (x ∈ { op(a, *, b) | a ∈ A }))) by Tautology
      val _8 = thenHave(∀(b, (b ∈ B /\ ∃(a ∈ A, x === op(a, *, b))) <=> ((b ∈ B) /\ (x ∈ { op(a, *, b) | a ∈ A })))) by RightForall
      val _9 = have(RHS <=> ∃(b ∈ B, x ∈ { op(a, *, b) | a ∈ A })) by Tautology.from(
        _8,
        equivalenceSubstitutionExists of (
          x := b,
          P := lambda(b, (b ∈ B /\ ∃(a ∈ A, x === op(a, *, b)))),
          Q := lambda(b, ((b ∈ B) /\ (x ∈ { op(a, *, b) | a ∈ A })))
        )
      )

      val _10 = have((∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
        equivalenceIntroduceExists of (x := b, p := x ∈ y, P := lambda(b, (b ∈ B) /\ (y === { op(a, *, b) | a ∈ A })))
      )
      val _11 = thenHave(∀(y, (∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by RightForall
      val _12 = have(∃(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
        _11,
        equivalenceSubstitutionExists of (
          x := y,
          P := lambda(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y),
          Q := lambda(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))
        )
      )
      val _13 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
        _6,
        _12
      )

      assume(∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))) // RHS
      val _14 = have(((y === { op(a, *, b) | a ∈ A }) /\ (x ∈ y)) |- x ∈ { op(a, *, b) | a ∈ A }) by Tautology.from(
        equalitySetMembership of (A := y, B := { op(a, *, b) | a ∈ A }, x := x)
      )

      val _15 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(_6, _12)
      val R = lambda(a, lambda(b, x ∈ { op(a, *, b) | a ∈ A }))
      val _16 = have(∃(b ∈ B, x ∈ { op(a, *, b) | a ∈ A })) by Tautology.from(_9)

      val _17 = have((x ∈ { op(a, *, b) | a ∈ A }) <=> (∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
        existsMembershipSet of (A := { op(a, *, b) | a ∈ A }, B := y)
      )
      thenHave((b ∈ B /\ x ∈ { op(a, *, b) | a ∈ A }) <=> (b ∈ B /\ ∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology
      val _18 = thenHave(∀(b, (b ∈ B /\ x ∈ { op(a, *, b) | a ∈ A }) <=> (b ∈ B /\ ∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)))) by RightForall
      val _19 = have(∃(b ∈ B, x ∈ { op(a, *, b) | a ∈ A }) <=> ∃(b ∈ B, ∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
        _18,
        equivalenceSubstitutionExists of (
          x := b,
          P := lambda(b, b ∈ B /\ x ∈ { op(a, *, b) | a ∈ A }),
          Q := lambda(b, b ∈ B /\ ∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))
        )
      )
      val _20 = have(∃(b ∈ B, ∃(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(_16, _19)
      val _21 = have(∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
        _20,
        swapExists of (a := b, A := B, b := y, Utils.R := lambda(b, lambda(y, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)))
      )
      have(thesis) by Tautology.from(_21, _15)
    }

    have(thesis) by Tautology.from(
      leftImplies,
      rightImplies
    )
  }

  val opSubstitution = Theorem(
    (x === op(a, *, b), a === c, b === d) |- (x === op(c, *, d))
  ) {
    have(thesis) by Congruence
  }

  val doubleSetMembership2 = Theorem(
    (x ∈ { op(fst(z), *, snd(z)) | z ∈ (A × B) }) <=> ∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))
  ) {
    val S = { op(fst(z), *, snd(z)) | z ∈ (A × B) }
    val leftImplies = have(x ∈ S |- ∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))) subproof {
      assume(x ∈ S)
      val _1 = have(∃(z ∈ (A × B), x === op(fst(z), *, snd(z)))) by Tautology.from(
        Replacement.membership of (y := x, x := z, A := (A × B), F := lambda(z, op(fst(z), *, snd(z))))
      )
      val auxP = lambda(z, z ∈ (A × B) /\ (x === op(fst(z), *, snd(z))))
      val z0 = ε(z, auxP(z))

      val _2 = have(auxP(z0)) by Tautology.from(_1, Quantifiers.existsEpsilon of (x := z, P := auxP))
      val a0 = fst(z0)
      val b0 = snd(z0)
      val _3 = have(a0 ∈ A /\ b0 ∈ B) by Tautology.from(
        _2,
        CartesianProduct.fstMembership of (z := z0),
        CartesianProduct.sndMembership of (z := z0)
      )
      have(a0 ∈ A /\ (x === op(a0, *, b0))) by Tautology.from(_3, _2)
      thenHave(∃(a ∈ A, x === op(a, *, b0))) by RightExists
      thenHave(b0 ∈ B /\ ∃(a ∈ A, x === op(a, *, b0))) by Tautology.fromLastStep(_3)
      thenHave(thesis) by RightExists
    }
    val rightImplies = have(∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b))) |- x ∈ S) subproof {
      assume(∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b))))
      val auxP1 = lambda(b, b ∈ B /\ ∃(a ∈ A, x === op(a, *, b)))
      val b0 = ε(b, auxP1(b))
      val _1 = have(auxP1(b0)) by Tautology.from(Quantifiers.existsEpsilon of (x := b, P := auxP1))
      thenHave(∃(a ∈ A, x === op(a, *, b0))) by Tautology

      val auxP2 = lambda(a, a ∈ A /\ (x === op(a, *, b0)))
      val a0 = ε(a, auxP2(a))
      val _2 = thenHave(auxP2(a0)) by Tautology.fromLastStep(Quantifiers.existsEpsilon of (x := a, P := auxP2))

      val z0 = (a0, b0)
      val _3 = have(z0 ∈ (A × B)) by Tautology.from(_1, _2, CartesianProduct.pairMembership of (x := a0, y := b0))

      val _4 = have((fst(z0) === a0) /\ (snd(z0) === b0)) by Tautology.from(
        Pair.pairFst of (x := a0, y := b0),
        Pair.pairSnd of (x := a0, y := b0)
      )
      val _5 = have(x === op(fst(z0), *, snd(z0))) by Tautology.from(
        opSubstitution of (x := x, a := a0, b := b0, c := fst(z0), d := snd(z0)),
        _2,
        _4
      )
      val auxF = lambda(z, op(fst(z), *, snd(z)))
      have(auxF(z0) ∈ S) by Tautology.from(
        Replacement.map of (A := (A × B), x := z0, F := auxF),
        _3
      )
      thenHave(thesis) by Tautology.fromLastStep(
        equalitySetMembership2 of (y := x, x := auxF(z0), A := S),
        _5
      )
    }
    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val restrictedAppTheorem = Theorem(
    ((f ↾ A) :: A -> B, x ∈ A) |- (app(f)(x) === app(f ↾ A)(x))
  ) {
    assume((f ↾ A) :: A -> B, x ∈ A)
    val fA = (f ↾ A)
    val _1 = have((app(fA)(x) === y) <=> (x, y) ∈ fA) by Tautology.from(
      functionBetweenIsFunction of (f := fA),
      functionBetweenDomain of (f := fA),
      equalitySetMembership of (x := x, A := A, B := dom(fA)),
      appDefinition of (f := fA)
    )

    val _2 = have(((x, y) ∈ fA) <=> ((x, y) ∈ f)) by Tautology.from(
      Restriction.pairMembership
    )
    val auxP = lambda(y, (x, y) ∈ fA)
    val auxQ = lambda(y, (x, y) ∈ f)
    val _3 = thenHave(∀(y, auxP(y) <=> auxQ(y))) by RightForall
    val fAx = app(fA)(x)
    val _4 = have((x, fAx) ∈ f) by Tautology.from(
      _1 of (y := fAx),
      _2 of (y := fAx)
    )

    have(∀(x ∈ A, ∃!(y, (x, y) ∈ fA))) by Tautology.from(
      functionBetween.definition of (f := fA)
    )
    thenHave(x ∈ A ==> ∃!(y, (x, y) ∈ fA)) by InstantiateForall(x)
    val _5 = thenHave(∃!(y, (x, y) ∈ fA)) by Tautology
    val _6 = have(∃!(y, (x, y) ∈ f)) by Tautology.from(
      _3,
      _5,
      equivalenceSubstitutionExistsOne of (x := y, P := auxP, Q := auxQ)
    )

    val _7a = have(auxQ(y) <=> (y === ε(z, auxQ(z)))) by Tautology.from(
      _4,
      _6,
      Quantifiers.existsOneEpsilonUniqueness of (x := z, P := auxQ)
    )
    val _7 = have(fAx === ε(z, auxQ(z))) by Tautology.from(
      _4,
      _7a of (y := fAx)
    )

    val _8 = have(app(f)(x) === ε(z, auxQ(z))) by Tautology.from(app.definition of (y := z))
    have(thesis) by Congruence.from(_7, _8)
  }

  val functionAppLemma = Theorem(
    (f :: A -> C, ∀(x ∈ A, app(f)(x) ∈ B))
      |- f ⊆ (A × B)
  ) {
    assume(f :: A -> C, ∀(x ∈ A, app(f)(x) ∈ B))
    val functionf = have(function(f)) by Tautology.from(functionBetweenIsFunction of (B := C))
    val subst = have(dom(f) === A) by Tautology.from(functionBetweenDomain of (B := C))
    have(x ∈ dom(f) |- (app(f)(x) === y) <=> (x, y) ∈ f) by Tautology.from(
      appDefinition,
      functionf
    )
    val _1 = thenHave(x ∈ A |- (app(f)(x) === y) <=> (x, y) ∈ f) by Substitute(subst)
    val _2 = have(z ∈ f |- z === (fst(z), snd(z))) by Tautology.from(
      inversion,
      functionf
    )

    have(∀(x ∈ A, app(f)(x) ∈ B)) by Restate
    val _3 = thenHave(x ∈ A |- app(f)(x) ∈ B) by InstantiateForall(x)

    have(z ∈ f |- z ∈ (A × B)) subproof {
      assume(z ∈ f)
      val x0 = fst(z)
      val y0 = snd(z)
      val z0 = (x0, y0)
      val step1 = have(z === (x0, y0)) by Tautology.from(_2)
      have(z ∈ f) by Restate
      val step2 = thenHave(z0 ∈ f) by Substitute(step1)
      val step3 = have(x0 ∈ dom(f)) by Tautology.from(step2, domainMembership of (x := x0, y := y0), functionf)
      val step4 = thenHave(x0 ∈ A) by Substitute(subst)

      val step5 = have(app(f)(x0) === y0) by Tautology.from(
        step2,
        step4,
        _1 of (x := x0, y := y0)
      )
      have(app(f)(x0) ∈ B) by Tautology.from(_3 of (x := x0), step4)
      val step6 = thenHave(y0 ∈ B) by Substitute(step5)
      val step7 = have(z0 ∈ (A × B)) by Tautology.from(
        step4,
        step6,
        CartesianProduct.pairMembership of (x := x0, y := y0)
      )
      thenHave(thesis) by Substitute(step1)
    }
    thenHave((z ∈ f) ==> (z ∈ (A × B))) by Restate
    thenHave(∀(z ∈ f, z ∈ (A × B))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      subsetAxiom of (x := f, y := (A × B))
    )
  }

  val functionBetweenTest = Theorem(
    (function(f), dom(f) === A, range(f) ⊆ B) |- f :: A -> B
  ) {
    assume(function(f), dom(f) === A, range(f) ⊆ B)
    val _1 = have(functionOn(f)(A)) by Tautology.from(functionOnIffFunctionWithDomain)

    val auxP = lambda(B, functionBetween(f)(A)(B))
    val B0 = ε(B, auxP(B))
    have(∃(B, auxP(B))) by Tautology.from(_1, functionOn.definition)
    val _4 = thenHave(f :: A -> B0) by Tautology.fromLastStep(
      Quantifiers.existsEpsilon of (x := B, P := auxP)
    )
    val _5 = have(relationBetween(f)(A)(B0) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(
      _4,
      functionBetween.definition of (f := f, B := B0)
    )

    have(x ∈ A |- app(f)(x) ∈ B) subproof {
      assume(x ∈ A)
      val subst = have(dom(f) === A) by Restate
      have(x ∈ A) by Restate
      val step1 = thenHave(x ∈ dom(f)) by Substitute(subst)
      val step2 = have(app(f)(x) ∈ range(f)) by Tautology.from(
        appInRange,
        step1
      )
      have(∀(y, y ∈ range(f) ==> y ∈ B)) by Tautology.from(
        subsetAxiom of (z := y, x := range(f), y := B)
      )
      val step3 = thenHave(app(f)(x) ∈ range(f) ==> app(f)(x) ∈ B) by InstantiateForall(app(f)(x))
      have(thesis) by Tautology.from(step2, step3)
    }
    thenHave(x ∈ A ==> app(f)(x) ∈ B) by Restate
    val _6 = thenHave(∀(x ∈ A, app(f)(x) ∈ B)) by RightForall
    val _7 = have(f ⊆ (A × B)) by Tautology.from(
      _4,
      _6,
      functionAppLemma of (C := B0)
    )
    val _8 = have(relationBetween(f)(A)(B)) by Tautology.from(
      _7,
      relationBetween.definition of (Relation.R := f, X := A, Y := B)
    )
    have(thesis) by Tautology.from(
      _5,
      _8,
      functionBetween.definition
    )
  }

  val restrictionRange = Theorem(
    (function(f)) |- range(f ↾ A) ⊆ range(f)
  ) {
    assume(function(f))
    have((f ↾ A) ⊆ f) by Tautology.from(Restriction.isSubset)
    thenHave(range(f ↾ A) ⊆ range(f)) by Tautology.fromLastStep(
      rangeMonotonic of (g := (f ↾ A))
    )
  }

  val restrictionDomain = Theorem(
    dom(f ↾ A) === (dom(f) ∩ A)
  ) {
    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition of (Relation.R := f))

    have(∀(z, z ∈ (f ↾ A) <=> (z ∈ f) /\ (fst(z) ∈ A))) by RightForall(Restriction.membership)
    val xdom = have(x ∈ dom(f ↾ A) <=> ∃(z ∈ f, fst(z) ∈ A /\ (fst(z) === x))) by Tableau.from(
      lastStep,
      `x ∈ dom(f)` of (f := f ↾ A)
    )

    val `==>` = have(x ∈ dom(f ↾ A) |- x ∈ (dom(f) ∩ A)) subproof {
      assume(x ∈ dom(f ↾ A))
      val _1 = have(∃(z ∈ f, fst(z) ∈ A /\ (fst(z) === x))) by Tautology.from(xdom)
      val auxP = lambda(z, z ∈ f /\ fst(z) ∈ A /\ (fst(z) === x))
      val z0 = ε(z, auxP(z))
      val _2 = have(z0 ∈ f /\ fst(z0) ∈ A /\ (fst(z0) === x)) by Tautology.from(
        _1,
        Quantifiers.existsEpsilon of (x := z, P := auxP)
      )
      val _3 = have(x ∈ A) by Tautology.from(
        _2,
        equalitySetMembership2 of (x := fst(z0), y := x, A := A)
      )
      have(z0 ∈ f /\ (fst(z0) === x)) by Tautology.from(_2)
      val _4 = thenHave(∃(z ∈ f, fst(z) === x)) by RightExists
      val _5 = have(x ∈ dom(f)) by Tautology.from(
        _4,
        `x ∈ dom(f)`
      )
      have(thesis) by Tautology.from(
        _3,
        _5,
        Intersection.membership of (z := x, x := dom(f), y := A)
      )
    }
    val `<==` = have(x ∈ (dom(f) ∩ A) |- x ∈ dom(f ↾ A)) subproof {
      assume(x ∈ (dom(f) ∩ A))
      val _1 = have(x ∈ dom(f) /\ x ∈ A) by Tautology.from(Intersection.membership of (z := x, x := dom(f), y := A))
      val _2 = have(∃(z ∈ f, fst(z) === x)) by Tautology.from(_1, `x ∈ dom(f)`)
      val auxP = lambda(z, z ∈ f /\ (fst(z) === x))
      val z0 = ε(z, auxP(z))
      val _3 = have(auxP(z0)) by Tautology.from(_2, Quantifiers.existsEpsilon of (x := z, P := auxP))
      val subst = have(fst(z0) === x) by Tautology.from(_3)
      have(x ∈ A) by Tautology.from(_1)
      val _4 = thenHave(fst(z0) ∈ A) by Substitute(subst)
      have(z0 ∈ f /\ fst(z0) ∈ A /\ (fst(z0) === x)) by Tautology.from(_3, _4)
      thenHave(∃(z, z ∈ f /\ fst(z) ∈ A /\ (fst(z) === x))) by RightExists
      thenHave(thesis) by Tautology.fromLastStep(xdom)
    }
    have((x ∈ dom(f ↾ A)) <=> (x ∈ (dom(f) ∩ A))) by Tautology.from(`==>`, `<==`)
    thenHave(∀(x, (x ∈ dom(f ↾ A)) <=> (x ∈ (dom(f) ∩ A)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      extensionalityAxiom of (z := x, x := dom(f ↾ A), y := (dom(f) ∩ A))
    )
  }

  val restrictedAppTheorem2 = Theorem(
    ((f ↾ A) :: A -> C, B ⊆ A) |- (f ↾ B) :: B -> C
  ) {
    assume((f ↾ A) :: A -> C, B ⊆ A)
    val fA = (f ↾ A)
    val _1 = have(relationBetween(fA)(A)(C) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ fA))) by Tautology.from(
      functionBetween.definition of (f := fA, B := C)
    )
    val fB = (f ↾ B)
    val fAB = ((f ↾ A) ↾ B)
    val BAeq = have((B ∩ A) === B) by Tautology.from(Intersection.ofSubsets of (x := B, y := A))
    val ABeq = have((A ∩ B) === B) by Congruence.from(BAeq, Intersection.commutativity of (x := B, y := A))
    have(fAB === (f ↾ (A ∩ B))) by Tautology.from(Restriction.doubleRestriction)
    val fABeq = thenHave(fAB === fB) by Substitute(ABeq)

    val functionfA = have(function(fA)) by Tautology.from(functionBetweenIsFunction of (f := fA, B := C))
    val domfA = have(dom(fA) === A) by Tautology.from(functionBetweenDomain of (f := fA, B := C))

    have(function(fAB)) by Tautology.from(Restriction.isFunction of (f := fA, A := B), functionfA)
    val _2 = thenHave(function(fB)) by Substitute(fABeq)

    have(dom(fAB) === (dom(fA) ∩ B)) by Tautology.from(restrictionDomain of (f := fA, A := B))
    thenHave(dom(fB) === (dom(fA) ∩ B)) by Substitute(fABeq)
    thenHave(dom(fB) === (A ∩ B)) by Substitute(domfA)
    val _3 = thenHave(dom(fB) === B) by Substitute(ABeq)

    have(range(fAB) ⊆ range(fA)) by Tautology.from(
      restrictionRange of (f := fA, A := B),
      functionfA
    )
    val _4 = thenHave(range(fB) ⊆ range(fA)) by Substitute(fABeq)
    have(range(fA) ⊆ C) by Tautology.from(
      functionBetweenRange of (f := fA, B := C)
    )
    val _5 = thenHave(range(fB) ⊆ C) by Tautology.fromLastStep(
      _4,
      Subset.transitivity of (x := range(fB), y := range(fA), z := C)
    )

    have(thesis) by Tautology.from(
      _2,
      _3,
      _5,
      functionBetweenTest of (f := fB, A := B, B := C)
    )
  }

  val restrictedAppTheorem3 = Theorem(
    (f :: A -> C, ∀(x ∈ A, app(f)(x) ∈ B)) |- f :: A -> B
  ) {
    assume(f :: A -> C, ∀(x ∈ A, app(f)(x) ∈ B))
    val _1 = have(relationBetween(f)(A)(C) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(
      functionBetween.definition of (B := C)
    )
    val _2 = have(relationBetween(f)(A)(B)) by Tautology.from(
      functionAppLemma,
      relationBetween.definition of (Relation.R := f, X := A, Y := B)
    )
    have(thesis) by Tautology.from(
      _1,
      _2,
      functionBetween.definition
    )
  }

  val functionBuilder = Theorem(
    (f === { (x, F(x)) | x ∈ A }) |- functionOn(f)(A) /\ ∀(x ∈ A, app(f)(x) === F(x))
  ) {
    assume(f === { (x, F(x)) | x ∈ A })
    val subst = have(f === { (x, F(x)) | x ∈ A }) by Restate

    have(z ∈ { (x, F(x)) | x ∈ A } <=> ∃(a ∈ A, z === (a, F(a)))) by Replacement.apply
    val _1 = thenHave(z ∈ f <=> ∃(a ∈ A, z === (a, F(a)))) by Substitute(subst)
    val B0 = { F(x) | x ∈ A }

    have(z ∈ f |- z ∈ (A × B0)) subproof {
      assume(z ∈ f)
      val _a1 = have(∃(a ∈ A, z === (a, F(a)))) by Tautology.from(_1)
      val auxP = lambda(a, a ∈ A /\ (z === (a, F(a))))
      val a0 = ε(a, auxP(a))
      val _a2 = have(a0 ∈ A /\ (z === (a0, F(a0)))) by Tautology.from(_a1, Quantifiers.existsEpsilon of (x := a, P := auxP))
      val subst = thenHave(z === (a0, F(a0))) by Tautology
      val _a3 = have(F(a0) ∈ B0) by Tautology.from(_a2, Replacement.map of (x := a0))
      val _a4 = have((a0, F(a0)) ∈ (A × B0)) by Tautology.from(_a2, _a3, CartesianProduct.pairMembership of (x := a0, y := F(a0), B := B0))
      thenHave(thesis) by Substitute(subst)
    }
    thenHave(z ∈ f ==> z ∈ (A × B0)) by Restate
    thenHave(∀(z, z ∈ f ==> z ∈ (A × B0))) by RightForall
    thenHave(f ⊆ (A × B0)) by Tautology.fromLastStep(subsetAxiom of (x := f, y := (A × B0)))
    val _2 = thenHave(relationBetween(f)(A)(B0)) by Tautology.fromLastStep(relationBetween.definition of (Relation.R := f, X := A, Y := B0))

    have(x ∈ A |- ∃!(y, (x, y) ∈ f) /\ (app(f)(x) === F(x))) subproof {
      assume(x ∈ A)
      val step1 = have((x, y) ∈ f <=> ∃(a ∈ A, (x, y) === (a, F(a)))) by Tautology.from(_1 of (z := (x, y)))
      have(((x, y) === (a, F(a))) <=> ((y === F(a)) /\ (x === a))) by Tautology.from(
        Pair.extensionality of (a := x, b := y, c := a, d := F(a))
      )
      thenHave((a ∈ A /\ ((x, y) === (a, F(a)))) <=> (a ∈ A /\ ((y === F(a)) /\ (x === a)))) by Tautology
      thenHave(∀(a, (a ∈ A /\ ((x, y) === (a, F(a)))) <=> (a ∈ A /\ ((y === F(a)) /\ (x === a))))) by RightForall
      val step2 = thenHave(∃(a, a ∈ A /\ ((x, y) === (a, F(a)))) <=> ∃(a, a ∈ A /\ ((y === F(a)) /\ (x === a)))) by Tautology.fromLastStep(
        equivalenceSubstitutionExists of (
          x := a,
          P := lambda(a, a ∈ A /\ ((x, y) === (a, F(a)))),
          Q := lambda(a, a ∈ A /\ ((y === F(a)) /\ (x === a)))
        )
      )

      val step3 = have((x, y) ∈ f <=> ∃(a, a ∈ A /\ ((y === F(a)) /\ (x === a)))) by Tautology.from(step1, step2)
      val step4 = have((x, y) ∈ f <=> (x ∈ A /\ (y === F(x)))) by Tautology.from(
        step3,
        Quantifiers.onePointRule of (x := a, y := x, P := lambda(a, a ∈ A /\ (y === F(a))))
      )
      val step5 = have((x, y) ∈ f <=> (y === F(x))) by Tautology.from(step4)
      val auxP = lambda(y, (x, y) ∈ f)
      have((auxP(y) /\ auxP(z)) |- y === z) subproof {
        assume(auxP(y), auxP(z))
        val _a = have(y === F(x)) by Tautology.from(step5)
        val _b = have(z === F(x)) by Tautology.from(step5 of (y := z))
        have(thesis) by Congruence.from(_a, _b)
      }
      thenHave((auxP(y) /\ auxP(z)) ==> (y === z)) by Restate
      val step6 = thenHave(∀(y, ∀(z, (auxP(y) /\ auxP(z)) ==> (y === z)))) by Generalize
      val auxpf = have(auxP(F(x))) by Tautology.from(step5 of (y := F(x)))
      val step7 = thenHave(∃(y, auxP(y))) by RightExists
      have(∃!(y, auxP(y))) by Tautology.from(
        step6,
        step7,
        Quantifiers.existsOneAlternativeDefinition of (x := y, y := z, P := auxP)
      )
      val step8 = thenHave(∃!(z, auxP(z))) by Restate
      val step9 = have(auxP(F(x)) <=> (F(x) === ε(z, auxP(z)))) by Tautology.from(
        step8,
        Quantifiers.existsOneEpsilonUniqueness of (x := z, y := F(x), P := auxP)
      )
      val step10 = have(F(x) === ε(z, auxP(z))) by Tautology.from(step9, auxpf)
      thenHave(F(x) === ε(y, (x, y) ∈ f)) by Restate
      val step11 = thenHave(F(x) === app(f)(x)) by Substitute(app.definition)
      have(thesis) by Tautology.from(step8, step11)
    }
    val _3 = thenHave(x ∈ A ==> ((∃!(y, (x, y) ∈ f) /\ (app(f)(x) === F(x))))) by Restate
    val _4a = thenHave(x ∈ A ==> (∃!(y, (x, y) ∈ f))) by Tautology
    val _4 = thenHave(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by RightForall
    val _5a = have(x ∈ A ==> (app(f)(x) === F(x))) by Tautology.from(_3)
    val _5 = thenHave(∀(x ∈ A, (app(f)(x) === F(x)))) by RightForall
    have(f :: A -> B0) by Tautology.from(_2, _4, functionBetween.definition of (B := B0))
    thenHave(thesis) by Tautology.fromLastStep(
      functionBetweenIsFunctionOn of (B := B0),
      _5
    )
  }

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  val functionBetweenRangeMembership = Theorem(
    f :: A -> B |- y ∈ range(f) <=> ∃(x, (x ∈ A) /\ (f(x) === y))
  ) {
    assume(f :: A -> B)
    have(functionOn(f)(A)) by Tautology.from(functionBetweenIsFunctionOn)
    val ff = thenHave(function(f) /\ (dom(f) === A)) by Tautology.fromLastStep(functionOnIffFunctionWithDomain)
    val _1 = have(function(f)) by Tautology.from(ff)
    val _2 = have(dom(f) === A) by Tautology.from(ff)

    val `==>` = have(y ∈ range(f) |- ∃(x, (x ∈ A) /\ (f(x) === y))) subproof {
      assume(y ∈ range(f))
      have(y ∈ range(f)) by Restate
      val step1 = thenHave(y ∈ { snd(z) | z ∈ f }) by Substitute(range.definition of (Relation.R := f))
      val step2 = have(y ∈ { snd(z) | z ∈ f } <=> ∃(z ∈ f, snd(z) === y)) by Replacement.apply
      val auxP = lambda(z, z ∈ f /\ (snd(z) === y))
      val z0 = ε(z, auxP(z))
      val step3 = have(z0 ∈ f /\ (snd(z0) === y)) by Tautology.from(step1, step2, Quantifiers.existsEpsilon of (x := z, P := auxP))
      val eqy = thenHave(snd(z0) === y) by Tautology

      val x0 = fst(z0)
      have(z0 === (fst(z0), snd(z0))) by Tautology.from(_1, step3, inversion of (z := z0))
      val step4 = thenHave(z0 === (x0, y)) by Substitute(eqy)
      have(z0 ∈ f) by Tautology.from(step3)
      val step5 = thenHave((x0, y) ∈ f) by Substitute(step4)
      val step6 = have(x0 ∈ dom(f)) by Tautology.from(step5, domainMembership of (x := x0))
      val step7 = thenHave(x0 ∈ A) by Substitute(_2)
      val step8 = have(f(x0) === y) by Tautology.from(
        _1,
        step5,
        step6,
        appDefinition of (x := x0)
      )

      have(x0 ∈ A /\ (f(x0) === y)) by Tautology.from(step7, step8)
      thenHave(thesis) by RightExists
    }

    val `<==` = have(∃(x, (x ∈ A) /\ (f(x) === y)) |- y ∈ range(f)) subproof {
      assume(∃(x, (x ∈ A) /\ (f(x) === y)))
      val auxP = lambda(x, (x ∈ A) /\ (f(x) === y))
      val x0 = ε(x, auxP(x))

      have(x0 ∈ A /\ (f(x0) === y)) by Tautology.from(Quantifiers.existsEpsilon of (P := auxP))
      thenHave(x0 ∈ dom(f) /\ (f(x0) === y)) by Substitute(_2)
      thenHave((x0, y) ∈ f) by Tautology.fromLastStep(
        _1,
        appDefinition of (x := x0)
      )
      thenHave(y ∈ range(f)) by Tautology.fromLastStep(rangeMembership of (x := x0))
    }

    have(thesis) by Tautology.from(`<==`, `==>`)
  }


  val functionIsBetweenDomAndRange = Theorem(
    function(f) |- f :: dom(f) -> range(f)
    ) {
      assume(function(f))
      val _1 = have(range(f) ⊆ range(f)) by Tautology.from(Subset.reflexivity of (x := range(f)))
      have(f :: dom(f) -> range(f)) by Tautology.from(
        functionBetweenTest of (A := dom(f), B := range(f)),
        _1,
        )
    }

  val functionOnIsFunctionBetweenRange = Theorem(
    functionOn(f)(A) |- f :: A -> range(f)
  ) {
    assume(functionOn(f)(A))
    val _1 = have(function(f)) by Tautology.from(functionOnIsFunction)
    val _2 = have(dom(f) === A) by Tautology.from(functionOnDomain)
    val _3 = have(f :: dom(f) -> range(f)) by Tautology.from(functionIsBetweenDomAndRange, _1)
    val _4 = thenHave(f :: A -> range(f)) by Substitute(_2)
  }


  val alternativeRangeDefinition = Theorem(
    function(f) |- range(f) === { f(x) | x ∈ dom(f) }
  ) {
    assume(function(f))
    val D = dom(f)
    val I = range(f)
    val _1 = have(f :: D -> I) by Tautology.from(functionIsBetweenDomAndRange)
    val _2 = have(relationBetween(f)(D)(I) /\ ∀(x ∈ D, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition of (A := D, B := I), _1)

    val _3 = have( I === {snd(z) | z ∈ f}) by Tautology.from(range.definition of (Relation.R := f))

    val outputSet = { f(x) | x ∈ dom(f) }

    val _dir1 = have(x ∈ range(f) |- x ∈ outputSet) subproof {
      assume(x ∈ range(f))
      val _s1 = have(x ∈ range(f)) by Restate
      val _s2 = thenHave(x ∈ {snd(z) | z ∈ f}) by Substitute(_3)
      val _s3 = have(∃(g ∈ f, snd(g) === x)) by Tautology.from(Replacement.membership of (y:=x,A:=f, F:=lambda(z, snd(z))), _s2)

      val pAux = lambda(g, (g ∈ f) /\ (snd(g) === x))
      val p0 = ε(g, pAux(g))
      val p0Thm = have(pAux(p0)) by Tautology.from(Quantifiers.existsEpsilon of (P:=pAux), _s3)
      val _s4 = have(p0 === (fst(p0), snd(p0))) by Tautology.from(inversion of (z := p0), p0Thm)

      have(p0 ∈ f) by Tautology.from(p0Thm)
      val _s5 = thenHave( (fst(p0), snd(p0)) ∈  f) by Substitute(_s4)
      val _s6 = have(fst(p0) ∈ dom(f)) by Tautology.from(_s5, domainMembership of (x:=fst(p0), y:=snd(p0)))

      val _s7a = have(snd(p0) === x) by Tautology.from(p0Thm)
      val _s7 = have(f(fst(p0)) === snd(p0)) by Tautology.from(
        _s6,           // fst(p0) ∈ dom(f)
        _s4,           // p0 ∈ f (which gives us (fst(p0), snd(p0)) ∈ f after using inversion)
        _s5,           // p0 === (fst(p0), snd(p0))
        appDefinition of (x := fst(p0), y := snd(p0))
      )
      val _s8 = thenHave(f(fst(p0)) === x) by Substitute(_s7a)
      val _s9 = have( (fst(p0) ∈ dom(f)) /\ (f(fst(p0)) === x) ) by Tautology.from(_s8 , _s6)
      val _s10 = thenHave(∃ (y, (y ∈ dom(f)) /\ (f(y) === x) )) by RightExists

      val _g1 = have(∃ (y ∈ dom(f) , f(y) === x)) by Tautology.from(_s10)
      have(thesis) by Tautology.from(_g1 , Replacement.membership of (y:= x, A:=dom(f), F:=lambda(z,f(z))))
    }

    val _dir2 = have(x ∈ outputSet |- x ∈ range(f)) subproof {
      assume(x ∈ outputSet)
      val _s1 = have(∃(y ∈ dom(f), f(y) === x)) by Tautology.from(
        Replacement.membership of (y := x, A := dom(f), F := lambda(z, f(z)))
      )

      val x0Aux = lambda(y, (y ∈ dom(f)) /\ (f(y) === x))
      val x0 = ε(y, x0Aux(y))
      val x0Thm = have(x0Aux(x0)) by Tautology.from(
        Quantifiers.existsEpsilon of (x := y, P := x0Aux),
        _s1
      )
      val _s2 = have((x0, f(x0)) ∈ f) by Tautology.from(
        x0Thm,  // gives you x0 ∈ dom(f) and f(x0) === x
        appDefinition of (x := x0, y := f(x0))
      )

      val _s3a = have(f(x0) === x) by Tautology.from(x0Thm)

      val _s3 = have(f(x0) ∈ range(f)) by Tautology.from(
        _s2,
        rangeMembership of (x := x0, y := f(x0))
      )
      thenHave(x ∈ range(f)) by Substitute(_s3a)
    }
    have(x ∈ range(f) <=> x ∈ outputSet) by Tautology.from(_dir1, _dir2)
    thenHave(thesis) by Extensionality
  }

  val imageInclusion = Theorem(
    (function(f), function(g), ∀(x ∈ dom(f), ∃(y ∈ dom(g), f(x) === g(y))))
      |- range(f) ⊆ range(g)
  ) {
    assume(function(f), function(g), ∀(x ∈ dom(f), ∃(y ∈ dom(g), f(x) === g(y))))
    val _sub1 = have(z ∈ range(f) |- z ∈ range(g)) subproof {
      assume(z ∈ range(f))
      val _1a = have(range(f) === { f(g) | g ∈ dom(f) }) by Tautology.from(alternativeRangeDefinition)
      val _1b = have(z ∈ range(f)) by Restate
      val _1 = thenHave(z ∈ { f(g) | g ∈ dom(f) }) by Substitute(_1a)

      val _2 = have(∃(g ∈ dom(f), f(g) === z)) by Tautology.from(
        Replacement.membership of (y := z, A := dom(f), F := lambda(g, f(g))),
        _1
      )
      val g0Aux = lambda(g, (g ∈ dom(f)) /\ (f(g) === z))
      val g0 = ε(g, g0Aux(g))
      val g0Thm = have(g0Aux(g0)) by Tautology.from(
        Quantifiers.existsEpsilon of (x := g, P := g0Aux),
        _2)

      val _3 = have(∀(x ∈ dom(f), ∃(y ∈ dom(g), f(x) === g(y)))) by Restate
      val _4 = have(∀(x, (x ∈ dom(f) ) ==> ∃(y ∈ dom(g), f(x) === g(y)))) by Tautology.from(_3)
      val _5 = thenHave( (g0 ∈ dom(f) ) ==> ∃(y ∈ dom(g), f(g0) === g(y))) by InstantiateForall(g0)
      val _6 = have(∃(y ∈ dom(g), f(g0) === g(y))) by Tautology.from(_5, g0Thm)

      val _7a = have({ g(y) | y ∈ dom(g) } === range(g)) by Tautology.from(alternativeRangeDefinition of (f := g))
      val _7b = have(f(g0) ∈ { g(y) | y ∈ dom(g) }) by Tautology.from(
        _6, 
        Replacement.membership of (y := f(g0), A := dom(g), F := lambda(y, g(y)))
      )
      val _7 = thenHave(f(g0) ∈ range(g)) by Substitute(_7a)
      val _7c = have(f(g0) === z) by Tautology.from(g0Thm)
      val _8 = have(f(g0) === z |- z ∈ range(g)) by Substitution.Apply(f(g0) === z)(_7)
      have(thesis) by Tautology.from(_8, _7c)
    }
    thenHave(z ∈ range(f) ==> z ∈ range(g)) by Restate
    thenHave(∀(z, z ∈ range(f) ==> z ∈ range(g))) by RightForall
    thenHave(thesis) by Substitute(subsetAxiom of (x := range(f), y := range(g)))
  }

