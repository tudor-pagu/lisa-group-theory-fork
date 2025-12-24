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

import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween}
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
        equalitySetMembership, equalitySetMembership of (A := B, B := A)
    )
  }

  val equivalenceSubstitutionExists = Theorem(∀(x, P(x) <=> Q(x)) |-  ∃(x, P(x)) <=> ∃(x, Q(x))) {
    have(thesis) by Tableau
  }

  val equivalenceSubstitutionExistsOne = Theorem(∀(x, P(x) <=> Q(x)) |-  ∃!(x, P(x)) <=> ∃!(x, Q(x))) {
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

  val equivalenceSubstitutionForall = Theorem(∀(x, P(x) <=> Q(x)) |-  ∀(x, P(x)) <=> ∀(x, Q(x))) {
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
    (x ∈ ⋃{ {op(a, *, b) | a ∈ A} | b ∈ B }) <=> ∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))
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
            _3, Quantifiers.existsEpsilon of (x := y, P := auxP)
        )

        val _5 = have(∃(b ∈ B, y0 === { op(a, *, b) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
            _2 of (y := y0), _4
        )

        val auxP2 = lambda(b, b ∈ B /\ (y0 === { op(a, *, b) | a ∈ A }))
        val b0 = ε(b, auxP2(b))
        val _6 = have(b0 ∈ B /\ (y0 === { op(a, *, b0) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
            _5, Quantifiers.existsEpsilon of (x := b, P := auxP2)
        )

        val _7 = have(b0 ∈ B /\ x ∈ { op(a, *, b0) | a ∈ A }) by Tautology.from(
            _6, equalitySetMembership of (x := x, A := y0, B := { op(a, *, b0) | a ∈ A })
        )
        val _8 = have(b0 ∈ B /\ ∃(a ∈ A, x === op(a, *, b0))) by Tautology.from(
            _7, Replacement.membership of (x := a, A := A, y := x, F := lambda(a, op(a, *, b0)))
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
            _4, equivalenceSubstitutionExists of (x := y, P := auxP, Q := auxQ)
        )
        val _6 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
            _1, _5
        )

        val _7 = have(∃(a ∈ A, x === op(a, *, b)) <=> (x ∈ {op(a, *, b) | a ∈ A})) by Tautology.from(
            Replacement.membership of (x := a, y := x, A := A, F := lambda(a, op(a, *, b)))
        )
        val _7b = thenHave((b ∈ B /\ ∃(a ∈ A, x === op(a, *, b))) <=> ((b ∈ B) /\ (x ∈ {op(a, *, b) | a ∈ A}))) by Tautology
        val _8 = thenHave(∀(b, (b ∈ B /\ ∃(a ∈ A, x === op(a, *, b))) <=> ((b ∈ B) /\ (x ∈ {op(a, *, b) | a ∈ A})))) by RightForall
        val _9 = have(RHS <=> ∃(b ∈ B, x ∈ {op(a, *, b) | a ∈ A})) by Tautology.from(
            _8,
            equivalenceSubstitutionExists of (
                x := b, 
                P := lambda(b, (b ∈ B /\ ∃(a ∈ A, x === op(a, *, b)))), 
                Q := lambda(b, ((b ∈ B) /\ (x ∈ {op(a, *, b) | a ∈ A})))
            )
        )
        
        val _10 = have((∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
            equivalenceIntroduceExists of (x := b, p := x ∈ y, P := lambda(b, (b ∈ B) /\ (y === { op(a, *, b) | a ∈ A })))
        )
        val _11 = thenHave(∀(y, (∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by RightForall 
        val _12 = have(∃(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y) <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _11, equivalenceSubstitutionExists of (
                x := y, 
                P := lambda(y, ∃(b ∈ B, y === { op(a, *, b) | a ∈ A }) /\ x ∈ y),
                Q := lambda(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))
            )
        )
        val _13 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _6, _12
        )

        assume(∃(b ∈ B, ∃(a ∈ A, x === op(a, *, b)))) // RHS
        val _14 = have(((y === { op(a, *, b) | a ∈ A }) /\ (x ∈ y)) |- x ∈ { op(a, *, b) | a ∈ A }) by Tautology.from(
            equalitySetMembership of (A := y, B := { op(a, *, b) | a ∈ A }, x := x)
        )

        val _15 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(_6, _12)
        val R = lambda(a, lambda(b, x ∈ {op(a, *, b) | a ∈ A}))
        val _16 = have(∃(b ∈ B, x ∈ {op(a, *, b) | a ∈ A})) by Tautology.from(_9)

        val _17 = have((x ∈ {op(a, *, b) | a ∈ A}) <=> (∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(
            existsMembershipSet of (A := {op(a, *, b) | a ∈ A}, B := y)
        )
        thenHave((b ∈ B /\ x ∈ {op(a, *, b) | a ∈ A}) <=> (b ∈ B /\ ∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y))) by Tautology
        val _18 = thenHave(∀(b, (b ∈ B /\ x ∈ {op(a, *, b) | a ∈ A}) <=> (b ∈ B /\ ∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y)))) by RightForall
        val _19 = have(∃(b ∈ B, x ∈ {op(a, *, b) | a ∈ A}) <=> ∃(b ∈ B, ∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(
            _18, equivalenceSubstitutionExists of (
                x := b,
                P := lambda(b, b ∈ B /\ x ∈ {op(a, *, b) | a ∈ A}),
                Q := lambda(b, b ∈ B /\ ∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y))
            )
        )
        val _20 = have(∃(b ∈ B, ∃(y, (y === {op(a, *, b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(_16, _19)
        val _21 = have(∃(y, ∃(b ∈ B, (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _20, swapExists of (a := b, A := B, b := y, 
                Utils.R := lambda(b, lambda(y,
                    (y === { op(a, *, b) | a ∈ A }) /\ x ∈ y
                ))
            )
        )
        have(thesis) by Tautology.from(_21, _15)
    }

    have(thesis) by Tautology.from(
        leftImplies, rightImplies
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
            _2, _4
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
      _1 of (y := fAx), _2 of (y := fAx)
    )

    have(∀(x ∈ A, ∃!(y, (x, y) ∈ fA))) by Tautology.from(
      functionBetween.definition of (f := fA)
    )
    thenHave(x ∈ A ==> ∃!(y, (x, y) ∈ fA)) by InstantiateForall(x)
    val _5 = thenHave(∃!(y, (x, y) ∈ fA)) by Tautology
    val _6 = have(∃!(y, (x, y) ∈ f)) by Tautology.from(
      _3, _5,
      equivalenceSubstitutionExistsOne of (x := y, P := auxP, Q := auxQ)
    )

    val _7a = have(auxQ(y) <=> (y === ε(z, auxQ(z)))) by Tautology.from(
      _4, _6, Quantifiers.existsOneEpsilonUniqueness of (x := z, P := auxQ)
    )
    val _7 = have(fAx === ε(z, auxQ(z))) by Tautology.from(
      _4, _7a of (y := fAx)
    )

    val _8 = have(app(f)(x) === ε(z, auxQ(z))) by Tautology.from(app.definition of (y := z))
    have(thesis) by Congruence.from(_7, _8)
  }
