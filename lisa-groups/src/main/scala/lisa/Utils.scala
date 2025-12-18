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

object Utils extends lisa.Main:
  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

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

  val P, Q = variable[Ind >>: Prop]
  val p, q = variable[Prop]
  val R = variable[Ind >>: Ind >>: Prop]
  val op = variable[Ind >>: Ind >>: Ind]

  val equivalenceSubstitutionExists = Theorem(∀(x, P(x) <=> Q(x)) |-  ∃(x, P(x)) <=> ∃(x, Q(x))) {
    have(thesis) by Tableau
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
    (x ∈ ⋃{ {op(a)(b) | a ∈ A} | b ∈ B }) <=> ∃(b ∈ B, ∃(a ∈ A, x === op(a)(b)))
  ) {
    val SS = { { op(a)(b) | a ∈ A } | b ∈ B }
    val LHS = ⋃(SS)
    val RHS = ∃(b ∈ B, ∃(a ∈ A, x === op(a)(b)))
    val _1 = have((x ∈ LHS) <=> ∃(y ∈ SS, x ∈ y)) by Tautology.from(
        unionAxiom of (x := SS, y := y, z := x)
    )
    val _2 = have(y ∈ SS <=> ∃(b ∈ B, y === { op(a)(b) | a ∈ A })) by Tautology.from(
        Replacement.membership of (x := b, A := B, y := y, F := lambda(b, { op(a)(b) | a ∈ A }))
    )
    val leftImplies = have(x ∈ LHS |- RHS) subproof {
        assume(x ∈ LHS)
        val _3 = have(∃(y, y ∈ SS /\ x ∈ y)) by Tautology.from(_1)
        val auxP = lambda(y, y ∈ SS /\ x ∈ y)
        val y0 = ε(y, y ∈ SS /\ x ∈ y)
        val _4 = have(auxP(y0)) by Tautology.from(
            _3, Quantifiers.existsEpsilon of (x := y, P := auxP)
        )

        val _5 = have(∃(b ∈ B, y0 === { op(a)(b) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
            _2 of (y := y0), _4
        )

        val auxP2 = lambda(b, b ∈ B /\ (y0 === { op(a)(b) | a ∈ A }))
        val b0 = ε(b, auxP2(b))
        val _6 = have(b0 ∈ B /\ (y0 === { op(a)(b0) | a ∈ A }) /\ x ∈ y0) by Tautology.from(
            _5, Quantifiers.existsEpsilon of (x := b, P := auxP2)
        )

        val _7 = have(b0 ∈ B /\ x ∈ { op(a)(b0) | a ∈ A }) by Tautology.from(
            _6, equalitySetMembership of (x := x, A := y0, B := { op(a)(b0) | a ∈ A })
        )
        val _8 = have(b0 ∈ B /\ ∃(a ∈ A, x === op(a)(b0))) by Tautology.from(
            _7, Replacement.membership of (x := a, A := A, y := x, F := lambda(a, op(a)(b0)))
        )
        thenHave(thesis) by RightExists
    }
    val rightImplies = have(RHS |- x ∈ LHS) subproof {
        val subst = y ∈ SS <=> ∃(b ∈ B, y === { op(a)(b) | a ∈ A }) 
        val auxP = lambda(y, y ∈ SS /\ x ∈ y)
        val auxQ = lambda(y, ∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y)
        val _3 = have(auxP(y) <=> auxQ(y)) by Tautology.from(_2)
        val _4 = thenHave(∀(y, auxP(y) <=> auxQ(y))) by RightForall
        
        val _5 = have(∃(y, auxP(y)) <=> ∃(y, auxQ(y))) by Tautology.from(
            _4, equivalenceSubstitutionExists of (x := y, P := auxP, Q := auxQ)
        )
        val _6 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
            _1, _5
        )

        val _7 = have(∃(a ∈ A, x === op(a)(b)) <=> (x ∈ {op(a)(b) | a ∈ A})) by Tautology.from(
            Replacement.membership of (x := a, y := x, A := A, F := lambda(a, op(a)(b)))
        )
        val _7b = thenHave((b ∈ B /\ ∃(a ∈ A, x === op(a)(b))) <=> ((b ∈ B) /\ (x ∈ {op(a)(b) | a ∈ A}))) by Tautology
        val _8 = thenHave(∀(b, (b ∈ B /\ ∃(a ∈ A, x === op(a)(b))) <=> ((b ∈ B) /\ (x ∈ {op(a)(b) | a ∈ A})))) by RightForall
        val _9 = have(RHS <=> ∃(b ∈ B, x ∈ {op(a)(b) | a ∈ A})) by Tautology.from(
            _8,
            equivalenceSubstitutionExists of (
                x := b, 
                P := lambda(b, (b ∈ B /\ ∃(a ∈ A, x === op(a)(b)))), 
                Q := lambda(b, ((b ∈ B) /\ (x ∈ {op(a)(b) | a ∈ A})))
            )
        )
        
        val _10 = have((∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y)) by Tautology.from(
            equivalenceIntroduceExists of (x := b, p := x ∈ y, P := lambda(b, (b ∈ B) /\ (y === { op(a)(b) | a ∈ A })))
        )
        val _11 = thenHave(∀(y, (∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y) <=> ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))) by RightForall 
        val _12 = have(∃(y, ∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y) <=> ∃(y, ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _11, equivalenceSubstitutionExists of (
                x := y, 
                P := lambda(y, ∃(b ∈ B, y === { op(a)(b) | a ∈ A }) /\ x ∈ y),
                Q := lambda(y, ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))
            )
        )
        val _13 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _6, _12
        )

        assume(∃(b ∈ B, ∃(a ∈ A, x === op(a)(b)))) // RHS
        val _14 = have(((y === { op(a)(b) | a ∈ A }) /\ (x ∈ y)) |- x ∈ { op(a)(b) | a ∈ A }) by Tautology.from(
            equalitySetMembership of (A := y, B := { op(a)(b) | a ∈ A }, x := x)
        )

        val _15 = have(x ∈ LHS <=> ∃(y, ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(_6, _12)
        val R = lambda(a, lambda(b, x ∈ {op(a)(b) | a ∈ A}))
        val _16 = have(∃(b ∈ B, x ∈ {op(a)(b) | a ∈ A})) by Tautology.from(_9)

        val _17 = have((x ∈ {op(a)(b) | a ∈ A}) <=> (∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(
            existsMembershipSet of (A := {op(a)(b) | a ∈ A}, B := y)
        )
        thenHave((b ∈ B /\ x ∈ {op(a)(b) | a ∈ A}) <=> (b ∈ B /\ ∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y))) by Tautology
        val _18 = thenHave(∀(b, (b ∈ B /\ x ∈ {op(a)(b) | a ∈ A}) <=> (b ∈ B /\ ∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y)))) by RightForall
        val _19 = have(∃(b ∈ B, x ∈ {op(a)(b) | a ∈ A}) <=> ∃(b ∈ B, ∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(
            _18, equivalenceSubstitutionExists of (
                x := b,
                P := lambda(b, b ∈ B /\ x ∈ {op(a)(b) | a ∈ A}),
                Q := lambda(b, b ∈ B /\ ∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y))
            )
        )
        val _20 = have(∃(b ∈ B, ∃(y, (y === {op(a)(b) | a ∈ A}) /\ x ∈ y))) by Tautology.from(_16, _19)
        val _21 = have(∃(y, ∃(b ∈ B, (y === { op(a)(b) | a ∈ A }) /\ x ∈ y))) by Tautology.from(
            _20, swapExists of (a := b, A := B, b := y, 
                Utils.R := lambda(b, lambda(y,
                    (y === { op(a)(b) | a ∈ A }) /\ x ∈ y
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
    (x === op(a)(b), a === c, b === d) |- (x === op(c)(d))
  ) {
    have(thesis) by Congruence
  }