package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}
import Symbols._

import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.Base.Symbols._
import lisa.maths.Quantifiers
import lisa.automation.Substitution
import lisa.maths.SetTheory.Base.EmptySet
import lisa.maths.SetTheory.Base.Singleton
import lisa.maths.SetTheory.Base.Subset
import lisa.Main
import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, function, functionBetween, functionOn}
import lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.BasicTheorems.*
import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Relations.Predef.{_, given}

import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.maths.GroupTheory.Utils.*
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

object Groups extends lisa.Main:

  case class Group(G: Expr[Ind], * : Expr[Ind])
  
  val binaryOperation = DEF(λ(G, λ(*,
    (* ↾ (G × G)) :: (G × G) -> G
  )))

  val isIdentityElement = DEF(λ(G, λ(*, λ(x,
    (x ∈ G) /\ (∀(y ∈ G, ((op(x, *, y) === y) /\ (op(y, *, x) === y))))
  ))))

  val identityElement = DEF(λ(G, λ(*,
    ∃(x, isIdentityElement(G)(*)(x))
  )))

  val identityOf = DEF(λ(G, λ(*,
    ε(e, isIdentityElement(G)(*)(e))
  )))

  val associativity = DEF(λ(G, λ(*,
    ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))
  )))

  val inverseElement = DEF(λ(G, λ(*,
    ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y))))
  )))

  val inverseOf = DEF(λ(G, λ(*, λ(x,
    ε(y, (y ∈ G) /\ (isIdentityElement(G)(*)(op(x, *, y))))
  )))).printAs(args => {
    val x = args(2)
    s"$x⁻¹"
  })

  val group = DEF(λ(G, λ(*,
    (binaryOperation(G)(*) /\
      identityElement(G)(*)) /\
      associativity(G)(*) /\
      inverseElement(G)(*)
  )))

  /* Lemmas */
  val identityGetsTransferredByCongruence = Theorem(
    (x === y, isIdentityElement(G)(*)(x)) |- isIdentityElement(G)(*)(y)
  ) {
    have(thesis) by Congruence
  }

  val inverseStaysInGroup = Theorem(
    (group(G)(*), x ∈ G) |- inverseOf(G)(*)(x) ∈ G
  ) {
    assume(group(G)(*), x ∈ G)
    val auxP = lambda(y,
      (y ∈ G) /\ isIdentityElement(G)(*)(op(x, *, y))
    )

    val inv = have(inverseElement(G)(*)) by Tautology.from(group.definition)

    val _1 = have(∀(x, x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y))))) by Tautology.from(inv, inverseElement.definition)
    val _2 = thenHave(x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))) by InstantiateForall(x)
    val _3 = thenHave(∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))) by Tautology
    val _4 = thenHave(∃(y, auxP(y))) by Tautology
    
    val eps = have(auxP(ε(y, auxP(y)))) by Tautology.from(_4, Quantifiers.existsEpsilon of (P := auxP))

    val _invDef = inverseOf(G)(*)(x) === ε(y, auxP(y))
    val invDef = have(_invDef) by Tautology.from(inverseOf.definition)

    val _5 = have(_invDef |- auxP(inverseOf(G)(*)(x))) by Substitution.Apply(_invDef)(eps)
    have(thesis) by Tautology.from(invDef, _5)
  }

  val associativityAlternateForm = Theorem(
    ∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))))
      |- associativity(G)(*)
  ) {
    assume(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))))

    val thm1 = have(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))))) by Restate
    val thm2 = have(∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by InstantiateForall(y)(thm2)
    val thm4 = have(((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by InstantiateForall(z)(thm3)
    val thm5 = thenHave(((x ∈ G), (y ∈ G), (z ∈ G)) |- (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by Restate

    // Build up z quantifier first
    val thm6 = thenHave(((x ∈ G), (y ∈ G)) |- (z ∈ G) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by Restate
    val thm7 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z, (z ∈ G) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by RightForall
    val thm8 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by Restate

    // Build up y quantifier
    val thm9 = thenHave((x ∈ G) |- (y ∈ G) ==> ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by Restate
    val thm10 = thenHave((x ∈ G) |- ∀(y, (y ∈ G) ==> ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by RightForall
    val thm11 = thenHave((x ∈ G) |- ∀(y ∈ G, ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by Restate

    // Build up x quantifier
    val thm12 = thenHave(() |- (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by Restate
    val thm13 = thenHave(() |- ∀(x, (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))))) by RightForall
    val thm14 = thenHave(() |- ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))))) by Restate

    have(associativity(G)(*)) by Tautology.from(thm14, associativity.definition)
  }

  val associativityThm = Theorem(
    (associativity(G)(*), x ∈ G, y ∈ G, z ∈ G) |-
      op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)
  ) {
    assume(associativity(G)(*), x ∈ G, y ∈ G, z ∈ G)

    // Unfold the definition of associativity
    val thm1 = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by Tautology.from(associativity.definition)

    // Instantiate x
    val thm2 = have((x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by Tautology.from(thm2)

    // Instantiate y
    val thm4 = have((y ∈ G) ==> ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by InstantiateForall(y)(thm3)
    val thm5 = have(∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by Tautology.from(thm4)

    // Instantiate z
    val thm6 = have((z ∈ G) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by InstantiateForall(z)(thm5)
    val thm7 = have(op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)) by Tautology.from(thm6)
  }

  val binaryOperationThm = Theorem(
    (binaryOperation(G)(*), x ∈ G, y ∈ G) |-
      op(x, *, y) ∈ G
  ) {
    assume(binaryOperation(G)(*), x ∈ G, y ∈ G)
    val _1 = have((* ↾ (G × G)) :: (G × G) -> G) by Tautology.from(binaryOperation.definition)
    
    val _2 = have((x, y) ∈ (G × G)) by Tautology.from(
      CartesianProduct.pairMembership of (A := G, B := G)
    )
    val x_y = Pair.pair(x)(y)
    val opG = (* ↾ (G × G))

    val _3 = have(app(opG)(x_y) === op(x, *, y)) by Tautology.from(
      _1, _2, restrictedAppTheorem of (f := *, x := x_y, A := (G × G), B := G)
    )
    val _4 = have(app(opG)(x_y) ∈ G) by Tautology.from(
      _1, _2,
      appTyping of (f := opG, x := x_y, A := (G × G), B := G)
    )
    thenHave(thesis) by Substitute(_3)
  }

  val identityIsUnique = Theorem(
    (group(G)(*), isIdentityElement(G)(*)(x), isIdentityElement(G)(*)(y)) |- x === y
  ) {
    assume(group(G)(*), isIdentityElement(G)(*)(x), isIdentityElement(G)(*)(y))
    val w = op(x, *, y)

    // x is an identity, so op(x, *, y) === y
    val step1a = have(isIdentityElement(G)(*)(x) |- ∀(a ∈ G, (op(x, *, a) === a) /\ (op(a, *, x) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, * := *, x := x)
    )
    val step1b = have(isIdentityElement(G)(*)(x) |- x ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, * := *, x := x)
    )
    val step1c = have(isIdentityElement(G)(*)(y) |- y ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, * := *, x := y)
    )
    val step1d = have(isIdentityElement(G)(*)(x) |- (y ∈ G) ==> ((op(x, *, y) === y) /\ (op(y, *, x) === y))) by InstantiateForall(y)(step1a)
    val step1 = have(w === y) by Tautology.from(step1d, step1c)

    // y is an identity, so op(x, *, y) === x
    val step2a = have(isIdentityElement(G)(*)(y) |- ∀(a ∈ G, (op(y, *, a) === a) /\ (op(a, *, y) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, * := *, x := y)
    )
    val step2b = have(isIdentityElement(G)(*)(y) |- (x ∈ G) ==> ((op(y, *, x) === x) /\ (op(x, *, y) === x))) by InstantiateForall(x)(step2a)
    val step2 = have(w === x) by Tautology.from(step2b, step1b)

    // Transitivity: x === w === y
    have(x === y) by Tautology.from(
      equalityTransitivity of (x := x, y := w, z := y),
      step2,
      step1
    )
  }

  // we can multiply to both sides of an equality
  val congruence = Theorem(
    (group(G)(*), x === y) |-
      op(z, *, x) === op(z, *, y)
  ) {
    have(thesis) by Congruence
  }

  val congruenceRight = Theorem(
    (group(G)(*), x === y) |-
      op(x, *, z) === op(y, *, z)
  ) {
    have(thesis) by Congruence
  }

  val inverseProperty2 = Theorem(
    (group(G)(*), x ∈ G) |- isIdentityElement(G)(*)(op(x, *, inverseOf(G)(*)(x)))
  ) {
    assume(group(G)(*), x ∈ G)
    val auxP = lambda(y, (y ∈ G) /\ (isIdentityElement(G)(*)(op(x, *, y))))
    val eps = have(∃(y, auxP(y)) |- auxP(ε(y, auxP(y)))) by Tautology.from(Quantifiers.existsEpsilon of (P := auxP))

    val ex = have(
      inverseElement(G)(*) |-
        ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y))))
    ) by Tautology.from(
      inverseElement.definition
    )

    val ex2 = thenHave(
      inverseElement(G)(*) |-
        ∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))))
    ) by Restate

    val ex3 = have(∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))))) by Tautology.from(ex2, group.definition)
    val ex4 = thenHave(x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y))))) by InstantiateForall(x)
    val ex5 = have(∃(y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))) by Tautology.from(ex4)
    val ex6 = have(∃(y ∈ G, auxP(y))) by Tautology.from(ex5)
    val ex7 = thenHave(∃(y, (y ∈ G) /\ auxP(y))) by Restate
    // val ex8 = have(∃(y, auxP(y)) ) by Tautology.from(ex7)
    val ex9 = have(auxP(ε(y, auxP(y)))) by Tautology.from(ex7, eps)

    val inv = inverseOf(G)(*)(x)
    val i1 = have(inv === ε(y, auxP(y))) by Tautology.from(inverseOf.definition)
    val eq1 = inv === ε(y, auxP(y))
    val i2 = have(eq1 |- auxP(inv)) by Substitution.Apply(eq1)(ex9)
    val i3 = have(auxP(inv)) by Tautology.from(i2, i1)
    val i4 = have((inv ∈ G) /\ (isIdentityElement(G)(*)(op(x, *, inv)))) by Tautology.from(i3)
    val i5 = have((isIdentityElement(G)(*)(op(x, *, inv)))) by Tautology.from(i4)
  }

  val inverseCommutability = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))
      |- isIdentityElement(G)(*)(op(y, *, x))
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, isIdentityElement(G)(*)(op(x, *, y)))
    val yInv = inverseOf(G)(*)(y)
    val e = op(x, *, y)

    val step0 = have(op(x, *, y) === e) by Restate
    val obs1 = have(yInv ∈ G) by Tautology.from(inverseStaysInGroup of (G := G, * := *, x := y))
    val assocG = have(associativity(G)(*)) by Tautology.from(group.definition)

    // Multiply both sides by y^(-1) on the right: (x * y) * y^(-1) === e * y^(-1)
    val step1 = have(op(op(x, *, y), *, yInv) === op(e, *, yInv)) by Tautology.from(
      congruenceRight of (G := G, * := *, x := op(x, *, y), y := e, z := yInv),
      step0
    )

    // e is an identity element, so e * y^(-1) === y^(-1)
    val step2a = have(isIdentityElement(G)(*)(e) |- ∀(z ∈ G, (op(e, *, z) === z) /\ (op(z, *, e) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := e)
    )

    val step2b = thenHave(isIdentityElement(G)(*)(e) |- (yInv ∈ G) ==> ((op(e, *, yInv) === yInv) /\ (op(yInv, *, e) === yInv))) by InstantiateForall(yInv)
    val step2 = have(op(e, *, yInv) === yInv) by Tautology.from(step2b, obs1)

    val step3 = have(op(op(x, *, y), *, yInv) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(op(x, *, y), *, yInv), y := op(e, *, yInv), z := yInv),
      step1,
      step2
    )

    // Use associativity: (x * y) * y^(-1) === x * (y * y^(-1))
    val step4 = have(op(op(x, *, y), *, yInv) === op(x, *, op(y, *, yInv))) by Tautology.from(
      associativityThm of (x := x, y := y, z := yInv),
      assocG,
      obs1
    )

    val step5 = have(op(x, *, op(y, *, yInv)) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(x, *, op(y, *, yInv)), y := op(op(x, *, y), *, yInv), z := yInv),
      step4,
      step3
    )

    // y * y^(-1) is an identity element (using inverseProperty2)
    val step6 = have(isIdentityElement(G)(*)(op(y, *, yInv))) by Tautology.from(
      inverseProperty2 of (G := G, * := *, x := y)
    )

    val step7a = have(isIdentityElement(G)(*)(op(y, *, yInv)) |- ∀(z ∈ G, (op(op(y, *, yInv), *, z) === z) /\ (op(z, *, op(y, *, yInv)) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := op(y, *, yInv))
    )
    val step7b = thenHave(isIdentityElement(G)(*)(op(y, *, yInv)) |- (x ∈ G) ==> ((op(op(y, *, yInv), *, x) === x) /\ (op(x, *, op(y, *, yInv)) === x))) by InstantiateForall(x)
    val step7 = have(op(x, *, op(y, *, yInv)) === x) by Tautology.from(step7b, step6)

    // Therefore x === y^(-1)
    val step8 = have(x === yInv) by Tautology.from(
      equalityTransitivity of (x := x, y := op(x, *, op(y, *, yInv)), z := yInv),
      step7,
      step5
    )

    // Multiply both sides by y on the left: y * x === y * y^(-1)
    val step9 = have(op(y, *, x) === op(y, *, yInv)) by Tautology.from(
      congruence of (G := G, * := *, x := x, y := yInv, z := y),
      step8
    )

    // y * y^(-1) is an identity element (using inverseProperty2 again)
    val step10 = have(isIdentityElement(G)(*)(op(y, *, yInv))) by Tautology.from(
      inverseProperty2 of (G := G, * := *, x := y)
    )

    // Therefore y * x is an identity element
    val step11Eq = op(y, *, x) === op(y, *, yInv)
    val step11 = have(step11Eq |- isIdentityElement(G)(*)(op(y, *, x))) by Substitution.Apply(step11Eq)(step10)
    have(isIdentityElement(G)(*)(op(y, *, x))) by Tautology.from(step11, step9)
  }

  val inverseCommutability2 = Theorem(
    (group(G)(*), x ∈ G, y ∈ G)
      |- isIdentityElement(G)(*)(op(x, *, y)) <=> isIdentityElement(G)(*)(op(y, *, x))
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G)
    val _1 = have(isIdentityElement(G)(*)(op(x, *, y)) ==> isIdentityElement(G)(*)(op(y, *, x))) by Restate.from(
      inverseCommutability
    )
    val _2 = have(isIdentityElement(G)(*)(op(y, *, x)) ==> isIdentityElement(G)(*)(op(x, *, y))) by Restate.from(
      inverseCommutability of (x := y, y := x)
    )
    have(thesis) by Tautology.from(_1, _2)
  }

  val inverseProperty = Theorem(
    (group(G)(*), x ∈ G) |- isIdentityElement(G)(*)(op(inverseOf(G)(*)(x), *, x))
  ) {
    assume(group(G)(*), x ∈ G)
    val thm1 = have(isIdentityElement(G)(*)(op(x, *, inverseOf(G)(*)(x)))) by Tautology.from(inverseProperty2)
    val thm1a = have(inverseOf(G)(*)(x) ∈ G) by Tautology.from(inverseStaysInGroup)
    val thm2 = have(isIdentityElement(G)(*)(op(inverseOf(G)(*)(x), *, x))) by Tautology.from(thm1a, inverseCommutability of (x := x, y := inverseOf(G)(*)(x)), thm1)
  }

  val applyAssociativity = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, z ∈ G) |- (a === op(x, *, op(y, *, z))) <=> (a === op(op(x, *, y), *, z))
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, z ∈ G)

    val assoc = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by Tautology.from(
      associativity.definition,
      group.definition
    )
    thenHave(∀(y ∈ G, ∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by InstantiateForall(x)
    thenHave(∀(z ∈ G, op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by InstantiateForall(y)
    thenHave(op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)) by InstantiateForall(z)

    thenHave(thesis) by Tautology.fromLastStep(
      equalityTransitivity of (x := a, y := op(x, *, op(y, *, z)), z := op(op(x, *, y), *, z)),
      equalityTransitivity of (x := a, y := op(op(x, *, y), *, z), z := op(x, *, op(y, *, z)))
    )
  }

  val identityProperty = Theorem(
    (group(G)(*), isIdentityElement(G)(*)(e), x ∈ G) |- ((op(e, *, x) === x) /\ (op(x, *, e) === x))
  ) {
    assume(group(G)(*), isIdentityElement(G)(*)(e), x ∈ G)
    have((e ∈ G) /\ (∀(y ∈ G, ((op(e, *, y) === y) /\ (op(y, *, e) === y))))) by Tautology.from(
      isIdentityElement.definition of (x := e)
    )
    thenHave(∀(y ∈ G, ((op(e, *, y) === y) /\ (op(y, *, e) === y)))) by Tautology 
    thenHave(thesis) by InstantiateForall(x)
  }

  val inverseCancelsOut = Theorem(
    (group(G)(*), x ∈ G, y ∈ G) |- op(inverseOf(G)(*)(x), *, op(x, *, y)) === y
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G)
    
    val inv = inverseOf(G)(*)(x)
    val e0 = op(inv, *, x)
    val _1 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
      inverseProperty of (x := x)
    )

    val _2 = have(op(e0, *, y) === y) by Tautology.from(
      _1,
      identityProperty of (e := e0, x := y)
    )

    have(thesis) by Tautology.from(
      _2,
      applyAssociativity of (a := y, x := inv, y := x, z := y),
      inverseStaysInGroup of (x := x)
    )
  }

  val doubleInverse = Theorem(
    (group(G)(*), x ∈ G) |- inverseOf(G)(*)(inverseOf(G)(*)(x)) === x
  ) {
    assume(group(G)(*), x ∈ G)
    
    val inv = inverseOf(G)(*)(x)
    val inv2 = inverseOf(G)(*)(inv)

    val e0 = op(inv, *, x)
    val _1 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
      inverseProperty of (x := x)
    )

    val _2 = have(op(inv2, *, op(inv, *, x)) === x) by Tautology.from(
      inverseCancelsOut of (x := inv, y := x),
      inverseStaysInGroup of (x := x)
    )

    val _3 = have(inv2 ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := inv),
      inverseStaysInGroup of (x := x)
    )

    val _4 = have(op(inv2, *, e0) === inv2) by Tautology.from(
      _1, _3,
      identityProperty of (e := e0, x := inv2)
    )

    have(thesis) by Tautology.from(
      equalityTransitivity of (x := x, y := op(inv2, *, e0), z := inv2),
      _2, _4
    )
  }

  val applyInverseLeft = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, z ∈ G) |-
      (x === op(y, *, z)) <=> (op(inverseOf(G)(*)(y), *, x) === z)
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, z ∈ G)
    
    val inv = inverseOf(G)(*)(y)    

    val leftImplies = have((x === op(y, *, z)) |- (op(inverseOf(G)(*)(y), *, x) === z)) subproof {
      assume(x === op(y, *, z))
  
      val _1 = have(op(inv, *, x) === op(inv, *, op(y, *, z))) by Tautology.from(congruence of (z := inv, x := x, y := op(y, *, z)))

      val _2 = have(op(inv, *, x) === op(op(inv, *, y), *, z)) by Tautology.from(
        _1,
        applyAssociativity of (a := op(inv, *, x), x := inv, y := y, z := z),
        inverseStaysInGroup of (x := y)
      )
      val e0 = op(inv, *, y)
      val _3 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
        group.definition,
        binaryOperationThm of (x := inv, y := y),
        inverseStaysInGroup of (x := y),
        inverseProperty of (x := y)
      )
      val _4 = have(op(e0, *, z) === z) by Tautology.from(
        _3,
        identityProperty of (e := e0, x := z)
      )

      have(op(inv, *, x) === z) by Tautology.from(
        equalityTransitivity of (x := op(inv, *, x), y := op(e0, *, z), z := z),
        _4,
        _2
      )
    }

    val rightImplies = have((op(inverseOf(G)(*)(y), *, x) === z) |- (x === op(y, *, z))) subproof {
      assume(op(inverseOf(G)(*)(y), *, x) === z)
      val inv2 = inverseOf(G)(*)(inv)
      val _1 = have(op(inv2, *, z) === x) by Tautology.from(
        leftImplies of (x := z, y := inv, z := x),
        inverseStaysInGroup of (x := y)
      )
      val _2 = have(inv2 === y) by Tautology.from(
        doubleInverse of (x := y)
      )

      have(y === inv2 |- op(y, *, z) === x) by Substitution.Apply(y === inv2)(_1)
      thenHave(x === op(y, *, z)) by Tautology.fromLastStep(_2)
    }

    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val applyInverseRight = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, z ∈ G) |- 
      (x === op(z, *, y)) <=> (op(x, *, inverseOf(G)(*)(y)) === z)
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, z ∈ G)

    val inv = inverseOf(G)(*)(y)

    val leftImplies = have((x === op(z, *, y)) |- (op(x, *, inv) === z)) subproof {
      assume(x === op(z, *, y))

      // apply congruence
      val _1 = have(op(x, *, inv) === op(op(z, *, y), *, inv)) by Tautology.from(
        congruenceRight of (z := inv, x := x, y := op(z, *, y))
      )

      // apply associativity
      val _2 = have(op(x, *, inv) === op(z, *, op(y, *, inv))) by Tautology.from(
        _1,
        applyAssociativity of (a := op(x, *, inv), x := z, y := y, z := inv),
        inverseStaysInGroup of (x := y)
      )

      // identify the identity element
      val e0 = op(y, *, inv)
      val _3 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
        group.definition,
        binaryOperationThm of (x := y, y := inv),
        inverseStaysInGroup of (x := y),
        inverseProperty2 of (x := y)
      )
      val _4 = have(op(z, *, e0) === z) by Tautology.from(
        _3,
        identityProperty of (e := e0, x := z)
      )

      // transitivity to get the final result
      have(op(x, *, inv) === z) by Tautology.from(
        equalityTransitivity of (x := op(x, *, inv), y := op(z, *, e0), z := z),
        _4,
        _2
      )
    }

    val rightImplies = have((op(x, *, inv) === z) |- (x === op(z, *, y))) subproof {
      assume(op(x, *, inv) === z)

      val inv2 = inverseOf(G)(*)(inv)
      val _1 = have(op(z, *, inv2) === x) by Tautology.from(
        leftImplies of (x := z, y := inv, z := x),
        inverseStaysInGroup of (x := y)
      )
      val _2 = have(inv2 === y) by Tautology.from(
        doubleInverse of (x := y)
      )

      have(y === inv2 |- op(z, *, y) === x) by Substitution.Apply(y === inv2)(_1)
      thenHave(x === op(z, *, y)) by Tautology.fromLastStep(_2)
    }

    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val eliminateLeft = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, z ∈ G) |- (op(z, *, x) === op(z, *, y)) <=> (x === y)
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, z ∈ G)

    val zx = op(z, *, x)
    val _1 = have(zx ∈ G) by Tautology.from(
      binaryOperationThm of (x := z, y := x),
      group.definition
    )

    val invz = inverseOf(G)(*)(z)
    val _2 = have(invz ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := z)
    )

    val _3 = have((op(invz, *, op(z, *, x)) === y) <=> (op(z, *, x) === op(z, *, y))) by Tautology.from(
      applyInverseLeft of (x := op(z, *, x), y := z, z := y),
      _1
    )

    val _4 = have((op(op(invz, *, z), *, x) === y) <=> (op(z, *, x) === op(z, *, y))) by Tautology.from(
      applyAssociativity of (a := y, x := invz, y := z, z := x),
      _2,
      _3
    )

    val e0 = op(invz, *, z)
    val _5 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
      inverseProperty of (x := z)
    )

    val prod = op(e0, *, x)
    have(e0 ∈ G) by Tautology.from(
      binaryOperationThm of (x := invz, y := z),
      group.definition,
      _2
    )
    val prodinG = thenHave(prod ∈ G) by Tautology.fromLastStep(
      binaryOperationThm of (x := e0, y := x),
      group.definition
    )

    val _6 = have(x === op(e0, *, x)) by Tautology.from(
      _5, identityProperty of (e := e0, x := x)
    )
    val _7 = have((op(op(invz, *, z), *, x) === y) <=> (y === x)) by Tautology.from(
      _6,
      equalityTransitivity of (x := x, y := op(e0, *, x), z := y),
      equalityTransitivity of (x := y, y := x, z := op(e0, *, x)),
      prodinG
    )

    have(thesis) by Tautology.from(_7, _4)
  }

  val eliminateRight = Theorem(
    (group(G)(*), x ∈ G, y ∈ G, z ∈ G) |- (op(x, *, z) === op(y, *, z)) <=> (x === y)
  ) {
    assume(group(G)(*), x ∈ G, y ∈ G, z ∈ G)

    val xz = op(x, *, z)
    val _1 = have(xz ∈ G) by Tautology.from(
      binaryOperationThm of (x := x, y := z),
      group.definition
    )

    val invz = inverseOf(G)(*)(z)
    val _2 = have(invz ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := z)
    )

    val _3 = have((op(op(x, *, z), *, invz) === y) <=> (xz === op(y, *, z))) by Tautology.from(
      applyInverseRight of (x := xz, y := z, z := y),
      _1
    )

    val _4 = have((op(x, *, op(z, *, invz)) === y) <=> (op(x, *, z) === op(y, *, z))) by Tautology.from(
      applyAssociativity of (a := y, x := x, y := z, z := invz),
      _2,
      _3
    )
    
    val e0 = op(z, *, invz)
    val _5 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(
      inverseProperty2 of (x := z)
    )

    val prod = op(x, *, e0)
    have(e0 ∈ G) by Tautology.from(
      binaryOperationThm of (x := z, y := invz),
      group.definition,
      _2
    )
    val prodinG = thenHave(prod ∈ G) by Tautology.fromLastStep(
      binaryOperationThm of (x := x, y := e0),
      group.definition
    )

    val _6 = have(x === op(x, *, e0)) by Tautology.from(
      _5, identityProperty of (e := e0, x := x)
    )
    val _7 = have((op(x, *, op(z, *, invz)) === y) <=> (y === x)) by Tautology.from(
      _6,
      equalityTransitivity of (x := x, y := op(x, *, e0), z := y),
      equalityTransitivity of (x := y, y := x, z := op(x, *, e0)),
      prodinG
    )

    have(thesis) by Tautology.from(_7, _4)
  }

  val identityOfIsIdentity = Theorem(
    (group(G)(*)) |- isIdentityElement(G)(*)(identityOf(G)(*))
  ) {
    assume(group(G)(*))
    val auxP = lambda(x, isIdentityElement(G)(*)(x))
    val e0 = identityOf(G)(*)

    val _1 = have(∃(x, auxP(x))) by Tautology.from(
      group.definition,
      identityElement.definition
    )
    val _2 = have(e0 === ε(x, auxP(x))) by Tautology.from(
      identityOf.definition
    )
    val _3 = have(auxP(ε(x, auxP(x)))) by Tautology.from(
      _1, _2, Quantifiers.existsEpsilon of (P := auxP)
    )
    have(thesis) by Congruence.from(
      _2, _3
    )
  }

  val identityIsIdempotent = Theorem(
    (group(G)(*)) |- isIdentityElement(G)(*)(e) <=> (e ∈ G /\ (op(e, *, e) === e))
  ) {
    assume(group(G)(*))
    val `==>` = have(isIdentityElement(G)(*)(e) |- (op(e, *, e) === e) /\ e ∈ G) subproof {
      have(thesis) by Tautology.from(
        identityProperty of (x := e),
        isIdentityElement.definition of (x := e)
      )
    }
    val `<==` = have((e ∈ G, op(e, *, e) === e) |- isIdentityElement(G)(*)(e)) subproof {
      assume(e ∈ G, op(e, *, e) === e)
      val e0 = identityOf(G)(*)
      val e0inG = have(e0 ∈ G) by Tautology.from(
        identityOfIsIdentity, isIdentityElement.definition of (x := e0)
      )
      have(op(e0, *, e) === e) by Tautology.from(
        identityOfIsIdentity, identityProperty of (e := e0, x := e)
      )
      thenHave(op(e0, *, e) === op(e, *, e)) by Congruence
      val subst = thenHave(e0 === e) by Tautology.fromLastStep(
        eliminateRight of (x := e0, y := e, z := e), e0inG
      )
      have(isIdentityElement(G)(*)(e0)) by Tautology.from(identityOfIsIdentity)
      thenHave(thesis) by Substitute(subst)
    }
    have(thesis) by Tautology.from(`<==`, `==>`)
  }

  val binaryOperationTestSubset = Theorem(
    (binaryOperation(G)(*), H ⊆ G, 
      ∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> op(x, *, y) ∈ H))
    )
    |- binaryOperation(H)(*)
  ) {
    assume(binaryOperation(G)(*), H ⊆ G, 
      ∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> op(x, *, y) ∈ H))
    )
    val G2 = G × G
    val fG2 = * ↾ (G × G)
    val H2 = H × H
    val fH2 = * ↾ (H × H)

    val H2sub = have(H2 ⊆ G2) by Tautology.from(
      CartesianProduct.monotonic of (A := H, B := H, C := G, D := G)
    )

    val _1 = have(fG2 :: G2 -> G) by Tautology.from(binaryOperation.definition)
    val _2 = have(fH2 :: H2 -> G) by Tautology.from(
      _1, H2sub, restrictedAppTheorem2 of (f := *, A := G2, B := H2, C := G)
    )
    val _3 = have((z ∈ H2) |- app(fH2)(z) ∈ H) subproof {
      assume(z ∈ H2)
      val x0 = fst(z)
      val y0 = snd(z)
      val _1a = have(z === (x0, y0)) by Tautology.from(
        CartesianProduct.inversion of (A := H, B := H)
      )
      val _2a = have(x0 ∈ H /\ y0 ∈ H) by Tautology.from(
        CartesianProduct.fstMembership of (A := H, B := H),
        CartesianProduct.sndMembership of (A := H, B := H)
      )
      val _3a = have(app(fH2)(z) === app(*)(z)) by Tautology.from(
        _2, restrictedAppTheorem of (x := z, f := *, A := H2, B := G)
      )
      val _4a = have(app(fH2)(z) === op(x0, *, y0)) by Congruence.from(_3a, _1a)
      have(∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> op(x, *, y) ∈ H))) by Restate
      thenHave((x0 ∈ H /\ y0 ∈ H) ==> op(x0, *, y0) ∈ H) by InstantiateForall(x0, y0)
      thenHave(op(x0, *, y0) ∈ H) by Tautology.fromLastStep(_2a)
      thenHave(thesis) by Substitute(_4a)
    }
    val _4 = thenHave(z ∈ H2 ==> app(fH2)(z) ∈ H) by Restate
    val _5 = thenHave(∀(z ∈ H2, app(fH2)(z) ∈ H)) by RightForall

    have(fH2 :: H2 -> H) by Tautology.from(
      _2, _5, 
      restrictedAppTheorem3 of (A := H2, B := H, C := G, f := fH2)
    )
    thenHave(thesis) by Tautology.fromLastStep(
      binaryOperation.definition of (G := H)
    )
  }

  val identityElementTestSubset = Theorem(
    (isIdentityElement(G)(*)(e), e ∈ H, H ⊆ G)
    |- isIdentityElement(H)(*)(e)
  ) {
    assume(isIdentityElement(G)(*)(e), e ∈ H, H ⊆ G)

    have((e ∈ G) /\ (∀(y ∈ G, ((op(e, *, y) === y) /\ (op(y, *, e) === y))))) by Tautology.from(
      isIdentityElement.definition of (x := e)
    )
    thenHave(∀(y ∈ G, ((op(e, *, y) === y) /\ (op(y, *, e) === y)))) by Tautology
    thenHave(y ∈ G ==> ((op(e, *, y) === y) /\ (op(y, *, e) === y))) by InstantiateForall(y)
    thenHave(y ∈ H ==> ((op(e, *, y) === y) /\ (op(y, *, e) === y))) by Tautology.fromLastStep(
      Subset.membership of (z := y, x := H, y := G)
    )
    thenHave(∀(y ∈ H, ((op(e, *, y) === y) /\ (op(y, *, e) === y)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(
      isIdentityElement.definition of (x := e, G := H)
    )
  }

  val binaryOperationTest = Theorem(
    (function(*), (G × G) ⊆ dom(*), ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> op(x, *, y) ∈ G)))
    |- binaryOperation(G)(*)
  ) {
    assume(function(*), (G × G) ⊆ dom(*), ∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> op(x, *, y) ∈ G)))
    val fR = (* ↾ (G × G))
    val _1 = have(dom(fR) === dom(*) ∩ (G × G)) by Tautology.from(
      restrictionDomain of (f := *, A := (G × G))
    )
    val _2 = have(dom(*) ∩ (G × G) === (G × G) ∩ dom(*)) by Tautology.from(
      Intersection.commutativity of (x := dom(*), y := (G × G))
    )
    val _3 = have((G × G) ∩ dom(*) === (G × G)) by Tautology.from(
      Intersection.ofSubsets of (x := (G × G), y := dom(*))
    )
    val _4 = have(dom(fR) === (G × G)) by Congruence.from(_1, _2, _3)
    val _5 = have(function(fR)) by Tautology.from(Restriction.isFunction of (f := *, A := (G × G)))
    have(functionOn(fR)(G × G)) by Tautology.from(_4, _5, functionOnIffFunctionWithDomain of (f := fR, A := (G × G)))
    thenHave(∃(B, fR :: (G × G) -> B)) by Tautology.fromLastStep(functionOn.definition of (f := fR, A := (G × G)))
    val auxP = lambda(B, fR :: (G × G) -> B)
    val B0 = ε(B, auxP(B))
    val _6 = thenHave(fR :: (G × G) -> B0) by Tautology.fromLastStep(Quantifiers.existsEpsilon of (x := B, P := auxP))
    
    have(z ∈ (G × G) |- app(fR)(z) ∈ G) subproof {
      assume(z ∈ (G × G))
      val step1 = have(app(*)(z) === app(fR)(z)) by Tautology.from(
        _6, restrictedAppTheorem of (f := *, A := (G × G), B := B0, x := z)
      )
      val x0 = fst(z)
      val y0 = snd(z)
      val step2 = have(x0 ∈ G /\ y0 ∈ G) by Tautology.from(
        CartesianProduct.fstMembership of (A := G, B := G),
        CartesianProduct.sndMembership of (A := G, B := G)
      )
      val step3 = have(z === (x0, y0)) by Tautology.from(CartesianProduct.inversion of (A := G, B := G))
      val step4 = have(op(x0, *, y0) === app(fR)(z)) by Congruence.from(step1, step3)
      have(∀(x, ∀(y, (x ∈ G /\ y ∈ G) ==> op(x, *, y) ∈ G))) by Restate
      thenHave((x0 ∈ G /\ y0 ∈ G) ==> op(x0, *, y0) ∈ G) by InstantiateForall(x0, y0)
      thenHave(op(x0, *, y0) ∈ G) by Tautology.fromLastStep(step2)
      thenHave(thesis) by Substitute(step4)
    }
    thenHave(z ∈ (G × G) ==> app(fR)(z) ∈ G) by Restate
    val _7 = thenHave(∀(z ∈ (G × G), app(fR)(z) ∈ G)) by RightForall
    have(fR :: (G × G) -> G) by Tautology.from(
      _6, _7,
      restrictedAppTheorem3 of (f := fR, A := (G × G), C := B0, B := G)
    )
    thenHave(thesis) by Tautology.fromLastStep(binaryOperation.definition)
  }