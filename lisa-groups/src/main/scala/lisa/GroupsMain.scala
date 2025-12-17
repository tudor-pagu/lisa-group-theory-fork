package lisa.maths.GroupTheory

import lisa.maths.SetTheory.Base.Predef.{_, given}

import lisa.kernel.proof.RunningTheoryJudgement._
import lisa.maths.SetTheory.Base.Symbols._
import lisa.maths.Quantifiers
import lisa.automation.Substitution
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
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.maths.GroupTheory.Utils.equalityTransitivity

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

object Groups extends lisa.Main:
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

  val binaryOperation = DEF(λ(G, λ(op, ∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)))))

  val isIdentityElement = DEF(λ(G, λ(op, λ(x, (x ∈ G) /\ (∀(y ∈ G, ((op(x)(y) === y) /\ (op(y)(x) === y))))))))

  val identityElement = DEF(λ(G, λ(op, ∃(x, isIdentityElement(G)(op)(x)))))
  val identityOf = DEF(λ(G, λ(op, ε(e, isIdentityElement(G)(op)(e)))))

  val associativity = DEF(λ(G, λ(op, ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))))))

  val inverseElement = DEF(λ(G, λ(op, ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))))

  val inverseOf = DEF(λ(G, λ(op, λ(x, ε(y, (y ∈ G) /\ (isIdentityElement(G)(op)(op(x)(y))))))))

  val group = DEF(
    λ(
      G,
      λ(
        op,
        (binaryOperation(G)(op) /\
          identityElement(G)(op)) /\
          associativity(G)(op) /\
          inverseElement(G)(op)
      )
    )
  )

  /*
  Subgroup
   */

  val subgroup = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          group(G)(op) /\
            H ⊆ G /\
            group(H)(op)
        )
      )
    )
  )

  /*
  Cosets
   */

  val leftCoset = DEF(
    λ(
      g,
      λ(
        op,
        λ(
          H,
          (op(g)(h) | (h ∈ H))
        )
      )
    )
  )

  val rightCoset = DEF(
    λ(
      H,
      λ(
        op,
        λ(
          g,
          (op(h)(g) | (h ∈ H))
        )
      )
    )
  )

  /*
  Normal
   */

  val normalizer = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          { g ∈ G | leftCoset(g)(op)(H) === rightCoset(H)(op)(g) }
        )
      )
    )
  )

  val conjugation = DEF(λ(G, λ(op, λ(x, λ(y, op(op(y)(x))(inverseOf(G)(op)(y)))))))
  
  val normalSubgroup = DEF(
    λ(
      H,
      λ(
        G,
        λ(
          op,
          subgroup(H)(G)(op) /\
          ∀(g ∈ G, leftCoset(g)(op)(H) === rightCoset(H)(op)(g))
        )
      )
    )
  )

  val quotientGroup = DEF(λ(G, λ(H, λ(op, 
    { leftCoset(g)(op)(H) | g ∈ G }
  ))))
  val isCosetOperation = DEF(λ(G, λ(H, λ(op, λ(op2,
    ∀(A ∈ quotientGroup(G)(H)(op), ∀(B ∈ quotientGroup(G)(H)(op), 
      op2(A)(B) === ⋃{ {op(a)(b) | a ∈ A} | b ∈ B }
    ))
  )))))

  /*
  Functions on groups
   */

  /* Lemmas */
  val identityGetsTransferredByCongruence = Theorem(
    (x === y, isIdentityElement(G)(op)(x)) |- isIdentityElement(G)(op)(y)
  ) {
    have(thesis) by Congruence
  }

  val inverseStaysInGroup = Theorem(
    (group(G)(op), x ∈ G) |- inverseOf(G)(op)(x) ∈ G
  ) {
    assume(group(G)(op), x ∈ G)
    val auxP = lambda(y,
      (y ∈ G) /\ isIdentityElement(G)(op)(op(x)(y))
    )

    val inv = have(inverseElement(G)(op)) by Tautology.from(group.definition)

    val _1 = have(∀(x, x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))) by Tautology.from(inv, inverseElement.definition)
    val _2 = thenHave(x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by InstantiateForall(x)
    val _3 = thenHave(∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by Tautology
    val _4 = thenHave(∃(y, auxP(y))) by Tautology
    
    val eps = have(auxP(ε(y, auxP(y)))) by Tautology.from(_4, Quantifiers.existsEpsilon of (P := auxP))

    val _invDef = inverseOf(G)(op)(x) === ε(y, auxP(y))
    val invDef = have(_invDef) by Tautology.from(inverseOf.definition)

    val _5 = have(_invDef |- auxP(inverseOf(G)(op)(x))) by Substitution.Apply(_invDef)(eps)
    have(thesis) by Tautology.from(invDef, _5)
  }

  val associativityAlternateForm = Theorem(
    ∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))))
      |- associativity(G)(op)
  ) {
    assume(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))))))

    val thm1 = have(∀(x, ∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by Restate
    val thm2 = have(∀(y, ∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(z, ((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by InstantiateForall(y)(thm2)
    val thm4 = have(((x ∈ G) /\ (y ∈ G) /\ (z ∈ G)) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(z)(thm3)
    val thm5 = thenHave(((x ∈ G), (y ∈ G), (z ∈ G)) |- (op(x)(op(y)(z)) === op(op(x)(y))(z))) by Restate

    // Build up z quantifier first
    val thm6 = thenHave(((x ∈ G), (y ∈ G)) |- (z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by Restate
    val thm7 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z, (z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by RightForall
    val thm8 = thenHave(((x ∈ G), (y ∈ G)) |- ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Restate

    // Build up y quantifier
    val thm9 = thenHave((x ∈ G) |- (y ∈ G) ==> ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Restate
    val thm10 = thenHave((x ∈ G) |- ∀(y, (y ∈ G) ==> ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by RightForall
    val thm11 = thenHave((x ∈ G) |- ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Restate

    // Build up x quantifier
    val thm12 = thenHave(() |- (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Restate
    val thm13 = thenHave(() |- ∀(x, (x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by RightForall
    val thm14 = thenHave(() |- ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, (op(x)(op(y)(z)) === op(op(x)(y))(z)))))) by Restate

    have(associativity(G)(op)) by Tautology.from(thm14, associativity.definition)
  }

  val associativityThm = Theorem(
    (associativity(G)(op), x ∈ G, y ∈ G, z ∈ G) |-
      op(x)(op(y)(z)) === op(op(x)(y))(z)
  ) {
    assume(associativity(G)(op), x ∈ G, y ∈ G, z ∈ G)

    // Unfold the definition of associativity
    val thm1 = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Tautology.from(associativity.definition)

    // Instantiate x
    val thm2 = have((x ∈ G) ==> ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) by InstantiateForall(x)(thm1)
    val thm3 = have(∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) by Tautology.from(thm2)

    // Instantiate y
    val thm4 = have((y ∈ G) ==> ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(y)(thm3)
    val thm5 = have(∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))) by Tautology.from(thm4)

    // Instantiate z
    val thm6 = have((z ∈ G) ==> (op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(z)(thm5)
    val thm7 = have(op(x)(op(y)(z)) === op(op(x)(y))(z)) by Tautology.from(thm6)
  }

  val binaryOperationThm = Theorem(
    (binaryOperation(G)(op), x ∈ G, y ∈ G) |-
      op(x)(y) ∈ G
  ) {
    assume(binaryOperation(G)(op), x ∈ G, y ∈ G)
    have(∀(x, ∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G))) by Tautology.from(binaryOperation.definition)
    thenHave(∀(y, x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G)) by InstantiateForall(x)
    thenHave(x ∈ G /\ y ∈ G ==> op(x)(y) ∈ G) by InstantiateForall(y)
    thenHave(thesis) by Tautology
  }

  /* Lagrange's Theorem */

  // P is a partition of G
  val partition = DEF(
    λ(
      G,
      λ(
        Pr,
        (∀(x ∈ Pr, x ⊆ G)) /\ // every set in P is a subset of G
          (∀(x ∈ G, ∃(y ∈ Pr, x ∈ y))) /\ // every element of G is found in some set in P
          (∀(x ∈ Pr, ∀(y ∈ Pr, x ≠ y ==> (x ∩ y === ∅)))) // the sets in P are disjoint
      )
    )
  )

  val identityIsUnique = Theorem(
    (group(G)(op), isIdentityElement(G)(op)(x), isIdentityElement(G)(op)(y)) |- x === y
  ) {
    assume(group(G)(op), isIdentityElement(G)(op)(x), isIdentityElement(G)(op)(y))
    val w = op(x)(y)

    // x is an identity, so op(x)(y) === y
    val step1a = have(isIdentityElement(G)(op)(x) |- ∀(a ∈ G, (op(x)(a) === a) /\ (op(a)(x) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := x)
    )
    val step1b = have(isIdentityElement(G)(op)(x) |- x ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := x)
    )
    val step1c = have(isIdentityElement(G)(op)(y) |- y ∈ G) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := y)
    )
    val step1d = have(isIdentityElement(G)(op)(x) |- (y ∈ G) ==> ((op(x)(y) === y) /\ (op(y)(x) === y))) by InstantiateForall(y)(step1a)
    val step1 = have(w === y) by Tautology.from(step1d, step1c)

    // y is an identity, so op(x)(y) === x
    val step2a = have(isIdentityElement(G)(op)(y) |- ∀(a ∈ G, (op(y)(a) === a) /\ (op(a)(y) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, op := op, x := y)
    )
    val step2b = have(isIdentityElement(G)(op)(y) |- (x ∈ G) ==> ((op(y)(x) === x) /\ (op(x)(y) === x))) by InstantiateForall(x)(step2a)
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
    (group(G)(op), x === y) |-
      op(z)(x) === op(z)(y)
  ) {
    have(thesis) by Congruence
  }

  val congruenceRight = Theorem(
    (group(G)(op), x === y) |-
      op(x)(z) === op(y)(z)
  ) {
    have(thesis) by Congruence
  }

  val inverseProperty2 = Theorem(
    (group(G)(op), x ∈ G) |- isIdentityElement(G)(op)(op(x)(inverseOf(G)(op)(x)))
  ) {
    assume(group(G)(op), x ∈ G)
    val auxP = lambda(y, (y ∈ G) /\ (isIdentityElement(G)(op)(op(x)(y))))
    val eps = have(∃(y, auxP(y)) |- auxP(ε(y, auxP(y)))) by Tautology.from(Quantifiers.existsEpsilon of (P := auxP))

    val ex = have(
      inverseElement(G)(op) |-
        ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))
    ) by Tautology.from(
      inverseElement.definition
    )

    val ex2 = thenHave(
      inverseElement(G)(op) |-
        ∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))
    ) by Restate

    val ex3 = have(∀(x, x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))) by Tautology.from(ex2, group.definition)
    val ex4 = thenHave(x ∈ G ==> (∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y))))) by InstantiateForall(x)
    val ex5 = have(∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))) by Tautology.from(ex4)
    val ex6 = have(∃(y ∈ G, auxP(y))) by Tautology.from(ex5)
    val ex7 = thenHave(∃(y, (y ∈ G) /\ auxP(y))) by Restate
    // val ex8 = have(∃(y, auxP(y)) ) by Tautology.from(ex7)
    val ex9 = have(auxP(ε(y, auxP(y)))) by Tautology.from(ex7, eps)

    val inv = inverseOf(G)(op)(x)
    val i1 = have(inv === ε(y, auxP(y))) by Tautology.from(inverseOf.definition)
    val eq1 = inv === ε(y, auxP(y))
    val i2 = have(eq1 |- auxP(inv)) by Substitution.Apply(eq1)(ex9)
    val i3 = have(auxP(inv)) by Tautology.from(i2, i1)
    val i4 = have((inv ∈ G) /\ (isIdentityElement(G)(op)(op(x)(inv)))) by Tautology.from(i3)
    val i5 = have((isIdentityElement(G)(op)(op(x)(inv)))) by Tautology.from(i4)
  }

  val inverseCommutability = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, isIdentityElement(G)(op)(op(x)(y)))
      |- isIdentityElement(G)(op)(op(y)(x))
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, isIdentityElement(G)(op)(op(x)(y)))
    val yInv = inverseOf(G)(op)(y)
    val e = op(x)(y)

    val step0 = have(op(x)(y) === e) by Restate
    val obs1 = have(yInv ∈ G) by Tautology.from(inverseStaysInGroup of (G := G, op := op, x := y))
    val assocG = have(associativity(G)(op)) by Tautology.from(group.definition)

    // Multiply both sides by y^(-1) on the right: (x * y) * y^(-1) === e * y^(-1)
    val step1 = have(op(op(x)(y))(yInv) === op(e)(yInv)) by Tautology.from(
      congruenceRight of (G := G, op := op, x := op(x)(y), y := e, z := yInv),
      step0
    )

    // e is an identity element, so e * y^(-1) === y^(-1)
    val step2a = have(isIdentityElement(G)(op)(e) |- ∀(z ∈ G, (op(e)(z) === z) /\ (op(z)(e) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := e)
    )

    val step2b = thenHave(isIdentityElement(G)(op)(e) |- (yInv ∈ G) ==> ((op(e)(yInv) === yInv) /\ (op(yInv)(e) === yInv))) by InstantiateForall(yInv)
    val step2 = have(op(e)(yInv) === yInv) by Tautology.from(step2b, obs1)

    val step3 = have(op(op(x)(y))(yInv) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(op(x)(y))(yInv), y := op(e)(yInv), z := yInv),
      step1,
      step2
    )

    // Use associativity: (x * y) * y^(-1) === x * (y * y^(-1))
    val step4 = have(op(op(x)(y))(yInv) === op(x)(op(y)(yInv))) by Tautology.from(
      associativityThm of (x := x, y := y, z := yInv),
      assocG,
      obs1
    )

    val step5 = have(op(x)(op(y)(yInv)) === yInv) by Tautology.from(
      equalityTransitivity of (x := op(x)(op(y)(yInv)), y := op(op(x)(y))(yInv), z := yInv),
      step4,
      step3
    )

    // y * y^(-1) is an identity element (using inverseProperty2)
    val step6 = have(isIdentityElement(G)(op)(op(y)(yInv))) by Tautology.from(
      inverseProperty2 of (G := G, op := op, x := y)
    )

    val step7a = have(isIdentityElement(G)(op)(op(y)(yInv)) |- ∀(z ∈ G, (op(op(y)(yInv))(z) === z) /\ (op(z)(op(y)(yInv)) === z))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := op(y)(yInv))
    )
    val step7b = thenHave(isIdentityElement(G)(op)(op(y)(yInv)) |- (x ∈ G) ==> ((op(op(y)(yInv))(x) === x) /\ (op(x)(op(y)(yInv)) === x))) by InstantiateForall(x)
    val step7 = have(op(x)(op(y)(yInv)) === x) by Tautology.from(step7b, step6)

    // Therefore x === y^(-1)
    val step8 = have(x === yInv) by Tautology.from(
      equalityTransitivity of (x := x, y := op(x)(op(y)(yInv)), z := yInv),
      step7,
      step5
    )

    // Multiply both sides by y on the left: y * x === y * y^(-1)
    val step9 = have(op(y)(x) === op(y)(yInv)) by Tautology.from(
      congruence of (G := G, op := op, x := x, y := yInv, z := y),
      step8
    )

    // y * y^(-1) is an identity element (using inverseProperty2 again)
    val step10 = have(isIdentityElement(G)(op)(op(y)(yInv))) by Tautology.from(
      inverseProperty2 of (G := G, op := op, x := y)
    )

    // Therefore y * x is an identity element
    val step11Eq = op(y)(x) === op(y)(yInv)
    val step11 = have(step11Eq |- isIdentityElement(G)(op)(op(y)(x))) by Substitution.Apply(step11Eq)(step10)
    have(isIdentityElement(G)(op)(op(y)(x))) by Tautology.from(step11, step9)
  }

  val inverseCommutability2 = Theorem(
    (group(G)(op), x ∈ G, y ∈ G)
      |- isIdentityElement(G)(op)(op(x)(y)) <=> isIdentityElement(G)(op)(op(y)(x))
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G)
    val _1 = have(isIdentityElement(G)(op)(op(x)(y)) ==> isIdentityElement(G)(op)(op(y)(x))) by Restate.from(
      inverseCommutability
    )
    val _2 = have(isIdentityElement(G)(op)(op(y)(x)) ==> isIdentityElement(G)(op)(op(x)(y))) by Restate.from(
      inverseCommutability of (x := y, y := x)
    )
    have(thesis) by Tautology.from(_1, _2)
  }

  val inverseProperty = Theorem(
    (group(G)(op), x ∈ G) |- isIdentityElement(G)(op)(op(inverseOf(G)(op)(x))(x))
  ) {
    assume(group(G)(op), x ∈ G)
    val thm1 = have(isIdentityElement(G)(op)(op(x)(inverseOf(G)(op)(x)))) by Tautology.from(inverseProperty2)
    val thm1a = have(inverseOf(G)(op)(x) ∈ G) by Tautology.from(inverseStaysInGroup)
    val thm2 = have(isIdentityElement(G)(op)(op(inverseOf(G)(op)(x))(x))) by Tautology.from(thm1a, inverseCommutability of (x := x, y := inverseOf(G)(op)(x)), thm1)
  }

  val applyAssociativity = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G) |- (a === op(x)(op(y)(z))) <=> (a === op(op(x)(y))(z))
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)

    val assoc = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))))) by Tautology.from(
      associativity.definition,
      group.definition
    )
    thenHave(∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))) by InstantiateForall(x)
    thenHave(∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z))) by InstantiateForall(y)
    thenHave(op(x)(op(y)(z)) === op(op(x)(y))(z)) by InstantiateForall(z)

    thenHave(thesis) by Tautology.fromLastStep(
      equalityTransitivity of (x := a, y := op(x)(op(y)(z)), z := op(op(x)(y))(z)),
      equalityTransitivity of (x := a, y := op(op(x)(y))(z), z := op(x)(op(y)(z)))
    )
  }

  val identityProperty = Theorem(
    (group(G)(op), isIdentityElement(G)(op)(e), x ∈ G) |- ((op(e)(x) === x) /\ (op(x)(e) === x))
  ) {
    assume(group(G)(op), isIdentityElement(G)(op)(e), x ∈ G)
    have((e ∈ G) /\ (∀(y ∈ G, ((op(e)(y) === y) /\ (op(y)(e) === y))))) by Tautology.from(
      isIdentityElement.definition of (x := e)
    )
    thenHave(∀(y ∈ G, ((op(e)(y) === y) /\ (op(y)(e) === y)))) by Tautology 
    thenHave(thesis) by InstantiateForall(x)
  }

  val inverseCancelsOut = Theorem(
    (group(G)(op), x ∈ G, y ∈ G) |- op(inverseOf(G)(op)(x))(op(x)(y)) === y
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G)
    
    val inv = inverseOf(G)(op)(x)
    val e0 = op(inv)(x)
    val _1 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
      inverseProperty of (x := x)
    )

    val _2 = have(op(e0)(y) === y) by Tautology.from(
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
    (group(G)(op), x ∈ G) |- inverseOf(G)(op)(inverseOf(G)(op)(x)) === x
  ) {
    assume(group(G)(op), x ∈ G)
    
    val inv = inverseOf(G)(op)(x)
    val inv2 = inverseOf(G)(op)(inv)

    val e0 = op(inv)(x)
    val _1 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
      inverseProperty of (x := x)
    )

    val _2 = have(op(inv2)(op(inv)(x)) === x) by Tautology.from(
      inverseCancelsOut of (x := inv, y := x),
      inverseStaysInGroup of (x := x)
    )

    val _3 = have(inv2 ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := inv),
      inverseStaysInGroup of (x := x)
    )

    val _4 = have(op(inv2)(e0) === inv2) by Tautology.from(
      _1, _3,
      identityProperty of (e := e0, x := inv2)
    )

    have(thesis) by Tautology.from(
      equalityTransitivity of (x := x, y := op(inv2)(e0), z := inv2),
      _2, _4
    )
  }

  val applyInverseLeft = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G) |-
      (x === op(y)(z)) <=> (op(inverseOf(G)(op)(y))(x) === z)
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)
    
    val inv = inverseOf(G)(op)(y)    

    val leftImplies = have((x === op(y)(z)) |- (op(inverseOf(G)(op)(y))(x) === z)) subproof {
      assume(x === op(y)(z))
  
      val _1 = have(op(inv)(x) === op(inv)(op(y)(z))) by Tautology.from(congruence of (z := inv, x := x, y := op(y)(z)))

      val _2 = have(op(inv)(x) === op(op(inv)(y))(z)) by Tautology.from(
        _1,
        applyAssociativity of (a := op(inv)(x), x := inv, y := y, z := z),
        inverseStaysInGroup of (x := y)
      )
      val e0 = op(inv)(y)
      val _3 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
        group.definition,
        binaryOperationThm of (x := inv, y := y),
        inverseStaysInGroup of (x := y),
        inverseProperty of (x := y)
      )
      val _4 = have(op(e0)(z) === z) by Tautology.from(
        _3,
        identityProperty of (e := e0, x := z)
      )

      have(op(inv)(x) === z) by Tautology.from(
        equalityTransitivity of (x := op(inv)(x), y := op(e0)(z), z := z),
        _4,
        _2
      )
    }

    val rightImplies = have((op(inverseOf(G)(op)(y))(x) === z) |- (x === op(y)(z))) subproof {
      assume(op(inverseOf(G)(op)(y))(x) === z)
      val inv2 = inverseOf(G)(op)(inv)
      val _1 = have(op(inv2)(z) === x) by Tautology.from(
        leftImplies of (x := z, y := inv, z := x),
        inverseStaysInGroup of (x := y)
      )
      val _2 = have(inv2 === y) by Tautology.from(
        doubleInverse of (x := y)
      )

      have(y === inv2 |- op(y)(z) === x) by Substitution.Apply(y === inv2)(_1)
      thenHave(x === op(y)(z)) by Tautology.fromLastStep(_2)
    }

    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val applyInverseRight = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G) |- 
      (x === op(z)(y)) <=> (op(x)(inverseOf(G)(op)(y)) === z)
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)

    val inv = inverseOf(G)(op)(y)

    val leftImplies = have((x === op(z)(y)) |- (op(x)(inv) === z)) subproof {
      assume(x === op(z)(y))

      // apply congruence
      val _1 = have(op(x)(inv) === op(op(z)(y))(inv)) by Tautology.from(
        congruenceRight of (z := inv, x := x, y := op(z)(y))
      )

      // apply associativity
      val _2 = have(op(x)(inv) === op(z)(op(y)(inv))) by Tautology.from(
        _1,
        applyAssociativity of (a := op(x)(inv), x := z, y := y, z := inv),
        inverseStaysInGroup of (x := y)
      )

      // identify the identity element
      val e0 = op(y)(inv)
      val _3 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
        group.definition,
        binaryOperationThm of (x := y, y := inv),
        inverseStaysInGroup of (x := y),
        inverseProperty2 of (x := y)
      )
      val _4 = have(op(z)(e0) === z) by Tautology.from(
        _3,
        identityProperty of (e := e0, x := z)
      )

      // transitivity to get the final result
      have(op(x)(inv) === z) by Tautology.from(
        equalityTransitivity of (x := op(x)(inv), y := op(z)(e0), z := z),
        _4,
        _2
      )
    }

    val rightImplies = have((op(x)(inv) === z) |- (x === op(z)(y))) subproof {
      assume(op(x)(inv) === z)

      val inv2 = inverseOf(G)(op)(inv)
      val _1 = have(op(z)(inv2) === x) by Tautology.from(
        leftImplies of (x := z, y := inv, z := x),
        inverseStaysInGroup of (x := y)
      )
      val _2 = have(inv2 === y) by Tautology.from(
        doubleInverse of (x := y)
      )

      have(y === inv2 |- op(z)(y) === x) by Substitution.Apply(y === inv2)(_1)
      thenHave(x === op(z)(y)) by Tautology.fromLastStep(_2)
    }

    have(thesis) by Tautology.from(leftImplies, rightImplies)
  }

  val eliminateLeft = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G) |- (op(z)(x) === op(z)(y)) <=> (x === y)
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)

    val zx = op(z)(x)
    val _1 = have(zx ∈ G) by Tautology.from(
      binaryOperationThm of (x := z, y := x),
      group.definition
    )

    val invz = inverseOf(G)(op)(z)
    val _2 = have(invz ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := z)
    )

    val _3 = have((op(invz)(op(z)(x)) === y) <=> (op(z)(x) === op(z)(y))) by Tautology.from(
      applyInverseLeft of (x := op(z)(x), y := z, z := y),
      _1
    )

    val _4 = have((op(op(invz)(z))(x) === y) <=> (op(z)(x) === op(z)(y))) by Tautology.from(
      applyAssociativity of (a := y, x := invz, y := z, z := x),
      _2,
      _3
    )

    val e0 = op(invz)(z)
    val _5 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
      inverseProperty of (x := z)
    )

    val prod = op(e0)(x)
    have(e0 ∈ G) by Tautology.from(
      binaryOperationThm of (x := invz, y := z),
      group.definition,
      _2
    )
    val prodinG = thenHave(prod ∈ G) by Tautology.fromLastStep(
      binaryOperationThm of (x := e0, y := x),
      group.definition
    )

    val _6 = have(x === op(e0)(x)) by Tautology.from(
      _5, identityProperty of (e := e0, x := x)
    )
    val _7 = have((op(op(invz)(z))(x) === y) <=> (y === x)) by Tautology.from(
      _6,
      equalityTransitivity of (x := x, y := op(e0)(x), z := y),
      equalityTransitivity of (x := y, y := x, z := op(e0)(x)),
      prodinG
    )

    have(thesis) by Tautology.from(_7, _4)
  }

  val eliminateRight = Theorem(
    (group(G)(op), x ∈ G, y ∈ G, z ∈ G) |- (op(x)(z) === op(y)(z)) <=> (x === y)
  ) {
    assume(group(G)(op), x ∈ G, y ∈ G, z ∈ G)

    val xz = op(x)(z)
    val _1 = have(xz ∈ G) by Tautology.from(
      binaryOperationThm of (x := x, y := z),
      group.definition
    )

    val invz = inverseOf(G)(op)(z)
    val _2 = have(invz ∈ G) by Tautology.from(
      inverseStaysInGroup of (x := z)
    )

    val _3 = have((op(op(x)(z))(invz) === y) <=> (xz === op(y)(z))) by Tautology.from(
      applyInverseRight of (x := xz, y := z, z := y),
      _1
    )

    val _4 = have((op(x)(op(z)(invz)) === y) <=> (op(x)(z) === op(y)(z))) by Tautology.from(
      applyAssociativity of (a := y, x := x, y := z, z := invz),
      _2,
      _3
    )
    
    val e0 = op(z)(invz)
    val _5 = have(isIdentityElement(G)(op)(e0)) by Tautology.from(
      inverseProperty2 of (x := z)
    )

    val prod = op(x)(e0)
    have(e0 ∈ G) by Tautology.from(
      binaryOperationThm of (x := z, y := invz),
      group.definition,
      _2
    )
    val prodinG = thenHave(prod ∈ G) by Tautology.fromLastStep(
      binaryOperationThm of (x := x, y := e0),
      group.definition
    )

    val _6 = have(x === op(x)(e0)) by Tautology.from(
      _5, identityProperty of (e := e0, x := x)
    )
    val _7 = have((op(x)(op(z)(invz)) === y) <=> (y === x)) by Tautology.from(
      _6,
      equalityTransitivity of (x := x, y := op(x)(e0), z := y),
      equalityTransitivity of (x := y, y := x, z := op(x)(e0)),
      prodinG
    )

    have(thesis) by Tautology.from(_7, _4)
  }

  val identityOfIsIdentity = Theorem(
    (group(G)(op)) |- isIdentityElement(G)(op)(identityOf(G)(op))
  ) {
    assume(group(G)(op))
    val auxP = lambda(x, isIdentityElement(G)(op)(x))
    val e0 = identityOf(G)(op)

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