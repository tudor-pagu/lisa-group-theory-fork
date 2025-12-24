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
import lisa.maths.GroupTheory.Utils.equalityTransitivity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

object Subgroups extends lisa.Main:

  val subgroupTestTwoStep = Theorem(
    (group(G)(*), H ≠ ∅, H ⊆ G, binaryOperation(H)(*), inverseElement(H)(*))
      |- subgroup(H)(G)(*)
  ) {
    assume(group(G)(*), H ≠ ∅, H ⊆ G, binaryOperation(H)(*), inverseElement(H)(*))
    val thm1 = have(binaryOperation(H)(*) /\ inverseElement(H)(*)) by Restate
    val subthm1 = have(identityElement(H)(*)) subproof {
      //  val identityElement = ∃(x, isIdentityElement(G)(*)(x)))

      val obs1 = have(∃(h, h ∈ H)) by Tautology.from(EmptySet.nonEmptyHasElement of (x := H, y := h))
      val obs2 = have(∀(x, x ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(*)(op(x, *, y))))) by Tautology.from(inverseElement.definition of (G := H, * := *))
      val obs3 = thenHave(h ∈ H ==> ∃(y ∈ H, isIdentityElement(H)(*)(op(h, *, y)))) by InstantiateForall(h)
      val obs4 = thenHave(h ∈ H |- ∃(y ∈ H, isIdentityElement(H)(*)(op(h, *, y)))) by Restate
      val obs5 = have(h ∈ H |- h ∈ H /\ (∃(y ∈ H, isIdentityElement(H)(*)(op(h, *, y))))) by Tautology.from(obs4)
      val obs6 = thenHave(h ∈ H |- ∃(x, x ∈ H /\ (∃(y ∈ H, isIdentityElement(H)(*)(op(x, *, y)))))) by RightExists
      val obs7 = thenHave(h ∈ H |- ∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(*)(op(x, *, y)))))) by Restate
      val obs8 = thenHave(∃(h, h ∈ H) |- ∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(*)(op(x, *, y)))))) by LeftExists
      val obs9 = have(∃(x ∈ H, (∃(y ∈ H, isIdentityElement(H)(*)(op(x, *, y)))))) by Tautology.from(obs1, obs8)
      val obs10 = have(∃(x, (∃(y, isIdentityElement(H)(*)(op(x, *, y)))))) by Tautology.from(obs9)

      val obs20 = have(isIdentityElement(H)(*)(op(x, *, y)) |- isIdentityElement(H)(*)(op(x, *, y))) by Tautology
      val obs21 = thenHave(isIdentityElement(H)(*)(op(x, *, y)) |- ∃(z, isIdentityElement(H)(*)(z))) by RightExists
      val obs22 = thenHave(∃(y, isIdentityElement(H)(*)(op(x, *, y))) |- ∃(z, isIdentityElement(H)(*)(z))) by LeftExists
      val obs23 = thenHave(∃(x, ∃(y, isIdentityElement(H)(*)(op(x, *, y)))) |- ∃(z, isIdentityElement(H)(*)(z))) by LeftExists
      val obs24 = have(∃(z, isIdentityElement(H)(*)(z))) by Tautology.from(obs23, obs10)
      val obs25 = have(identityElement(H)(*)) by Tautology.from(obs24, identityElement.definition of (G := H, * := *))
    }

    val subthm2 = have((x ∈ H, y ∈ H, z ∈ H) |- op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)) subproof {
      assume(x ∈ H, y ∈ H, z ∈ H)
      val obs1 = have(H ⊆ G) by Restate
      val obs2 = have(x ∈ G) by Tautology.from(Subset.membership of (z := x, x := H, y := G), obs1)
      val obs3 = have(y ∈ G) by Tautology.from(Subset.membership of (z := y, x := H, y := G), obs1)
      val obs4 = have(z ∈ G) by Tautology.from(Subset.membership of (z := z, x := H, y := G), obs1)

      val obs5 = have(associativity(G)(*)) by Tautology.from(group.definition)
      val obs7 = have(op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)) by Tautology.from(associativityThm, obs2, obs3, obs4, obs5)
    }

    val subthm3 = have(associativity(H)(*)) subproof {
      have((x ∈ H, y ∈ H, z ∈ H) |- op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)) by Restate.from(subthm2)
      val obs1 = thenHave(((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))) by Restate
      thenHave(∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))) by RightForall
      thenHave(∀(y, ∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z))))) by RightForall
      val obs2 = thenHave(∀(x, ∀(y, ∀(z, ((x ∈ H) /\ (y ∈ H) /\ (z ∈ H)) ==> (op(x, *, op(y, *, z)) === op(op(x, *, y), *, z)))))) by RightForall
      have(associativity(H)(*)) by Tautology.from(obs2, associativityAlternateForm of (G := H, * := *))
    }
    val thm2 = have(group(H)(*)) by Tautology.from(group.definition of (G := H, * := *), subthm1, subthm3, thm1)
    val thm3 = have(subgroup(H)(G)(*)) by Tautology.from(subgroup.definition of (G := G, H := H, * := *), thm2)
  }

  val elementInSubgroupMeansItsInGroup = Theorem(
    (group(G)(*), subgroup(H)(G)(*), x ∈ H) |- x ∈ G
  ) {
    assume(group(G)(*), subgroup(H)(G)(*), x ∈ H)

    // From subgroup definition, we have H ⊆ G
    val step1 = have(H ⊆ G) by Tautology.from(subgroup.definition)

    // Apply subset axiom: H ⊆ G means ∀(z, (z ∈ H) ==> (z ∈ G))
    val step2 = have(∀(z, (z ∈ H) ==> (z ∈ G))) by Tautology.from(
      step1,
      Subset.subsetAxiom of (x := H, y := G)
    )

    // Instantiate with x
    val step3 = thenHave((x ∈ H) ==> (x ∈ G)) by InstantiateForall(x)

    have(x ∈ G) by Tautology.from(step3)
  }

  val groupHasTheSameIdentityAsSubgroup = Theorem(
    (group(G)(*), subgroup(H)(G)(*), isIdentityElement(H)(*)(e)) |- isIdentityElement(G)(*)(e)
  ) {
    assume(group(G)(*), subgroup(H)(G)(*), isIdentityElement(H)(*)(e))
    
    val step1 = have(group(H)(*)) by Tautology.from(subgroup.definition)
    
    val step2 = have(e ∈ H) by Tautology.from(
      isIdentityElement.definition of (G := H, x := e)
    )
    
    val step3 = have(e ∈ G) by Tautology.from(
      elementInSubgroupMeansItsInGroup of (x := e),
      step2
    )
    
    val step4a = have(∀(h ∈ H, (op(e, *, h) === h) /\ (op(h, *, e) === h))) by Tautology.from(
      isIdentityElement.definition of (G := H, x := e)
    )
    val step4b = have((e ∈ H) ==> ((op(e, *, e) === e) /\ (op(e, *, e) === e))) by InstantiateForall(e)(step4a)
    val step4 = have(op(e, *, e) === e) by Tautology.from(step4b, step2)
    
    val invH = inverseOf(G)(*)(e)
    val step4c = have(invH ∈ G) by Tautology.from(
      inverseStaysInGroup of (G := G, * := *, x := e),
      step3
    )
    
    val step5 = have(op(invH, *, op(e, *, e)) === op(invH, *, e)) by Tautology.from(
      congruence of (G := G, * := *, x := op(e, *, e), y := e, z := invH),
      step4
    )
    
    val eG = identityOf(G)(*)
    val step6a = have(isIdentityElement(G)(*)(op(invH, *, e))) by Tautology.from(
      inverseProperty of (G := G, * := *, x := e),
      step3
    )
    val step6b = have(∃(z, isIdentityElement(G)(*)(z))) by Tautology.from(
      group.definition,
      identityElement.definition of (G := G)
    )
    val eGDef = have(eG === ε(z, isIdentityElement(G)(*)(z))) by Tautology.from(
      identityOf.definition of (G := G, * := *)
    )
    val eGEps = have(isIdentityElement(G)(*)(ε(z, isIdentityElement(G)(*)(z)))) by Tautology.from(
      step6b,
      Quantifiers.existsEpsilon of (x := z, P := lambda(z, isIdentityElement(G)(*)(z)))
    )
    val eGEq = eG === ε(z, isIdentityElement(G)(*)(z))
    val eGThmA = have(eGEq |- isIdentityElement(G)(*)(eG)) by Substitution.Apply(eGEq)(eGEps)
    val eGThm = have(isIdentityElement(G)(*)(eG)) by Tautology.from(eGThmA, eGDef)
    
    val step6 = have(op(invH, *, e) === eG) by Tautology.from(
      identityIsUnique of (x := op(invH, *, e), y := eG),
      step6a,
      eGThm
    )
    
    val step7 = have(op(invH, *, op(e, *, e)) === eG) by Tautology.from(
      equalityTransitivity of (x := op(invH, *, op(e, *, e)), y := op(invH, *, e), z := eG),
      step5,
      step6
    )
    
    val assocG = have(associativity(G)(*)) by Tautology.from(group.definition)
    val step8 = have(op(op(invH, *, e), *, e) === eG) by Tautology.from(
      equalityTransitivity of (x := op(op(invH, *, e), *, e), y := op(invH, *, op(e, *, e)), z := eG),
      associativityThm of (x := invH, y := e, z := e),
      assocG,
      step4c,
      step3,
      step7
    )
    
    val step9Eq = op(invH, *, e) === eG
    val step9a = have(step9Eq |- op(op(invH, *, e), *, e) === op(eG, *, e)) by Substitution.Apply(step9Eq)(
      have(op(eG, *, e) === op(eG, *, e)) by Restate
    )
    val step9 = have(op(eG, *, e) === eG) by Tautology.from(
      equalityTransitivity of (x := op(eG, *, e), y := op(op(invH, *, e), *, e), z := eG),
      step9a,
      step6,
      step8
    )
    
    val step10a = have(isIdentityElement(G)(*)(eG) |- ∀(a ∈ G, (op(eG, *, a) === a) /\ (op(a, *, eG) === a))) by Tautology.from(
      isIdentityElement.definition of (G := G, x := eG)
    )
    val step10b = have(isIdentityElement(G)(*)(eG) |- (e ∈ G) ==> ((op(eG, *, e) === e) /\ (op(e, *, eG) === e))) by InstantiateForall(e)(step10a)
    val step10c = have(op(eG, *, e) === e) by Tautology.from(step10b, eGThm, step3)
    val step10 = have(e === eG) by Tautology.from(
      equalityTransitivity of (x := e, y := op(eG, *, e), z := eG),
      step10c,
      step9
    )
    
    val step11Eq = e === eG
    val step11 = have(step11Eq |- isIdentityElement(G)(*)(e)) by Substitution.Apply(step11Eq)(eGThm)
    have(thesis) by Tautology.from(step11, step10)
  }

  val subgroupHasTheSameIdentity = Theorem(
    (group(G)(*), subgroup(H)(G)(*), isIdentityElement(G)(*)(e)) |- isIdentityElement(H)(*)(e)
  ) {
    assume(group(G)(*), subgroup(H)(G)(*), isIdentityElement(G)(*)(e))
    // T.P. (e ∈ H) /\ (∀(y ∈ H, ((op(e, *, y) === y) /\ (op(y, *, e) === y))))

    // H is a group, so it has inverse elements
    val step1 = have(group(H)(*)) by Tautology.from(subgroup.definition)
    val step2 = have(inverseElement(H)(*)) by Tautology.from(step1, group.definition of (G := H))

    // H is non-empty (has at least one element)
    val step3 = have(identityElement(H)(*)) by Tautology.from(step1, group.definition of (G := H))

    val step4 = have(∃(e, isIdentityElement(H)(*)(e))) by Tautology.from(
      step3,
      identityElement.definition of (G := H)
    )
    val eH = identityOf(H)(*)
    val eHDef = have(eH === ε(e, isIdentityElement(H)(*)(e))) by Tautology.from(
      identityOf.definition of (G := H, * := *)
    )
    val eHEps = have(isIdentityElement(H)(*)(ε(e, isIdentityElement(H)(*)(e)))) by Tautology.from(
      step4,
      Quantifiers.existsEpsilon of (x := e, P := lambda(e, isIdentityElement(H)(*)(e)))
    )
    val eHEq = eH === ε(e, isIdentityElement(H)(*)(e))
    val eHThmA = have(eHEq |- isIdentityElement(H)(*)(eH)) by Substitution.Apply(eHEq)(eHEps)
    val eHThm = have(isIdentityElement(H)(*)(eH)) by Tautology.from(eHThmA, eHDef)

    val eHThm2 = have(isIdentityElement(G)(*)(eH)) by Tautology.from(
      groupHasTheSameIdentityAsSubgroup of (e := eH),
      eHThm
    )

    val step5 = have(eH === e) by Tautology.from(
      identityIsUnique of (x := eH, y := e),
      eHThm2
    )
    val step6Eq = eH === e
    val step6 = have(step6Eq |- isIdentityElement(H)(*)(e)) by Substitution.Apply(step6Eq)(eHThm)
    have(thesis) by Tautology.from(step6, step5)
  }

  val identityInSubgroupIsTheSame = Theorem(
    (group(G)(*), subgroup(H)(G)(*), isIdentityElement(H)(*)(x), isIdentityElement(G)(*)(y)) |- x === y
  ) {
    assume(group(G)(*), subgroup(H)(G)(*), isIdentityElement(H)(*)(x), isIdentityElement(G)(*)(y))
    have(isIdentityElement(G)(*)(x)) by Tautology.from(
        groupHasTheSameIdentityAsSubgroup of (e := x)
    )
    thenHave(thesis) by Tautology.fromLastStep(
        identityIsUnique of (x := x, y := y)
    )
  }

  val identityOfInSubgroup = Theorem(
    (group(G)(*), subgroup(H)(G)(*)) |- identityOf(G)(*) === identityOf(H)(*)
  ) {
    assume(group(G)(*), subgroup(H)(G)(*))
    val e1 = identityOf(H)(*)
    val e2 = identityOf(G)(*)
    have(thesis) by Tautology.from(
        identityOfIsIdentity,
        identityOfIsIdentity of (G := H),
        subgroup.definition,
        identityInSubgroupIsTheSame of (x := e1, y := e2)
    )
  }

  val inverseInSubgroupIsTheSame = Theorem(
    (group(G)(*), subgroup(H)(G)(*), x ∈ H) |- inverseOf(H)(*)(x) === inverseOf(G)(*)(x)
  ) {
    assume(group(G)(*), subgroup(H)(G)(*), x ∈ H)
    
    val invh = inverseOf(H)(*)(x)
    val invg = inverseOf(G)(*)(x)

    have(invh ∈ H) by Tautology.from(
        inverseStaysInGroup of (G := H),
        subgroup.definition
    )
    val invhinG = thenHave(invh ∈ G) by Tautology.fromLastStep(
        elementInSubgroupMeansItsInGroup of (x := invh)
    )
    val xinG = have(x ∈ G) by Tautology.from(
        elementInSubgroupMeansItsInGroup
    )
    val invginG = have(invg ∈ G) by Tautology.from(
        inverseStaysInGroup,
        xinG
    )
    val eh = op(invh, *, x)
    val eg = op(invg, *, x)
    val _1 = have(isIdentityElement(H)(*)(eh)) by Tautology.from(
        inverseProperty of (G := H),
        subgroup.definition
    )
    val _2 = have(isIdentityElement(G)(*)(eg)) by Tautology.from(
        inverseProperty,
        xinG
    )

    val _3 = have(eh === eg) by Tautology.from(_1, _2, identityInSubgroupIsTheSame of (x := eh, y := eg))

    val _4 = thenHave(op(invh, *, x) === op(invg, *, x)) by Tautology
    thenHave(thesis) by Tautology.fromLastStep(
        invhinG, xinG, invginG,
        eliminateRight of (x := invh, y := invg, z := x)
    )
  }