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

import lisa.maths.SetTheory.Functions.Predef.{_}
import lisa.maths.SetTheory.Functions.Function.{bijective, surjective, injective, ::, app, apply, function, functionBetween}
import lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
import lisa.maths.SetTheory.Functions.Operations.Restriction
import lisa.maths.SetTheory.Functions.BasicTheorems.*
import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.Pair
// import lisa.maths.SetTheory.Relations.Predef.{_, given}
import lisa.maths.Quantifiers.∃!

object Homomorphisms extends lisa.Main:

    extension (f: Expr[Ind]) {
        def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
    }

    val groupHomomorphism = DEF(λ(f, λ(G, λ(*, λ(H, λ(∘,
        group(G)(*) /\
        group(H)(∘) /\
        (f :: G -> H) /\
        ∀(x ∈ G, ∀(y ∈ G, 
            f(op(x, *, y)) === op(f(x), ∘, f(y))
        ))
    )))))).printAs(args => {
        val f = args(0)
        val G = args(1)
        val opG = args(2)
        val H = args(3)
        val opH = args(4)
        s"$f : ($G, $opG) -> ($H, $opH)"
    })

    extension (f: Expr[Ind]) {
        infix def :::(fType: ((Expr[Ind], Expr[Ind]), (Expr[Ind], Expr[Ind]))): Expr[Prop] = {
            val (g1, g2) = fType
            val G0 = g1._1
            val opG = g1._2
            val H0 = g2._1
            val opH = g2._2
            groupHomomorphism(f)(G0)(opG)(H0)(opH)
        }
    }

    val homomorphismProperty = Theorem(
        (f ::: (G, *) -> (H, ∘), x ∈ G, y ∈ G)
        |- f(op(x, *, y)) === op(f(x), ∘, f(y))
    ) {
        assume(f ::: (G, *) -> (H, ∘), x ∈ G, y ∈ G)
        have(
            (f :: G -> H) /\ 
            ∀(x ∈ G, ∀(y ∈ G, f(op(x, *, y)) === op(f(x), ∘, f(y))))
        ) by Tautology.from(groupHomomorphism.definition)
        thenHave(∀(x ∈ G, ∀(y ∈ G, f(op(x, *, y)) === op(f(x), ∘, f(y))))) by Tautology
        thenHave(x ∈ G |- ∀(y ∈ G, f(op(x, *, y)) === op(f(x), ∘, f(y)))) by InstantiateForall(x)
        thenHave((x ∈ G, y ∈ G) |- f(op(x, *, y)) === op(f(x), ∘, f(y))) by InstantiateForall(y)
        thenHave(thesis) by Tautology
    }

    val homomorphismAppTyping = Theorem(
        (f ::: (G, *) -> (H, ∘), x ∈ G)
        |- f(x) ∈ H
    ) {
        assume(f ::: (G, *) -> (H, ∘), x ∈ G)
        have(f :: G -> H) by Tautology.from(groupHomomorphism.definition)
        thenHave(f(x) ∈ H) by Tautology.fromLastStep(appTyping of (A := G, B := H))
    }

    val homomorphismAppIdentity = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘), isIdentityElement(G)(*)(e))
        |- isIdentityElement(H)(∘)(f(e))
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘), isIdentityElement(G)(*)(e))
        val _1 = have(isIdentityElement(G)(*)(e)) by Tautology
        val einG = have(e ∈ G) by Tautology.from(_1, isIdentityElement.definition of (x := e))
        val feinH = have(f(e) ∈ H) by Tautology.from(homomorphismAppTyping of (x := e), einG)
        val _2 = have(op(e, *, e) === e) by Tautology.from(
            _1, identityIsIdempotent of (e := e)
        )

        val _3 = have(f(op(e, *, e)) === op(f(e), ∘, f(e))) by Tautology.from(
            homomorphismProperty of (x := e, y := e), einG
        )
        val _4 = have(f(e) === op(f(e), ∘, f(e))) by Congruence.from(_2, _3)
        val _5 = have(isIdentityElement(H)(∘)(f(e))) by Tautology.from(
            _4, identityIsIdempotent of (e := f(e), G := H, * := ∘),
            einG, feinH
        )
    }

    val kernel = DEF(λ(f, λ(G, λ(*, λ(H, λ(∘,
        { x ∈ G | isIdentityElement(H)(∘)(f(x)) }
    )))))).printAs( args => {
        val f = args(0)
        s"ker($f)"
    })

    private [GroupTheory] def ker(f: Expr[Ind]) = {
        kernel(f)(G)(*)(H)(∘)
    }

    val kerProperty = Theorem(
        (x ∈ ker(f))
        |- x ∈ G /\ isIdentityElement(H)(∘)(f(x))
    ) {
        assume(x ∈ ker(f))
        val auxP = lambda(x, isIdentityElement(H)(∘)(f(x)))
        val subst = have(ker(f) === { x ∈ G | auxP(x) }) by Tautology.from(kernel.definition)
        have(x ∈ ker(f)) by Tautology
        thenHave(x ∈ { x ∈ G | auxP(x) }) by Substitute(subst)
        thenHave(thesis) by Tautology.fromLastStep(
            Comprehension.membership of (x := x, y := G, φ := auxP)
        )
    }

    val kerIsSubset = Theorem(
        ker(f) ⊆ G
    ) {
        val K = ker(f)
        have(x ∈ K ==> x ∈ G) by Tautology.from(kerProperty)
        thenHave(∀(x ∈ K, x ∈ G)) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(subsetAxiom of (x := K, y := G, z := x))
    }

    val kerMembershipTest = Theorem(
        (x ∈ G, isIdentityElement(H)(∘)(f(x))) |- x ∈ ker(f)
    ) {
        assume(x ∈ G, isIdentityElement(H)(∘)(f(x)))
        val K = ker(f)
        val auxP = lambda(x, isIdentityElement(H)(∘)(f(x)))
        val subst = have(K === { x ∈ G | auxP(x) }) by Tautology.from(kernel.definition) 
        have(x ∈ { x ∈ G | isIdentityElement(H)(∘)(f(x)) }) by Tautology.from(
            Comprehension.membership of (x := x, y := G, φ := auxP)
        )
        thenHave(x ∈ K) by Substitute(subst)
    }

    val eIsInKer = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- identityOf(G)(*) ∈ ker(f)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val eG = identityOf(G)(*)
        val eH = f(eG)

        val _1 = have(isIdentityElement(G)(*)(eG)) by Tautology.from(identityOfIsIdentity)
        val eGinG = have(eG ∈ G) by Tautology.from(_1, isIdentityElement.definition of (x := eG))
        val _2 = have(isIdentityElement(H)(∘)(f(eG))) by Tautology.from(_1, homomorphismAppIdentity of (e := eG))
        have(thesis) by Tautology.from(
            eGinG, _2, kerMembershipTest of (x := eG)
        )
    }

    val identityElementIsInKer = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘), isIdentityElement(G)(*)(e))
        |- e ∈ ker(f)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘), isIdentityElement(G)(*)(e))
        val K = ker(f)
        val e0 = identityOf(G)(*)
        val subst = have(e === e0) by Tautology.from(
            identityIsUnique of (x := e, y := e0),
            identityOfIsIdentity
        )
        have(e0 ∈ K) by Tautology.from(eIsInKer)
        thenHave(e ∈ K) by Substitute(subst)
    }

    val kerIsNonEmpty = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- ker(f) ≠ ∅
    ) {
        val K = ker(f)
        have(thesis) by Tautology.from(
            EmptySet.setWithElementNonEmpty of (x := identityOf(G)(*), y := K),
            eIsInKer
        )
    }

    val kerIsClosedUnderOperation = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- binaryOperation(ker(f))(*)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val K = ker(f)
        have((x ∈ K, y ∈ K) |- op(x, *, y) ∈ K) subproof {
            assume(x ∈ K, y ∈ K)
            val _1 = have(x ∈ G /\ isIdentityElement(H)(∘)(f(x))) by Tautology.from(kerProperty)
            val _2 = have(y ∈ G /\ isIdentityElement(H)(∘)(f(y))) by Tautology.from(kerProperty of (x := y))

            val fyinH = have(f(y) ∈ H) by Tautology.from(_2, homomorphismAppTyping of (x := y))
            val _3 = have(f(op(x, *, y)) === op(f(x), ∘, f(y))) by Tautology.from(_1, _2, homomorphismProperty)
            val _4 = have(op(f(x), ∘, f(y)) === f(y)) by Tautology.from(
                _1, fyinH, identityProperty of (e := f(x), x := f(y), G := H, * := ∘),
            )
            val _5 = have(isIdentityElement(H)(∘)(f(y))) by Tautology.from(_2)
            val _6 = have(isIdentityElement(H)(∘)(f(op(x, *, y)))) by Congruence.from(_3, _4, _5)
            val _7 = have(op(x, *, y) ∈ G) by Tautology.from(
                _1, _2, binaryOperationThm, group.definition
            )
            have(thesis) by Tautology.from(
                _6, _7, kerMembershipTest of (x := op(x, *, y))
            )
        }
        thenHave((x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K) by Restate
        thenHave(∀(x, ∀(y, (x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K))) by Generalize
        thenHave(thesis) by Tautology.fromLastStep(
            kerIsSubset,
            group.definition,
            binaryOperationTestSubset of (H := K)
        )
    }

    val kerIsClosedUnderInverse = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- inverseElement(ker(f))(*)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val K = ker(f)
        val xi = inverseOf(G)(*)(x)
        val _1 = have(x ∈ G |- isIdentityElement(G)(*)(op(x, *, xi))) by Tautology.from(inverseProperty2)
        val _2 = have(isIdentityElement(G)(*)(op(x, *, xi)) |- isIdentityElement(K)(*)(op(x, *, xi))) subproof {
            val e0 = op(x, *, xi)
            assume(isIdentityElement(G)(*)(e0))
            have(e0 ∈ K) by Tautology.from(identityElementIsInKer of (e := e0))
            thenHave(isIdentityElement(K)(*)(e0)) by Tautology.fromLastStep(
                identityElementTestSubset of (H := K, e := e0),
                kerIsSubset
            )
        }
        val _3 = have(x ∈ K |- xi ∈ K) subproof {
            assume(x ∈ K)
            val e0 = op(x, *, xi)
            val xinG = have(x ∈ G) by Tautology.from(
                kerIsSubset, Subset.membership of (z := x, x := K, y := G)
            )
            val xiinG = have(xi ∈ G) by Tautology.from(
                xinG, inverseStaysInGroup
            )
            val step1 = have(isIdentityElement(H)(∘)(f(x))) by Tautology.from(kerProperty)
            val step2 = have(f(xi) ∈ H) by Tautology.from(homomorphismAppTyping of (x := xi), xiinG)
            
            val step3 = have(op(f(x), ∘, f(xi)) === f(xi)) by Tautology.from(
                step1, step2, identityProperty of (e := f(x), x := f(xi), G := H, * := ∘)
            )
            val step4 = have(f(e0) === op(f(x), ∘, f(xi))) by Tautology.from(
                homomorphismProperty of (x := x, y := xi),
                xinG, xiinG
            )
            val step5 = have(f(e0) === f(xi)) by Congruence.from(step3, step4)

            val step6 = have(isIdentityElement(G)(*)(e0)) by Tautology.from(xinG, inverseProperty2)
            val step7 = have(e0 ∈ K) by Tautology.from(step6, identityElementIsInKer of (e := e0))
            val step8 = have(isIdentityElement(H)(∘)(f(e0))) by Tautology.from(
                step7, kerProperty of (x := e0)
            )
            val step9 = thenHave(isIdentityElement(H)(∘)(f(xi))) by Substitute(step5)
            have(thesis) by Tautology.from(
                xiinG, step9,
                kerMembershipTest of (x := xi)
            )
        }
        val _4 = have(x ∈ K |- x ∈ G) by Tautology.from(
            kerIsSubset,
            Subset.membership of (z := x, x := K, y := G)
        )
        have(x ∈ K |- xi ∈ K /\ isIdentityElement(K)(*)(op(x, *, xi))) by Tautology.from(
            _1, _2, _3, _4
        )
        thenHave(x ∈ K |- ∃(y ∈ K, isIdentityElement(K)(*)(op(x, *, y)))) by RightExists
        thenHave(x ∈ K ==> ∃(y ∈ K, isIdentityElement(K)(*)(op(x, *, y)))) by Restate
        thenHave(∀(x ∈ K, ∃(y ∈ K, isIdentityElement(K)(*)(op(x, *, y))))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(inverseElement.definition of (G := K))
    }

    val kerIsSubgroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- ker(f) ≤ G
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val K = ker(f)
        have(thesis) by Tautology.from(
            kerIsNonEmpty,
            kerIsSubset,
            kerIsClosedUnderInverse,
            kerIsClosedUnderOperation,
            subgroupTestTwoStep of (H := K)
        )
    }

    val kerIsGroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- group(ker(f))(*)
    ) {
        val K = ker(f)
        have(thesis) by Tautology.from(kerIsSubgroup, subgroup.definition of (H := K))
    }

    val kerIsNormalSubgroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- ker(f) ◁ G
    ) {
        sorry
    }

    val im = DEF(λ(f, range(f)))

    val homomorphismImageIsSubgroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- im(f) ≤ (H, ∘)
    ) {
        sorry
    }