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

    val ker = DEF(λ(f, λ(G, λ(*, λ(H, λ(∘,
        { x ∈ G | isIdentityElement(H)(∘)(f(x)) }
    ))))))

    val kerProperty = Theorem(
        (x ∈ ker(f)(G)(*)(H)(∘))
        |- x ∈ G /\ isIdentityElement(H)(∘)(f(x))
    ) {
        assume(x ∈ ker(f)(G)(*)(H)(∘))
        val auxP = lambda(x, isIdentityElement(H)(∘)(f(x)))
        val subst = have(ker(f)(G)(*)(H)(∘) === { x ∈ G | auxP(x) }) by Tautology.from(ker.definition)
        have(x ∈ ker(f)(G)(*)(H)(∘)) by Tautology
        thenHave(x ∈ { x ∈ G | auxP(x) }) by Substitute(subst)
        thenHave(thesis) by Tautology.fromLastStep(
            Comprehension.membership of (x := x, y := G, φ := auxP)
        )
    }

    val kerIsSubset = Theorem(
        ker(f)(G)(*)(H)(∘) ⊆ G
    ) {
        val K = ker(f)(G)(*)(H)(∘)
        have(x ∈ K ==> x ∈ G) by Tautology.from(kerProperty)
        thenHave(∀(x ∈ K, x ∈ G)) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(subsetAxiom of (x := K, y := G, z := x))
    }

    val kerMembershipTest = Theorem(
        (x ∈ G, isIdentityElement(H)(∘)(f(x))) |- x ∈ ker(f)(G)(*)(H)(∘)
    ) {
        assume(x ∈ G, isIdentityElement(H)(∘)(f(x)))
        val K = ker(f)(G)(*)(H)(∘)
        val auxP = lambda(x, isIdentityElement(H)(∘)(f(x)))
        val subst = have(K === { x ∈ G | auxP(x) }) by Tautology.from(ker.definition) 
        have(x ∈ { x ∈ G | isIdentityElement(H)(∘)(f(x)) }) by Tautology.from(
            Comprehension.membership of (x := x, y := G, φ := auxP)
        )
        thenHave(x ∈ K) by Substitute(subst)
    }

    val eIsInKer = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- identityOf(G)(*) ∈ ker(f)(G)(*)(H)(∘)
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

    val kerIsNonEmpty = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- ker(f)(G)(*)(H)(∘) ≠ ∅
    ) {
        val K = ker(f)(G)(*)(H)(∘)
        have(thesis) by Tautology.from(
            EmptySet.setWithElementNonEmpty of (x := identityOf(G)(*), y := K),
            eIsInKer
        )
    }

    val kerIsClosedUnderOperation = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- binaryOperation(ker(f)(G)(*)(H)(∘))(*)
    ) {
        sorry
    }

    val kerIsClosedUnderInverse = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- inverseElement(ker(f)(G)(*)(H)(∘))(*)
    ) {
        sorry
    }

    val kerIsSubgroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- subgroup(ker(f)(G)(*)(H)(∘))(G)(*)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val K = ker(f)(G)(*)(H)(∘)
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
        |- group(ker(f)(G)(*)(H)(∘))(*)
    ) {
        val K = ker(f)(G)(*)(H)(∘)
        have(thesis) by Tautology.from(kerIsSubgroup, subgroup.definition of (H := K))
    }

    val kerIsNormalSubgroup = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- normalSubgroup(ker(f)(G)(*)(H)(∘))(G)(*)
    ) {
        sorry
    }