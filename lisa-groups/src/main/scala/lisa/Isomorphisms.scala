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
import lisa.maths.GroupTheory.QuotientGroup.{/}
import lisa.maths.GroupTheory.Homomorphisms.*
import lisa.maths.GroupTheory.Homomorphisms.{:::}
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

object Isomorphisms extends lisa.Main:
    extension (f: Expr[Ind]) {
        def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
    }

    val groupIsomorphism = DEF(λ(f, λ(G, λ(*, λ(H, λ(∘,
        (f ::: (G, *) -> (H, ∘)) /\
        bijective(f)(G)(H)
    )))))).printAs(args => {
        val f = args(0)
        val G = args(1)
        val opG = args(2)
        val H = args(3)
        val opH = args(4)
        s"$f : ($G, $opG) ≃> ($H, $opH)"
    })

    extension (f: Expr[Ind]) {
        infix def ::~(fType: ((Expr[Ind], Expr[Ind]), (Expr[Ind], Expr[Ind]))): Expr[Prop] = {
            val (g1, g2) = fType
            val G0 = g1._1
            val opG = g1._2
            val H0 = g2._1
            val opH = g2._2
            groupIsomorphism(f)(G0)(opG)(H0)(opH)
        }
    }

    val groupIsomorphic = DEF(λ(G, λ(*, λ(H, λ(∘,
        ∃(f, f ::~ (G, *) -> (H, ∘))
    ))))).printAs(args => {
        val G = args(0)
        val H = args(2)
        s"$G ≅ $H"
    })

    extension(g1: (Expr[Ind], Expr[Ind])) {
        infix def ≅(g2: (Expr[Ind], Expr[Ind])) = {
            val G = g1._1
            val opG = g1._2
            val H = g2._1
            val opH = g2._2
            groupIsomorphic(G)(opG)(H)(opH)
        }
    }

    val isomorphismProperty = Theorem(
        (f ::~ (G, *) -> (H, ∘), x ∈ G, y ∈ G)
        |- f(op(x, *, y)) === op(f(x), ∘, f(y))
    ) {
        have(thesis) by Tautology.from(
            groupIsomorphism.definition,
            homomorphismProperty
        )
    }

    val isomorphismExists = Theorem(
        (f ::~ (G, *) -> (H, ∘))
        |- (G, *) ≅ (H, ∘)
    ) {
        assume(f ::~ (G, *) -> (H, ∘))
        have(f ::~ (G, *) -> (H, ∘)) by Tautology
        thenHave(∃(f, f ::~ (G, *) -> (H, ∘))) by RightExists
        thenHave(thesis) by Tautology.fromLastStep(groupIsomorphic.definition)
    }

    val FITisomorphism = Lemma(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- { (x, cosetRep(G)(ker(f))(*)(x)) | x ∈ (G / ker(f)) } ::~ (G / ker(f), cosetOperation(G)(*)) -> (im(f), ∘)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val f0 = { (x, cosetRep(G)(ker(f))(*)(x)) | x ∈ (G / ker(f)) }
        val GK = G / ker(f)

        val _1 = have(functionOn(f0)(GK) /\ ∀(x ∈ GK, app(f0)(x) === cosetRep(G)(ker(f))(*)(x))) by Tautology.from(
            functionBuilder of (f := f0, A := GK, F := cosetRep(G)(ker(f))(*))
        )
        val _2 = have(function(f0) /\ (dom(f0) === GK)) by Tautology.from(_1, functionOnIffFunctionWithDomain of (f := f0, A := GK))
        
        val _2a = have(range(f0) === range(f)) subproof {
            sorry
        }
        
        have(f0 :: GK -> range(f0)) by Tautology.from(_1, functionOnIsFunctionBetweenRange of (f := f0, A := GK))
        thenHave(f0 :: GK -> range(f)) by Substitute(_2a)
        val _2b = thenHave(f0 :: GK -> im(f)) by Substitute(im.definition)
        
        val ** = cosetOperation(G)(*)
        have(ker(f) ◁ G) by Tautology.from(kerIsNormalSubgroup)
        val _3 = thenHave(group(G / ker(f))(**)) by Tautology.fromLastStep(
            quotientGroupIsGroup2 of (H := ker(f))
        )

        val _4 = have(group(im(f))(∘)) by Tautology.from(imIsGroup)

        have((x ∈ GK, y ∈ GK) |- f0(op(x, **, y)) === op(f0(x), ∘, f0(y))) subproof {
            sorry
        }

        thenHave(x ∈ GK |- y ∈ GK ==> (f0(op(x, **, y)) === op(f0(x), ∘, f0(y)))) by Restate
        thenHave(x ∈ GK |- ∀(y ∈ GK, (f0(op(x, **, y)) === op(f0(x), ∘, f0(y))))) by RightForall
        thenHave(x ∈ GK ==> ∀(y ∈ GK, (f0(op(x, **, y)) === op(f0(x), ∘, f0(y))))) by Restate
        thenHave(∀(x ∈ GK, ∀(y ∈ GK, (f0(op(x, **, y)) === op(f0(x), ∘, f0(y)))))) by RightForall
        val _5 = thenHave(f0 ::: (GK, **) -> (im(f), ∘)) by Tautology.fromLastStep(
            _3, _4, _2b,
            groupHomomorphism.definition of (f := f0, G := GK, * := **, H := im(f), ∘ := ∘)
        )

        have(range(f0) === im(f)) by Substitute(im.definition)(_2a)
        val _6 = thenHave(surjective(f0)(im(f))) by Substitute(surjective.definition of (f := f0, B := im(f)))
        
        have((x ∈ GK, y ∈ GK, f0(x) === f0(y)) |- x === y) subproof {
            sorry
        }
        thenHave(x ∈ GK |- y ∈ GK ==> ((f0(x) === f0(y)) ==> (x === y))) by Restate
        thenHave(x ∈ GK |- ∀(y ∈ GK, (f0(x) === f0(y)) ==> (x === y))) by RightForall
        thenHave(x ∈ GK ==> ∀(y ∈ GK, (f0(x) === f0(y)) ==> (x === y))) by Restate
        thenHave(∀(x ∈ GK, ∀(y ∈ GK, (f0(x) === f0(y)) ==> (x === y)))) by RightForall
        val _7 = thenHave(injective(f0)(GK)) by Tautology.fromLastStep(
            injective.definition of (f := f0, A := GK)
        )

        val _8 = have(bijective(f0)(GK)(im(f))) by Tautology.from(
            _2b, _6, _7, bijective.definition of (f := f0, A := GK, B := im(f))
        )
        
        have(f0 ::~ (GK, **) -> (im(f), ∘)) by Tautology.from(
            _5, _8, groupIsomorphism.definition of (f := f0, G := GK, * := **, H := im(f), ∘ := ∘)
        )
    }
    
    val firstIsomorphismTheorem = Theorem(
        (group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        |- (G / ker(f), cosetOperation(G)(*)) ≅ (im(f), ∘)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val f0 = { (x, cosetRep(G)(ker(f))(*)(x)) | x ∈ (G / ker(f)) }
        have(f0 ::~ (G / ker(f), cosetOperation(G)(*)) -> (im(f), ∘)) by Tautology.from(FITisomorphism)
        thenHave(∃(g, g ::~ (G / ker(f), cosetOperation(G)(*)) -> (im(f), ∘))) by RightExists
        thenHave(thesis) by Tautology.fromLastStep(
            groupIsomorphic.definition of (
                G := G / ker(f), 
                * := cosetOperation(G)(*), 
                H := im(f), 
                ∘ := ∘, 
                f := g
            )
        )
    }