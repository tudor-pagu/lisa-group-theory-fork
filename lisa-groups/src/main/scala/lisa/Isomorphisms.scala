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
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.maths.GroupTheory.Homomorphisms.groupHomomorphism
import lisa.maths.GroupTheory.Utils.functionBuilder
import lisa.maths.GroupTheory.Homomorphisms.homomorphismProperty
import lisa.maths.GroupTheory.Homomorphisms.kerIsNormalSubgroup
import lisa.maths.GroupTheory.QuotientGroup.quotientGroupMembership

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

    // f(gRep) === f(g) where gRep is a rep of the g*K coset, K being the kernel
    val cosetRepWithKernelIsUniqueAfterF= Theorem(
      ((x ∈ G), f ::: (G, *) -> (H, ∘), group(G)(*), group(H)(∘)) |- 
      f(cosetRep(G)(ker(f))(*)(leftCoset(x)(*)(ker(f)))) === f(x)
      ) {
        assume(x ∈ G, f ::: (G, *) -> (H, ∘), group(G)(*), group(H)(∘))
        val K = ker(f)
        val gK = leftCoset(x)(*)(K)
        val gRep = cosetRep(G)(K)(*)(gK)
        val _1 = have(∃(k ∈ K, gRep === op(x, * , k) )) by Tautology.from(
          cosetRepIdentityChoice of (H:=K, g:= x), kerIsNormalSubgroup
          )
        val kAux = lambda(k, (k ∈ K) /\ (gRep === op(x, * , k)))
        val k0 = ε(k, kAux(k))
        val k0Thm = have(kAux(k0)) by Tautology.from(Quantifiers.existsEpsilon of (x := k, P:=kAux), _1)

        val _2 = have(gRep === (op(x, *, k0))) by Tautology.from(k0Thm)

        have(f(gRep) === f(gRep)) by Tautology
        val _3 = thenHave(f(gRep) === f(op(x, *, k0))) by Substitute(_2)
        val _4a = have(k0 ∈ G) by Tautology.from(k0Thm, kerProperty of (x := k0))
        val _4 = have( f(op(x, *, k0)) === op(f(x),∘,f(k0)) ) by Tautology.from(homomorphismProperty of (y:=k0), _3, _4a)
        val _5 = have(isIdentityElement(H)(∘)(f(k0))) by Tautology.from(kerProperty of (x := k0), k0Thm)
        val _6a = have(f(x) ∈ H) by Tautology.from(homomorphismAppTyping)
        val _6 = have(op(f(x),∘, f(k0)) === f(x)) by Tautology.from(_5, identityProperty of (e:=f(k0), G:=H, * := ∘,x:=f(x)), _6a)
        have(f(gRep) === f(x)) by Congruence.from(_3,_4,_5,_6)
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
        |- { (x, f(cosetRep(G)(ker(f))(*)(x))) | x ∈ (G / ker(f)) } ::~ (G / ker(f), cosetOperation(G)(*)) -> (im(f), ∘)
    ) {
        assume(group(G)(*), group(H)(∘), f ::: (G, *) -> (H, ∘))
        val f0 = { (x, f(cosetRep(G)(ker(f))(*)(x))) | x ∈ (G / ker(f)) }

        val K = ker(f)
        val GK = G / ker(f)

        val _1 = have(functionOn(f0)(GK) /\ ∀(x ∈ GK, app(f0)(x) === f(cosetRep(G)(ker(f))(*)(x)))) by Tautology.from(
            functionBuilder of (f := f0, A := GK, F := lambda(x, f(cosetRep(G)(ker(f))(*)(x))))
        )
        val _2 = have(function(f0) /\ (dom(f0) === GK)) by Tautology.from(_1, functionOnIffFunctionWithDomain of (f := f0, A := GK))

        val fDomainStep = have(dom(f) === G) by Tautology.from(groupHomomorphism.definition, functionBetweenDomain of (A := G, B := H))

        val fIsAFunction = have(function(f)) by Tautology.from(
            groupHomomorphism.definition, 
            functionBetweenIsFunction of (A := G, B := H)
        )

        val _2a_1 = have( x ∈ G |- ∃(y ∈ GK, f(x) === f0(y))) subproof {
          assume(x ∈ G)
          val gK = leftCoset(x)(*)(K)
          val gRep = cosetRep(G)(K)(*)(gK)
          val gkThm = have(gK ∈ GK) by Tautology.from(quotientGroupMembershipTest of (x := gK, y := x, H := K))

          val _g1 = have((gRep ∈ G) /\ (gK === leftCoset(gRep)(*)(K))) by Tautology.from(quotientGroupMembership of (H:=K, x:=gK),gkThm, kerIsNormalSubgroup)
          val goal1 = have(f(gRep) === f(x)) by Tautology.from(cosetRepWithKernelIsUniqueAfterF)

          val _s1a = have(∀(x, (x ∈ GK) ==> (app(f0)(x) === f(cosetRep(G)(ker(f))(*)(x))))) by Tautology.from(_1)
          val _s1b = thenHave( (gK ∈ GK) ==> (app(f0)(gK) === f(gRep))) by InstantiateForall(gK)
          val _s2 = have(f0(gK) === f(gRep)) by Tautology.from(_s1b, gkThm)
          val _s3 = have(f0(gK) === f(x)) by Congruence.from(_s2, goal1)
          val _s4 = have((gK ∈ GK) /\ (f0(gK) === f(x))) by Tautology.from(_s3, gkThm)
          val _s5 = thenHave(∃(y,(y ∈ GK) /\ (f0(y) === f(x)))) by RightExists
          have(∃(y ∈ GK,  (f0(y) === f(x)))) by Tautology.from(_s5)
        }

        val _2a_2 = have(y ∈ GK |- ∃(x ∈ G, f(x) === f0(y))) subproof {
          assume(y ∈ GK)
          val _s1a = have(∀(y, (y ∈ GK) ==> (app(f0)(y) === f(cosetRep(G)(ker(f))(*)(y))))) by Tautology.from(_1)
          sorry
        }

        val _2a = have(range(f0) === range(f)) subproof {
          val _1 = have(dom(f) === G) by Tautology.from(fDomainStep)
          val _1_2 = have(dom(f0) === GK) by Tautology.from(_2)
          val goal1a = have((x ∈ G) ==> ∃(y ∈ GK, f(x) === f0(y))) by Tautology.from(_2a_1)
          val goal1 = thenHave(∀ (x, (x ∈ G) ==> ∃(y ∈ GK, f(x) === f0(y)))) by RightForall
          val _2_ = thenHave(∀(x ∈ dom(f), ∃(y ∈ GK, f(x) === f0(y)))) by Substitute(_1)
          val _3 = thenHave(∀(x ∈ dom(f), ∃(y ∈ dom(f0), f(x) === f0(y)))) by Substitute(_1_2)

          val inclusion1 = have(range(f) ⊆ range(f0)) by Tautology.from(
            fIsAFunction, _2, _3, fDomainStep, _2,
            imageInclusion of (f := f, g := f0)
          )
          
          val goal2 = have(∀ (y ∈ GK, ∃ (x ∈ G, f(x) === f0(y)))) by Sorry
          val _4 = thenHave(∀ (y ∈ dom(f0), ∃ (x ∈ G, f(x) === f0(y)))) by Substitute(_1_2)
          val _5 = thenHave(∀ (y ∈ dom(f0), ∃ (x ∈ dom(f), f(x) === f0(y)))) by Substitute(_1)
  
          val inclusion2 = have(range(f0) ⊆ range(f)) by Tautology.from(
            _2, fIsAFunction, _5, _2, fDomainStep,
            imageInclusion of (f := f0, g := f)
          )
          
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
        val f0 = { (x, f(cosetRep(G)(ker(f))(*)(x))) | x ∈ (G / ker(f)) }
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
