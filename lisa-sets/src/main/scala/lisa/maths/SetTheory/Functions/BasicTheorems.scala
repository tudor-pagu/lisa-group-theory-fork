package lisa.maths.SetTheory.Functions

import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef._

import Function._

/**
 * This file contains proofs of basic properties about functions.
 *
 * TODO: Add constant functions
 * TODO: Add Cantor's theorem (probably in a distinct file, when we get to cardinals).
 */
object BasicTheorems extends lisa.Main {

  private val S = variable[Ind]
  private val P, Q = variable[Ind >>: Prop]

  extension (f: Expr[Ind]) {

    /**
     * Syntax for `f(x)`.
     */
    def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  ////////////////////////////////////////////////////////////////////////////
  section("Membership")

  /**
   * Theorem --- If `f` is a function and `z ∈ f` then `z` is a pair.
   */
  val inversion = Theorem(
    (function(f), z ∈ f) |- (z === (fst(z), snd(z)))
  ) {
    assume(z ∈ f)
    have(f :: A -> B |- (z === (fst(z), snd(z)))) by Tautology.from(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenIsRelation of (R := f, X := A, Y := B),
      Relations.BasicTheorems.inversion of (R := f)
    )
    thenHave(∃(B, f :: A -> B) |- (z === (fst(z), snd(z)))) by LeftExists
    thenHave(∃(A, ∃(B, f :: A -> B)) |- (z === (fst(z), snd(z)))) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `(x, y) ∈ f` then `x ∈ dom(f)`.
   *
   * Equivalent to [[Relations.BasicTheorems.domainMembership]].
   */
  val domainMembership = Theorem(
    (x, y) ∈ f |- x ∈ dom(f)
  ) {
    have(thesis) by Restate.from(Relations.BasicTheorems.domainMembership of (R := f))
  }

  /**
   * Theorem --- If `g ⊆ f` then `dom(g) ⊆ dom(f)`.
   */
  val domainMonotonic = Theorem(
    g ⊆ f |- dom(g) ⊆ dom(f)
  ) {
    have(x ∈ { fst(z) | z ∈ g } <=> ∃(z ∈ g, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(g)` = thenHave(x ∈ dom(g) <=> ∃(z ∈ g, fst(z) === x)) by Substitute(dom.definition of (R := g))
    thenHave((∀(z, z ∈ g ==> (z ∈ f)), x ∈ dom(g)) |- ∃(z ∈ f, fst(z) === x)) by Tableau
    thenHave((g ⊆ f, x ∈ dom(g)) |- x ∈ dom(f)) by Substitute(
      ⊆.definition of (x := g, y := f),
      `x ∈ dom(g)` of (g := f)
    )
    thenHave(g ⊆ f |- x ∈ dom(g) ==> (x ∈ dom(f))) by Restate
    thenHave(g ⊆ f |- ∀(x, x ∈ dom(g) ==> (x ∈ dom(f)))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (x := dom(g), y := dom(f)))
  }

  /**
   * Theorem --- If `(x, y) ∈ f` then `y ∈ range(f)`.
   *
   * Equivalent to [[Relations.BasicTheorems.rangeMembership]].
   */
  val rangeMembership = Theorem(
    (x, y) ∈ f |- y ∈ range(f)
  ) {
    have(thesis) by Restate.from(Relations.BasicTheorems.rangeMembership of (R := f))
  }

  /**
   * Theorem --- If `g ⊆ f` then `range(g) ⊆ range(f)`.
   */
  val rangeMonotonic = Theorem(
    g ⊆ f |- range(g) ⊆ range(f)
  ) {
    have(y ∈ { snd(z) | z ∈ g } <=> ∃(z ∈ g, snd(z) === y)) by Replacement.apply
    val `y ∈ range(g)` = thenHave(y ∈ range(g) <=> ∃(z ∈ g, snd(z) === y)) by Substitute(range.definition of (R := g))
    thenHave((∀(z, z ∈ g ==> (z ∈ f)), y ∈ range(g)) |- ∃(z ∈ f, snd(z) === y)) by Tableau
    thenHave((g ⊆ f, y ∈ range(g)) |- y ∈ range(f)) by Substitute(
      ⊆.definition of (y := g, y := f),
      `y ∈ range(g)` of (g := f)
    )
    thenHave(g ⊆ f |- y ∈ range(g) ==> (y ∈ range(f))) by Restate
    thenHave(g ⊆ f |- ∀(y, y ∈ range(g) ==> (y ∈ range(f)))) by RightForall
    thenHave(thesis) by Substitute(⊆.definition of (y := range(g), y := range(f)))
  }

  /////////////////////////////////////////////////////////////////////////
  section("Functions from A to B")

  /**
   * Lemma --- If `f : A -> B` then `f` is a function.
   */
  val functionBetweenIsFunction = Theorem(
    f :: A -> B |- function(f)
  ) {
    assume(f :: A -> B)
    thenHave(∃(B, f :: A -> B)) by RightExists
    thenHave(∃(A, ∃(B, f :: A -> B))) by RightExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Lemma --- If `f : A -> B` then `f` is a function on `A`.
   */
  val functionBetweenIsFunctionOn = Theorem(
    f :: A -> B |- functionOn(f)(A)
  ) {
    assume(f :: A -> B)
    thenHave(∃(B, f :: A -> B)) by RightExists
    thenHave(thesis) by Substitute(functionOn.definition)
  }

  /**
   * Theorem --- If `f : A -> B` then `dom(f) = A`.
   */
  val functionBetweenDomain = Theorem(
    f :: A -> B |- dom(f) === A
  ) {
    assume(f :: A -> B)

    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition)

    // We show that `A ⊆ dom(f)`; the other direction is guaranteed by [[relationBetweenDomain]].
    have(A ⊆ dom(f)) subproof {
      have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
      thenHave(x ∈ A |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
      val existence = thenHave(x ∈ A |- ∃(y, (x, y) ∈ f)) by Tautology.fromLastStep(
        Quantifiers.existsOneImpliesExists of (P := λ(y, (x, y) ∈ f))
      )

      have((x, y) ∈ f |- x ∈ dom(f)) by Tautology.from(Relations.BasicTheorems.domainMembership of (R := f))
      thenHave(∃(y, (x, y) ∈ f) |- x ∈ dom(f)) by LeftExists

      have(x ∈ A ==> x ∈ dom(f)) by Tautology.from(
        lastStep,
        existence,
        `x ∈ dom(f)`
      )
      thenHave(∀(x, x ∈ A ==> x ∈ dom(f))) by RightForall
      thenHave(thesis) by Substitute(⊆.definition of (x := A, y := dom(f)))
    }
    thenHave(thesis) by Tautology.fromLastStep(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenDomain of (R := f, X := A, Y := B),
      Subset.doubleInclusion of (x := A, y := dom(f))
    )
  }

  /**
   * Theorem --- If `f : A -> B` then `range(f) ⊆ B`.
   *
   * Consequence of [[relationBetweenRange]].
   */
  val functionBetweenRange = Theorem(
    f :: A -> B |- range(f) ⊆ B
  ) {
    have(thesis) by Tautology.from(
      functionBetween.definition,
      Relations.BasicTheorems.relationBetweenRange of (R := f, X := A, Y := B)
    )
  }

  ////////////////////////////////////////////////////////////////////////////
  section("Function application")

  /**
   * Theorem --- If `f` is a function then `f(x) = y` if and only if `(x, y) ∈ f`.
   */
  val appDefinition = Theorem(
    (function(f), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f
  ) {
    have(f :: A -> B |- ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
    thenHave((f :: A -> B, x ∈ A) |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
    thenHave((f :: A -> B, x ∈ A) |- (ε(y, (x, y) ∈ f) === y) <=> (x, y) ∈ f) by Tautology.fromLastStep(
      Quantifiers.existsOneEpsilonUniqueness of (P := λ(y, (x, y) ∈ f))
    )
    thenHave((f :: A -> B, x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by Substitute(
      app.definition,
      functionBetweenDomain
    )
    thenHave((∃(B, f :: A -> B), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by LeftExists
    thenHave((∃(A, ∃(B, f :: A -> B)), x ∈ dom(f)) |- (f(x) === y) <=> (x, y) ∈ f) by LeftExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `f` is a function and `x ∈ dom(f)` then `f(x) ∈ range(f)`.
   */
  val appInRange = Theorem(
    (function(f), x ∈ dom(f)) |- f(x) ∈ range(f)
  ) {
    assume(function(f))
    assume(x ∈ dom(f))

    have((x, f(x)) ∈ f) by Tautology.from(appDefinition of (y := f(x)))
    thenHave(thesis) by Tautology.fromLastStep(
      Relations.BasicTheorems.rangeMembership of (R := f, y := f(x))
    )
  }

  /**
   * Theorem --- If `f : A -> B` and `x ∈ A` then `f(x) ∈ B`.
   *
   * Special case of [[appInRange]].
   */
  val appTyping = Theorem(
    (f :: A -> B, x ∈ A) |- (f(x) ∈ B)
  ) {
    assume(f :: A -> B)
    assume(x ∈ A)
    have(x ∈ dom(f)) by Congruence.from(functionBetweenDomain)
    thenHave(f(x) ∈ range(f)) by Tautology.fromLastStep(
      functionBetweenIsFunction,
      appInRange
    )
    thenHave(thesis) by Tautology.fromLastStep(
      functionBetweenRange,
      Subset.membership of (x := range(f), y := B, z := f(x))
    )
  }

  ////////////////////////////////////////////////////////////////////////
  section("Functions on A")

  /**
   * Lemma --- If `f` is a function on `A` then `f` is a function.
   */
  val functionOnIsFunction = Theorem(
    functionOn(f)(A) |- function(f)
  ) {
    assume(functionOn(f)(A))
    thenHave(∃(B, f :: A -> B)) by Substitute(functionOn.definition)
    thenHave(∃(A, ∃(B, f :: A -> B))) by RightExists
    thenHave(thesis) by Substitute(function.definition)
  }

  /**
   * Theorem --- If `f` is a function on `A` then `dom(f) = A`.
   *
   * Consequence of [[functionBetweenDomain]].
   */
  val functionOnDomain = Theorem(
    functionOn(f)(A) |- dom(f) === A
  ) {
    have(∃(B, f :: A -> B) |- dom(f) === A) by LeftExists(functionBetweenDomain)
    thenHave(thesis) by Substitute(functionOn.definition)
  }

  /**
   * Theorem --- `f` is a function on `A` <=> `f` is a function with `dom(f) = A`.
   */
  val functionOnIffFunctionWithDomain = Theorem(
    functionOn(f)(A) <=> function(f) /\ (dom(f) === A)
  ) {
    val `==>` = have(functionOn(f)(A) |- function(f) /\ (dom(f) === A)) by RightAnd(functionOnIsFunction, functionOnDomain)

    val `<==` =
      have((f :: C -> D, dom(f) === A) |- dom(f) === C) by Tautology.from(functionBetweenDomain of (A := C, B := D))
      thenHave((f :: C -> D, dom(f) === A) |- (f :: A -> D)) by Congruence
      thenHave((f :: C -> D, dom(f) === A) |- ∃(B, f :: A -> B)) by RightExists
      thenHave((f :: C -> D, dom(f) === A) |- functionOn(f)(A)) by Substitute(functionOn.definition)
      thenHave((∃(D, f :: C -> D), dom(f) === A) |- functionOn(f)(A)) by LeftExists
      thenHave((∃(C, ∃(D, f :: C -> D)), dom(f) === A) |- functionOn(f)(A)) by LeftExists
      thenHave((function(f), dom(f) === A) |- functionOn(f)(A)) by Substitute(function.definition)

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- If `f` and `g` are functions on `A` such that `f(x) = g(x)`
   * for all `x ∈ A`, then `f` equals `g`.
   */
  val extensionality = Theorem(
    (
      functionOn(f)(A),
      functionOn(g)(A),
      ∀(x ∈ A, f(x) === g(x))
    ) |- (f === g)
  ) {
    assume(functionOn(f)(A))
    assume(functionOn(g)(A))
    assume(∀(x ∈ A, f(x) === g(x)))

    thenHave(x ∈ A |- f(x) === g(x)) by InstantiateForall(x)
    val `f(x)` = thenHave(x ∈ dom(f) |- f(x) === g(x)) by Substitute(functionOnDomain)

    // Take z ∈ f. We show that z ∈ g.
    val `==>` = have(z ∈ f |- z ∈ g) subproof {
      assume(z ∈ f)

      // 1. z = (fst(z), snd(z))
      val step1 = have(z === (fst(z), snd(z))) by Tautology.from(inversion, functionOnIsFunction)

      // 2. (fst(z), snd(z)) ∈ f
      val step2 = thenHave((fst(z), snd(z)) ∈ f) by Congruence

      // 3. fst(z) ∈ dom(f)
      val step3 = thenHave(fst(z) ∈ dom(f)) by Tautology.fromLastStep(domainMembership of (x := fst(z), y := snd(z)))

      // 4. f(fst(z)) = snd(z)
      val step4 = have(f(fst(z)) === snd(z)) by Tautology.from(
        appDefinition of (x := fst(z), y := snd(z)),
        functionOnIsFunction,
        step3,
        step2
      )

      // 5. f(fst(z)) = g(fst(z))
      val step5 = have(f(fst(z)) === g(fst(z))) by Tautology.from(
        `f(x)` of (x := fst(z)),
        step3
      )

      // 6. g(fst(z)) = snd(z)
      val step6 = have(g(fst(z)) === snd(z)) by Congruence.from(
        step4,
        step5
      )

      // 7. fst(z) ∈ dom(g)
      val step7 = have(fst(z) ∈ dom(g)) by Congruence.from(
        step3,
        functionOnDomain of (f := f),
        functionOnDomain of (f := g)
      )

      // 8. (fst(z), snd(z)) ∈ g
      val step8 = have((fst(z), snd(z)) ∈ g) by Congruence.from(
        appDefinition of (f := g, x := fst(z), y := snd(z)),
        functionOnIsFunction of (f := g),
        step7,
        step6
      )

      // 9. z ∈ g
      thenHave(thesis) by Substitute(step1)
    }

    /**
     * The reverse implication is obtained by symmetry.
     */
    val `<==` = have(z ∈ g |- z ∈ f) by Tautology.from(`==>` of (f := g, g := f))

    have(z ∈ f <=> z ∈ g) by Tautology.from(`==>`, `<==`)
    thenHave(thesis) by Extensionality
  }

  /////////////////////////////////////////////////////////////////////////
  section("Subsets, extensions")

  /**
   * Theorem --- If `f` is a function and `g ⊆ f` then `g` is also a function.
   */
  val subset = Theorem(
    (function(f), g ⊆ f) |- function(g)
  ) {
    assume(function(f), g ⊆ f)

    // First, we show that `g` is a relation
    val `g is relation between dom(g) and range(g)` = have(f :: A -> B |- relationBetween(g)(dom(g))(range(g))) subproof {
      assume(f :: A -> B)
      have(relationBetween(f)(A)(B)) by Tautology.from(functionBetween.definition)
      thenHave(relation(g)) by Tautology.fromLastStep(
        Relations.BasicTheorems.subsetIsRelationBetween of (R := f, S := g, X := A, Y := B),
        Relations.BasicTheorems.relationBetweenIsRelation of (R := g, X := A, Y := B)
      )
      thenHave(thesis) by Tautology.fromLastStep(
        Relations.BasicTheorems.relationBetweenDomainRange of (R := g)
      )
    }

    // Second, we show that for any `x ∈ dom(g)` we have `(x, y) ∈ f <=> (x, y) ∈ g`.
    have(x ∈ dom(g) |- (x, y) ∈ f <=> (x, y) ∈ g) subproof {
      assume(x ∈ dom(g))

      val `==>` = have((x, y) ∈ f |- (x, y) ∈ g) subproof {
        assume((x, y) ∈ f)

        have(x ∈ { fst(z) | z ∈ g } <=> ∃(z ∈ g, fst(z) === x)) by Replacement.apply
        thenHave(x ∈ dom(g) <=> ∃(z ∈ g, fst(z) === x)) by Substitute(dom.definition of (R := g))
        val _1 = thenHave(∃(z ∈ g, fst(z) === x)) by Tautology
        val auxP = lambda(z, z ∈ g /\ (fst(z) === x))
        val z0 = ε(z, auxP(z))
        val _2 = have(z0 ∈ g /\ (fst(z0) === x)) by Tautology.from(
          _1, Quantifiers.existsEpsilon of (x := z, P := auxP)
        )
        have(∀(z, z ∈ g ==> z ∈ f)) by Tautology.from(
          subsetAxiom of (x := g, y := f)
        )
        thenHave(z0 ∈ g ==> z0 ∈ f) by InstantiateForall(z0)
        val _3 = thenHave(z0 ∈ f) by Tautology.fromLastStep(_2)

        val xeq = have(x === fst(z0)) by Tautology.from(_2)
        val y0 = snd(z0)
        have(z0 === (fst(z0), snd(z0))) by Tautology.from(_3, inversion of (z := z0))
        val _4 = thenHave(z0 === (x, y0)) by Substitute(xeq)
        have(z0 ∈ f) by Tautology.from(_3)
        val _5 = thenHave((x, y0) ∈ f) by Substitute(_4)

        val _6 = have(x ∈ dom(f)) by Tautology.from(
          domainMonotonic,
          Subset.membership of (z := x, x := dom(g), y := dom(f))
        )

        val _7 = have(f(x) === y0) by Tautology.from(
          _5, _6, appDefinition of (y := y0)
        )
        val _8 = have(f(x) === y) by Tautology.from(
          _6, appDefinition
        )
        val _9 = thenHave(y0 === y) by Substitute(_7)
        have(z0 === (x, y0)) by Tautology.from(_4)
        val _10 = thenHave(z0 === (x, y)) by Substitute(_9)

        have(z0 ∈ g) by Tautology.from(_2)
        thenHave(thesis) by Substitute(_10)
      }

      val `<==` = have((x, y) ∈ g |- (x, y) ∈ f) by Tautology.from(Subset.membership of (z := (x, y), x := g, y := f))

      have(thesis) by Tautology.from(`==>`, `<==`)
    }
    val equivalence = thenHave(x ∈ dom(g) |- ∀(y, (x, y) ∈ f <=> (x, y) ∈ g)) by RightForall

    // Finally, since `f` is functional on `dom(f)` it is functional on `dom(g)` as well
    // We use the equivalence shown above to replace `(x, y) ∈ f` with `(x, y) ∈ g`.
    have(f :: A -> B |- ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(functionBetween.definition)
    thenHave((f :: A -> B, x ∈ A) |- ∃!(y, (x, y) ∈ f)) by InstantiateForall(x)
    thenHave((f :: A -> B, x ∈ dom(f)) |- ∃!(y, (x, y) ∈ f)) by Substitute(functionBetweenDomain)
    thenHave((f :: A -> B, x ∈ dom(g)) |- ∃!(y, (x, y) ∈ f)) by Tautology.fromLastStep(
      domainMonotonic,
      Subset.membership of (z := x, x := dom(g), y := dom(f))
    )
    thenHave(f :: A -> B |- x ∈ dom(g) ==> ∃!(y, (x, y) ∈ g)) by Tautology.fromLastStep(
      equivalence,
      Quantifiers.uniqueExistentialEquivalenceDistribution of (P := λ(y, (x, y) ∈ f), Q := λ(y, (x, y) ∈ g))
    )
    thenHave(f :: A -> B |- ∀(x ∈ dom(g), ∃!(y, (x, y) ∈ g))) by RightForall

    // We put everything together and show that `g : dom(g) -> range(g)`.
    have(f :: A -> B |- (g :: dom(g) -> range(g))) by Tautology.from(
      functionBetween.definition of (f := g, A := dom(g), B := range(g)),
      lastStep,
      `g is relation between dom(g) and range(g)`
    )

    thenHave(f :: A -> B |- ∃(B, g :: dom(g) -> B)) by RightExists
    thenHave(f :: A -> B |- ∃(A, ∃(B, g :: A -> B))) by RightExists
    thenHave(∃(B, f :: A -> B) |- ∃(A, ∃(B, g :: A -> B))) by LeftExists
    thenHave(∃(A, ∃(B, f :: A -> B)) |- ∃(A, ∃(B, g :: A -> B))) by LeftExists
    thenHave(thesis) by Substitute(function.definition, function.definition of (f := g))
  }

  /**
   * Theorem --- If `f, g` are functions such that `g ⊆ f`, then
   * `g(x) = y` implies that `f(x) = y`.
   */
  val extensionApp = Theorem(
    (function(f), function(g), g ⊆ f, x ∈ dom(g)) |- (g(x) === y) ==> (f(x) === y)
  ) {
    assume(function(f))
    assume(function(g))
    assume(g ⊆ f)
    assume(x ∈ dom(g))

    have((g(x) === y) <=> (x, y) ∈ g) by Tautology.from(appDefinition of (f := g))
    thenHave((g(x) === y) ==> ((x, y) ∈ f)) by Tautology.fromLastStep(
      Subset.membership of (z := (x, y), x := g, y := f)
    )
    thenHave(thesis) by Tautology.fromLastStep(
      appDefinition,
      Subset.membership of (z := x, x := dom(g), y := dom(f)),
      domainMonotonic
    )
  }

  /**
   * Theorem --- If `f` is a function and `x ∉ dom(f)` then `f ∪ {(x, y)}` is a function
   * on `dom(f) ∪ {x}`.
   */
  val pointExtension = Theorem(
    (function(f), x ∉ dom(f)) |- functionOn(f ∪ singleton((x, y)))(dom(f) ∪ singleton(x))
  ) {
    assume(function(f))
    assume(x ∉ dom(f))

    sorry
  }

}
