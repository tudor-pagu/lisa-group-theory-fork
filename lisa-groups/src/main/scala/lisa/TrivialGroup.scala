// package lisa.maths.GroupTheory

// import lisa.maths.SetTheory.Base.Predef.{_, given}
// import Symbols._

// import lisa.kernel.proof.RunningTheoryJudgement._
// import lisa.maths.SetTheory.Base.Symbols._
// import lisa.maths.Quantifiers
// import lisa.automation.Substitution
// import lisa.maths.SetTheory.Functions.Function.bijective
// import lisa.maths.SetTheory.Base.EmptySet
// import lisa.maths.SetTheory.Base.Singleton
// import lisa.maths.SetTheory.Base.Subset
// import lisa.Main

// import lisa.automation.Congruence
// import lisa.automation.Substitution.{Apply => Substitute}
// import lisa.automation.Tableau
// import lisa.utils.prooflib.BasicStepTactic.RightForall
// import lisa.maths.GroupTheory.Groups.*
// import lisa.maths.GroupTheory.Subgroups.*
// import lisa.maths.GroupTheory.Cosets.*
// import lisa.maths.GroupTheory.Utils.equalityTransitivity
// import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

//   /*
//    * The most simple group:
//    * G = {x}, op(x,x) = x
//    *
//    */
// object TrivialGroup extends lisa.Main:
//   private val x = variable[Ind]
//   private val y = variable[Ind]
//   private val z = variable[Ind]

//   private val e = constant[Ind]("e")

//   addSymbol(e)

//   private val G = singleton(e)
//   // x * y = e
//   private val star = DEF(λ(x, λ(y, e)))

//   // prove that this simple structure is indeed
//   // a group
//   val trivialGroupHasBinaryOperation = Theorem(
//     () |- Groups.binaryOperation(G)(star)
//   ) {
//     val thm2 = have(star(x)(y) === e) by Tautology.from(star.definition)
//     val thm3 = have(star(x)(y) ∈ G) by Tautology.from(thm2, Singleton.membership of (x := e, y := star(x)(y)))
//     val thm4 = have(x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G) by Tautology.from(thm3)
//     thenHave(∀(y, x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G)) by RightForall
//     val thm5 = thenHave(∀(x, ∀(y, x ∈ G /\ y ∈ G ==> star(x)(y) ∈ G))) by RightForall
//     val thm6 = have(binaryOperation(G)(star)) by Tautology.from(thm5, binaryOperation.definition of (Symbols.G := G, Symbols.op := star))
//   }

//   val everyPairIsE = Theorem(
//     star(x)(e) === e
//   ) {
//     have(star(x)(e) === e) by Tautology.from(star.definition of (y := e))
//   }

//   val eIsIdentity = Theorem(
//     () |- Groups.isIdentityElement(G)(star)(e)
//   ) {
//     val sub1 = have((x ∈ G) |- (star(x)(e) === x) /\ (star(e)(x) === x)) subproof {
//       assume(x ∈ G)
//       val thm1 = have(star(x)(e) === e) by Tautology.from(star.definition of (y := e))
//       val thm2 = have(star(e)(x) === e) by Tautology.from(star.definition of (x := e, y := x))
//       val thm3 = have(e === x) by Tautology.from(Singleton.membership of (x := e, y := x))
//       val thm4 = have((star(x)(e) === e) /\ (e === x)) by Tautology.from(thm3, thm1)
//       val thm5 = have((star(x)(e) === x)) by Tautology.from(thm4, Utils.equalityTransitivity of (Utils.x := star(x)(e), Utils.y := e, Utils.z := x))
//       val thm6 = have(star(e)(x) === x) by Tautology.from(thm2, thm3, Utils.equalityTransitivity of (Utils.x := star(e)(x), Utils.y := e, Utils.z := x))
//       val thm7 = have((star(e)(x) === x) /\ (star(x)(e) === x)) by Tautology.from(thm5, thm6)
//     }
//     val thm1 = have((x ∈ G) ==> ((star(x)(e) === x) /\ (star(e)(x) === x))) by Tautology.from(sub1)
//     val thm2 = thenHave(∀(x, (x ∈ G) ==> ((star(x)(e) === x) /\ (star(e)(x) === x)))) by RightForall
//     val thm3 = have(∀(x ∈ G, ((star(x)(e) === x) /\ (star(e)(x) === x)))) by Tautology.from(thm2)
//     val thm4 = have(e ∈ G /\ ∀(x ∈ G, ((star(x)(e) === x) /\ (star(e)(x) === x)))) by Tautology.from(thm2, Singleton.membership of (x := e, y := e))
//     val thm5 = have(Groups.isIdentityElement(G)(star)(e)) by Tautology.from(thm4, Groups.isIdentityElement.definition of (Symbols.G := G, Symbols.op := star, x := e))
//   }

//   val trivialGroupHasIdentityElement = Theorem(
//     () |- Groups.identityElement(G)(star)
//   ) {
//     val thm5 = have(Groups.isIdentityElement(G)(star)(e)) by Restate.from(eIsIdentity)
//     val thm6 = thenHave(∃(x, Groups.isIdentityElement(G)(star)(x))) by RightExists
//     val thm7 = have(Groups.identityElement(G)(star)) by Tautology.from(thm6, Groups.identityElement.definition of (Symbols.G := G, Symbols.op := star))
//   }

//   val trivialGroupIsNotEmpty = Theorem(
//     () |- ∃(x, x ∈ G)
//   ) {
//     have(e ∈ G) by Tautology.from(Singleton.membership of (x := e, y := e))
//     thenHave(∃(x, x ∈ G)) by RightExists
//   }

//   val trivialGroupHasInverse = Theorem(
//     () |- Groups.inverseElement(G)(star)
//   ) {
//     // val inverseElement = DEF(λ(G, λ(op, ∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(op)(op(x)(y)))))))
//     val subthm1 = have(y ∈ G |- Groups.inverseElement(G)(star)) subproof {
//       assume(y ∈ G)
//       val thm1 = have(e === star(x)(y)) by Tautology.from(star.definition)
//       val thm2 = have(isIdentityElement(G)(star)(star(x)(y))) by Tautology.from(
//         eIsIdentity,
//         Groups.identityGetsTransferredByCongruence of (Symbols.G := G, Symbols.op := star, x := e, y := star(x)(y)),
//         thm1
//       )
//       val thm3 = have(y ∈ G /\ isIdentityElement(G)(star)(star(x)(y))) by Tautology.from(thm2)
//       val thm4 = thenHave(∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y)))) by RightExists
//       val thm5 = have(x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y)))) by Tautology.from(thm4)
//       val thm6 = thenHave(∀(x, x ∈ G ==> ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y))))) by RightForall
//       val thm7 = thenHave(∀(x ∈ G, ∃(y ∈ G, isIdentityElement(G)(star)(star(x)(y))))) by Restate
//       val thm8 = have(Groups.inverseElement(G)(star)) by Tautology.from(thm7, Groups.inverseElement.definition of (Symbols.G := G, Symbols.op := star))
//     }

//     val thm1 = thenHave((y ∈ G) |- Groups.inverseElement(G)(star)) by Restate
//     val thm3 = thenHave(∃(y, y ∈ G) |- Groups.inverseElement(G)(star)) by LeftExists
//     val thm4 = thenHave((∃(x, x ∈ G)) |- Groups.inverseElement(G)(star)) by Restate
//     val thm6 = have(Groups.inverseElement(G)(star)) by Tautology.from(thm4, trivialGroupIsNotEmpty)
//   }

//   val trivialGroupIsAssociative = Theorem(
//     () |- Groups.associativity(G)(star)
//   ) {
//     // DEF(λ(G, λ(op, ∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, op(x)(op(y)(z)) === op(op(x)(y))(z)))))))
//     val thm1 = have(star(x)(star(y)(z)) === e) by Tautology.from(star.definition of (x := x, y := star(y)(z)))
//     val thm2 = have(star(star(x)(y))(z) === e) by Tautology.from(star.definition of (x := star(x)(y), y := z))
//     val thm3 = have(star(x)(star(y)(z)) === star(star(x)(y))(z)) by Tautology.from(thm1, thm2, Utils.equalityTransitivity of (x := star(x)(star(y)(z)), y := e, z := star(star(x)(y))(z)))

//     val thm4 = have(z ∈ G ==> (star(x)(star(y)(z)) === star(star(x)(y))(z))) by Tautology.from(thm3)
//     val thm5 = thenHave(∀(z, z ∈ G ==> (star(x)(star(y)(z)) === star(star(x)(y))(z)))) by RightForall
//     val thm6 = have(∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))) by Restate.from(thm5)

//     val thm7 = have(y ∈ G ==> ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))) by Tautology.from(thm6)
//     val thm8 = thenHave(∀(y, y ∈ G ==> ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by RightForall
//     val thm9 = have(∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by Restate.from(thm8)

//     val thm10 = have(x ∈ G ==> ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z)))) by Tautology.from(thm9)
//     val thm11 = thenHave(∀(x, x ∈ G ==> ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))))) by RightForall
//     val thm12 = have(∀(x ∈ G, ∀(y ∈ G, ∀(z ∈ G, star(x)(star(y)(z)) === star(star(x)(y))(z))))) by Restate.from(thm11)

//     val thm13 = have(Groups.associativity(G)(star)) by Tautology.from(thm12, Groups.associativity.definition of (Symbols.G := G, Symbols.op := star))
//   }

//   val trivialGroupIsGroup = Theorem(
//     () |- Groups.group(G)(star)
//   ) {
//     have(Groups.group(G)(star)) by Tautology.from(
//       trivialGroupHasBinaryOperation,
//       trivialGroupIsAssociative,
//       trivialGroupHasInverse,
//       trivialGroupHasIdentityElement,
//       Groups.group.definition of (Symbols.G := G, Symbols.op := star)
//     )
//   }

