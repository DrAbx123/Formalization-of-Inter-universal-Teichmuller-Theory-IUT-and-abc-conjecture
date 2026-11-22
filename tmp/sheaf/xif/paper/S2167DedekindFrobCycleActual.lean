import tmp.sheaf.xif.paper.S2132FrobCycleActual
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# S2167: the Dedekind--Frobenius cycle-type interface for psi_5 at 29

The S1987 proof of the l = 5 D5 large-image input uses the following arithmetic
fact: the Frobenius at 29 acts on the twelve pairs of nonzero 5-torsion points
with cycle type (10, 2), because the odd 5-division polynomial psi_5 factors
modulo 29 as an irreducible quadratic times an irreducible degree-ten factor.

This file separates the part that is actually available in Mathlib from the
exact missing bridge.

## What Mathlib does provide

The task premise that Mathlib has no Frobenius element is too pessimistic.
This Mathlib snapshot (Lean 4.32.2, mathlib rev 905b958) contains
Mathlib/RingTheory/Frobenius.lean, with

* AlgHom.IsArithFrobAt;
* IsArithFrobAt.exists_of_isInvariant;
* arithFrobAt, a choice of an arithmetic Frobenius at a prime with finite
  residue field;
* arithFrobAt_mem_stabilizer and isConj_arithFrobAt.

What Mathlib does not provide is any comparison between the cycle type of
arithFrobAt on the roots of a polynomial and the degrees of the irreducible
factors of its reduction modulo the prime.  That comparison is the missing
theorem below (DedekindFrobeniusCycleTypeTheorem).

## What is proved here

* The root-permutation and root-cycle-type vocabulary for an integral
  polynomial over a number field and a Galois automorphism.
* The precise general cycle-type interface, as a proposition.
* The corrected mod-29 product certificate from S2132 (the product with the
  scalar 4 forced by the leading coefficient).
* The concrete target is exactly S2132FrobInducesPairCycleType.

## Exact first missing

DedekindFrobeniusCycleTypeTheorem below.  For the concrete S2132 target one
also needs the standard transport from the Q-Frobenius to the F'-automorphism:
because F' and the 5-division field are linearly disjoint over Q (their
intersection is Q), the restriction map on Galois groups is surjective, so a
Q-Frobenius with cycle type (10, 2) lifts to an F'-automorphism with the same
cycle type.  This file records that transport as a comment, not as an
unproved Lean axiom.

A subtle point: the paper's factorization of psi_5 modulo 29 is over F_29,
while 29 is inert in Q(sqrt(-3)), which is a subfield of F'.  Hence a prime of
F' above 29 has residue field F_{29^2}, and the F_29 factorization is the
Q-level Frobenius computation, not a direct factorization over the residue
field of F'.  The linear-disjointness transfer above is therefore genuinely
needed; this is the precise reason S2132FrobInducesPairCycleType is not an
immediate corollary of the mod-29 certificate.

No sorry, admit, axiom, opaque declaration or native_decide is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

/-! ## 0. The Mathlib Frobenius API used below -/

#check @arithFrobAt
#check @IsArithFrobAt.exists_of_isInvariant
#check @IsArithFrobAt.arithFrobAt_mem_stabilizer

/-- The existence half of the Dedekind--Frobenius bridge is available in
Mathlib for the generic action of Gal(L/K) on the ring of integers: for every
prime P with finite residue field there is an arithmetic Frobenius at P.  What
is missing is the cycle-type comparison with the factorization of a polynomial
modulo P. -/
theorem S2167FrobeniusExists
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [Finite ((RingOfIntegers L) ⧸ P)] :
    ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P := by
  haveI : Algebra.IsInvariant (RingOfIntegers K) (RingOfIntegers L) Gal(L/K) := by
    refine ⟨fun b hb => ?_⟩
    have hb' : ∀ g : Gal(L/K),
        (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
          IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
         g • b : RingOfIntegers L) = b := by
      intro g
      rw [← show (g • b : RingOfIntegers L) =
        (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
          IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
         g • b : RingOfIntegers L) from by
        apply Subtype.ext
        change (g • (b : L)) = ((galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) g b : L)
        exact (algebraMap_galRestrict_apply (RingOfIntegers K) g b).symm]
      exact hb g
    exact (Algebra.isInvariant_of_isGalois (RingOfIntegers K) K L (RingOfIntegers L)).1 b hb'
  exact IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) Gal(L/K) P

/-! ## 1. Factor degrees and cycle types -/

/-- The multiset of degrees of the irreducible factors of a polynomial. -/
noncomputable def factorDegrees {K : Type} [Field K] (f : K[X]) : Multiset Nat :=
  letI := Classical.decEq K
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree

/-- A permutation has cycle type m. -/
def HasCycleType {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (sigma : Equiv.Perm alpha) (m : Multiset Nat) : Prop :=
  sigma.cycleType = m

/-- The permutation of the roots of an integral polynomial in a splitting
field induced by a Galois automorphism.  This uses the canonical
Polynomial.Gal.galAction action of Gal(L/K) on the root set of the
polynomial over K. -/
noncomputable def rootPerm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) :=
  let p : K[X] := f.map (algebraMap (RingOfIntegers K) K)
  have hmap : p.map (algebraMap K L) = f.map (algebraMap (RingOfIntegers K) L) := by
    simp only [p, Polynomial.map_map]
    rw [show (algebraMap K L).comp (algebraMap (RingOfIntegers K) K) =
        algebraMap (RingOfIntegers K) L from
      IsScalarTower.algebraMap_eq (RingOfIntegers K) K L]
  have h : (p.map (algebraMap K L)).Splits := by
    rw [hmap]
    exact hsplit
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨h⟩
  MulAction.toPermHom (Gal(L/K)) (p.rootSet L) sigma

/-- The cycle type of a Galois automorphism on the roots of an integral
polynomial. -/
noncomputable def rootCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) : Multiset Nat :=
  letI := Classical.decEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L)
  (rootPerm K L f hsplit sigma).cycleType

/-! ## 2. The general Dedekind--Frobenius interface -/

/-- The Dedekind--Frobenius cycle-type statement for one prime ideal: the
arithmetic Frobenius at a prime P above p realises exactly the multiset of
degrees of the irreducible factors of f modulo p.

The hypotheses are the honest ones: f is monic, its reduction modulo p is
separable, and f splits in L.  The conclusion is the existence of a
Frobenius element at P whose permutation of the roots of f has cycle type
factorDegrees (f mod p). -/
def DedekindFrobeniusCycleTypeStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  let fbar : ((RingOfIntegers K) ⧸ p)[X] := f.map (Ideal.Quotient.mk p)
  ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P ∧
    rootCycleType K L f hsplit sigma = factorDegrees fbar

/-- The exact first missing theorem.  For every finite Galois extension of
number fields, every monic integral polynomial that splits in the extension,
and every prime P above p at which the reduction is separable, some
arithmetic Frobenius at P has cycle type equal to the multiset of degrees of
the irreducible factors of f modulo p.

Mathlib supplies the Frobenius element (arithFrobAt) and the residue-field
action, but not this cycle-type comparison. -/
def DedekindFrobeniusCycleTypeTheorem : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusCycleTypeStatement K L f p P hmonic hsep hsplit

/-! ## 3. The corrected mod-29 factorization certificate -/

/-- The scalar 4 is the reduction of the leading coefficient of 2^36 psi_5;
the monic quadratic recorded in the original S2057 datum is therefore not the
correct factor.  This is the S2132 corrected product. -/
theorem S2167CorrectedProduct :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29)) =
      LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
        (Int.castRingHom (ZMod 29)) :=
  S2132CorrectedProduct

/-- The degree-ten factor f of S2126 is irreducible (kernel checked). -/
def S2167TenIrreducible : Prop :=
  Irreducible LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10

/-- The S2126 irreducibility theorem, re-exported under the S2167 name. -/
theorem S2167TenIrreducible_proof : S2167TenIrreducible :=
  LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10_irreducible

/-- The quadratic factor 19 + 24x + 4x^2 is irreducible modulo 29.  This is a
finite computation (discriminant 17, a non-square modulo 29); it is recorded
here as a named missing micro-input so that the main missing theorem remains
the cycle-type bridge, not a finite field check. -/
def S2167QuadraticIrreducible : Prop :=
  Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29)))

/-- The corrected factorization package required for the Dedekind--Frobenius
theorem at 29.  The product is proved above; the only unproved finite field
input is the irreducibility of the quadratic.  The degree statements are part
of the same finite certificate. -/
def S2167Mod29FactorizationRequired : Prop :=
  S2132F2Z.map (Int.castRingHom (ZMod 29)) *
      S2132F10Z.map (Int.castRingHom (ZMod 29)) =
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
      (Int.castRingHom (ZMod 29)) ∧
  S2167QuadraticIrreducible ∧
  S2167TenIrreducible ∧
  (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 ∧
  (S2132F10Z.map (Int.castRingHom (ZMod 29))).natDegree = 10

/-! ## 4. The concrete S2132 target -/

/-- The concrete target of S2132: an F'-automorphism of the actual
five-division field whose induced permutation of the twelve roots has cycle
type {2, 10}. -/
abbrev S2167ConcreteTarget : Prop := S2132FrobInducesPairCycleType

/-- The concrete target is exactly the S2132 statement. -/
theorem S2167ConcreteTarget_iff :
    S2167ConcreteTarget ↔ S2132FrobInducesPairCycleType :=
  Iff.rfl

/-! ## 5. Exact first missing -/

/-- The exact first missing of this file: the general Dedekind--Frobenius
cycle-type theorem, together with the one finite-field irreducibility check for
the corrected quadratic factor.  The latter is a small computation; the former
is the actual conceptual gap. -/
def S2167FirstMissing : Prop :=
  DedekindFrobeniusCycleTypeTheorem ∧ S2167QuadraticIrreducible

/-- The first missing projects to the quadratic finite check. -/
theorem S2167QuadraticIrreducible_of_firstMissing
    (h : S2167FirstMissing) : S2167QuadraticIrreducible :=
  h.2

/-- The first missing projects to the general Dedekind--Frobenius theorem. -/
theorem S2167DedekindFrobeniusCycleTypeTheorem_of_firstMissing
    (h : S2167FirstMissing) : DedekindFrobeniusCycleTypeTheorem :=
  h.1

/-! ## 6. Axiom footprint -/

#print axioms factorDegrees
#print axioms HasCycleType
#print axioms rootPerm
#print axioms rootCycleType
#print axioms DedekindFrobeniusCycleTypeStatement
#print axioms DedekindFrobeniusCycleTypeTheorem
#print axioms S2167FrobeniusExists
#print axioms S2167CorrectedProduct
#print axioms S2167TenIrreducible
#print axioms S2167TenIrreducible_proof
#print axioms S2167QuadraticIrreducible
#print axioms S2167Mod29FactorizationRequired
#print axioms S2167ConcreteTarget_iff
#print axioms S2167FirstMissing
#print axioms S2167QuadraticIrreducible_of_firstMissing
#print axioms S2167DedekindFrobeniusCycleTypeTheorem_of_firstMissing

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

end
