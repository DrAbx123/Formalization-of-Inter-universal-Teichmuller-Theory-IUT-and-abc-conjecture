 /-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2141D5FactorizationFieldsActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2427RootPermCycleActualAdapted
import tmp.sheaf.xif.paper.S2454D5FinalIntegrationActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual

/-!
# S2491: concrete mod-29 factorization, the pair cycle type (10, 2), and the
precise factorization/cycle theorem

This file is the Task B computation file.  It has four layers.

## 1. A specific actual matrix with pair cycle type (10, 2)

The matrix `!![0, 1; 1, 1]` of S2009 is packaged as
`S2491PairMatrix`.  Its action on the twelve pairs `{+v}` of nonzero
vectors of `F_5^2` is the explicit permutation `C` of S2009, and the
kernel-checked S2009 computation gives

  `(pairPermHom S2491PairMatrix).cycleType = {10, 2}`.

This is a genuine, unconditional statement about a specific actual matrix.

## 2. The actual mod-29 factorization

S2141 proves the corrected product

  `S2141Factor2 * S2141Factor10 = S2132Psi5Z.map (Int.castRingHom (ZMod 29))`

where `S2141Factor2 = S2132Factor2 = x^2 + 6x + 12` and
`S2141Factor10 = 4 * (x^10 + 7x^7 + 5x^6 + 8x^5 - 5x^4 + 14x^3 - 13x^2 - 5x + 10)`.
We prove here that both factors are irreducible: the quadratic by the
finite root check of S2216/S2471, the degree-ten factor because it is the
unit multiple of the S2126 polynomial `f`.  Consequently

  `factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) = {2, 10}`.

## 3. The precise factorization/cycle theorem

S2454 proves the raw cycle type of the arithmetic Frobenius permutation
`permBar` as the multiset of degrees of the normalized factors of the
reduction.  The single missing normalization was the identification of that
finset-indexed multiset with `factorDegrees`.  We supply it in
`S2491permBar_cycleType_normalized`, and obtain the corrected
Dedekind--Frobenius cycle-type statement:

  `rootCycleType K L f hsplit sigma =
      (factorDegrees (fbar f p)).filter (fun n => n != 1)`

for every arithmetic Frobenius `sigma` at `P`.  This is the precise
factorization/cycle theorem; it is not a conditional construction of the
paper target.  The concrete mod-29 corollary is
`S2491rootCycleType_of_factorDegrees`: any arithmetic Frobenius at a prime
above 29 whose reduction has factor degrees `{2, 10}` has root cycle type
`{2, 10}`.

## 4. The exact missing arithmetic input for the paper target

The paper target is `S2480Target = S2203RangeCycleTypeRequired S1982Basis`,
equivalently the existence of an actual absolute Galois element of F' whose
mod-5 matrix has pair cycle type `(10, 2)` (`S2480FirstMissing`).  We prove
the concrete matrix side is complete, and that any actual Galois element whose
matrix is exactly the S2009 matrix `g102` gives the target.  What is missing
is exactly the arithmetic construction of such a Galois element: the mod-29
factorization of the actual (non-monic) division polynomial, the monic
integral model needed for the Dedekind--Frobenius theorem, and the
Q-to-F' linear-disjointness/restriction transport (S2253/S2328).  No
conditional object is announced as the actual target.

## Verification status

Per the task instruction this file has NOT been compiled.  The declarations
below are proposed; the parent build coordinator must run the serial build and
check the axiom footprint.  No `sorry`, `admit`, `axiom`, `True`,
`PUnit`, or `native_decide` is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

attribute [local instance] Ideal.Quotient.field

-- The mod-29 residue field instances used by the finite computations below.
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

namespace LeanFormal.IUT.XiFPaper.S2491CycleComputationActualAdapted

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2427RootPermCycleActualAdapted
open LeanFormal.IUT.XiFPaper.S2446D5FinalActual
open LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
open LeanFormal.IUT.XiFPaper.S2454D5FinalIntegrationActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual

/-! ## 1. The concrete matrix on the twelve pairs -/

/-- The concrete matrix `!![0, 1; 1, 1]` of S2009, acting on the twelve
pairs `{+v}` of nonzero vectors of `F_5^2`. -/
def S2491PairMatrix : S2009DicksonActual.GL2 :=
  S2009DicksonActual.g102

/-- The kernel-checked S2009 computation: this actual matrix has pair cycle
type `(10, 2)`. -/
theorem S2491PairMatrix_pairCycleType :
    (S2009DicksonActual.pairPermHom S2491PairMatrix).cycleType =
      ({10, 2} : Multiset ℕ) :=
  S2009DicksonActual.cycleType_pairPerm_g102

/-- The matrix is an element of the full finite Dickson group, so its cycle
type is realised in `GL_2(F_5)`. -/
theorem S2491PairMatrix_hasCycleType102 :
    S2009DicksonActual.HasCycleType102
      (⊤ : Subgroup S2009DicksonActual.GL2) :=
  ⟨S2491PairMatrix, Subgroup.mem_top _, S2491PairMatrix_pairCycleType⟩

/-- The explicit action on the enumerated twelve pairs, transported from
S2009: the matrix acts by the explicit permutation `tau`. -/
theorem S2491PairMatrix_action (i : Fin 12) :
    S2009DicksonActual.pairAct S2491PairMatrix
        (S2009DicksonActual.pairOf i) =
      S2009DicksonActual.pairOf (S2009DicksonActual.tau i) :=
  S2009DicksonActual.pairAct_g102_pairOf i

/-- The pair permutation of the concrete matrix is exactly the S2009
permutation `C`, whose cycle type is the disjoint union of a 10-cycle and a
2-cycle. -/
theorem S2491PairMatrix_eq_C :
    S2009DicksonActual.pairPermHom S2491PairMatrix =
      S2009DicksonActual.C :=
  S2009DicksonActual.C_eq_pairPerm.symm

/-- The multiset `{10, 2}` and `{2, 10}` are the same cycle type. -/
theorem S2491CycleTypeSymm :
    ({10, 2} : Multiset ℕ) = ({2, 10} : Multiset ℕ) := by
  decide

/-! ## 2. The actual mod-29 factorization and its factor degrees -/

/-- The monic quadratic factor `x^2 + 6x + 12` of the corrected mod-29
product, written in expanded form for the finite computation. -/
def S2491Factor2Expanded : (ZMod 29)[X] :=
  C (12 : ZMod 29) + C 6 * X + X ^ 2

/-- The expanded quadratic is the S2132 quadratic factor. -/
theorem S2491Factor2Expanded_eq :
    S2491Factor2Expanded = S2141Factor2 := by
  rfl

/-- The quadratic factor is irreducible over `F_29`: its discriminant
`36 - 48 = 17` is a non-square, checked by the finite root computation. -/
theorem S2491Factor2Expanded_irreducible :
    Irreducible S2491Factor2Expanded := by
  have hdeg : S2491Factor2Expanded.natDegree = 2 := by
    unfold S2491Factor2Expanded
    compute_degree!
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]
    norm_num
  · intro x hx
    have hnot : ∀ y : ZMod 29,
        (12 : ZMod 29) + 6 * y + y ^ 2 ≠ 0 := by
      decide +revert
    exact hnot x (by simpa [S2491Factor2Expanded, IsRoot] using hx)

/-- The S2141 quadratic factor is irreducible. -/
theorem S2491Factor2_irreducible : Irreducible S2141Factor2 := by
  rw [← S2491Factor2Expanded_eq]
  exact S2491Factor2Expanded_irreducible

/-- The un-scaled expanded degree-ten factor
`x^10 + 7x^7 + 5x^6 + 8x^5 - 5x^4 + 14x^3 - 13x^2 - 5x + 10`. -/
def S2491F10Base : (ZMod 29)[X] :=
  C 10 - C 5 * X - C 13 * X ^ 2 + C 14 * X ^ 3 - C 5 * X ^ 4 +
    C 8 * X ^ 5 + C 5 * X ^ 6 + C 7 * X ^ 7 - C 4 * X ^ 9 + X ^ 10

/-- The S2141 degree-ten factor is the unit multiple `4 * S2491F10Base`. -/
theorem S2491Factor10_eq_scaled :
    S2141Factor10 = C (4 : ZMod 29) * S2491F10Base :=
  rfl

/-- The un-scaled degree-ten factor is exactly the S2126 polynomial `f` of
S2132. -/
theorem S2491F10Base_eq : S2491F10Base = S2132Factor10 := by
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      (simp [S2491F10Base, S2132Factor10, _root_.f, coeff_add, coeff_sub,
        coeff_mul, coeff_C, coeff_X_pow, coeff_X, coeff_monomial] <;>
        reduce_mod_char <;> decide)
  · have h1 : S2491F10Base.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      unfold S2491F10Base
      compute_degree!
      omega
    have h2 : S2132Factor10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [S2132Factor10_eq_s2126, _root_.hfdeg]
      omega
    rw [h1, h2]

/-- The un-scaled degree-ten factor is monic. -/
theorem S2491F10Base_monic : S2491F10Base.Monic := by
  rw [S2491F10Base_eq, S2132Factor10_eq_s2126]
  exact _root_.hfmonic

/-- The un-scaled degree-ten factor is irreducible: S2126 proves the
irreducibility of `f`, and `S2491F10Base = f`. -/
theorem S2491F10Base_irreducible : Irreducible S2491F10Base := by
  rw [S2491F10Base_eq]
  exact S2132Factor10_irreducible

/-- The S2141 degree-ten factor is irreducible: it is the unit multiple
`4 * f` of the irreducible S2126 polynomial. -/
theorem S2491Factor10_irreducible : Irreducible S2141Factor10 := by
  have hu : IsUnit (C (4 : ZMod 29)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by decide))
  have hassoc :
      Associated (C (4 : ZMod 29) * S2491F10Base) S2491F10Base :=
    associated_unit_mul_left S2491F10Base (C (4 : ZMod 29)) hu
  rw [S2491Factor10_eq_scaled]
  exact hassoc.symm.irreducible S2491F10Base_irreducible

/-- The quadratic factor is monic. -/
theorem S2491Factor2_monic : S2141Factor2.Monic := by
  unfold S2141Factor2 S2132Factor2
  monicity!

/-- The actual corrected mod-29 product, re-exported from S2141. -/
theorem S2491Mod29Product :
    S2141Factor2 * S2141Factor10 =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) :=
  S2141Product

/-- The original S2167 corrected product is the same factorization, with the
scalar `4` on the quadratic factor rather than on the degree-ten factor. -/
theorem S2491CorrectedProduct :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29)) =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) :=
  S2167CorrectedProduct

/-- The exact factor-degree computation: the reduction of the actual integral
model has one irreducible quadratic factor and one irreducible degree-ten
factor, so its factor-degree multiset is `{2, 10}`. -/
theorem S2491FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) := by
  classical
  rw [← S2141Product]
  change (UniqueFactorizationMonoid.normalizedFactors
      (S2141Factor2 * S2141Factor10)).map Polynomial.natDegree =
    ({2, 10} : Multiset ℕ)
  rw [UniqueFactorizationMonoid.normalizedFactors_mul
    S2491Factor2_irreducible.ne_zero S2491Factor10_irreducible.ne_zero]
  have h2norm : UniqueFactorizationMonoid.normalizedFactors S2141Factor2 =
      ({S2141Factor2} : Multiset ((ZMod 29)[X])) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      S2491Factor2_irreducible, Monic.normalize_eq_self S2491Factor2_monic]
  have h10norm : UniqueFactorizationMonoid.normalizedFactors S2141Factor10 =
      ({S2132Factor10} : Multiset ((ZMod 29)[X])) := by
    rw [S2491Factor10_eq_scaled]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul
      (Polynomial.C_ne_zero.mpr (by decide : (4 : ZMod 29) ≠ 0))
      S2491F10Base_irreducible.ne_zero]
    rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by decide)))]
    rw [Multiset.zero_add]
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      S2491F10Base_irreducible, Monic.normalize_eq_self S2491F10Base_monic,
      S2491F10Base_eq]
  rw [h2norm, h10norm]
  simp only [Multiset.map_add, Multiset.map_singleton]
  rw [S2141Factor2_natDegree, S2132Factor10_eq_s2126, _root_.hfdeg]
  decide

/-- The same factor-degree computation for the original S2132 corrected
product. -/
theorem S2491FactorDegreesCorrectedProduct :
    factorDegrees (S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) := by
  rw [S2167CorrectedProduct]
  exact S2491FactorDegrees

/-- The full concrete mod-29 factorization certificate: product,
irreducibility of both factors, and the factor-degree multiset. -/
theorem S2491ConcreteMod29Factorization :
    S2141Factor2 * S2141Factor10 =
        S2132Psi5Z.map (Int.castRingHom (ZMod 29)) ∧
      Irreducible S2141Factor2 ∧
      Irreducible S2141Factor10 ∧
      factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
        ({2, 10} : Multiset ℕ) :=
  ⟨S2141Product, S2491Factor2_irreducible, S2491Factor10_irreducible,
    S2491FactorDegrees⟩

/-! ## 3. The precise factorization/cycle theorem -/

/-- Auxiliary multiset lemma: for a multiset `M` and the subtype of its
members, the multiset of all subtype values is `M.dedup`.  This is the
normalization that identifies the finset-indexed raw S2454 cycle type with
the `normalizedFactors`-indexed `factorDegrees`. -/
theorem S2491map_univ_subtype_val {alpha : Type*}
    (M : Multiset alpha) [Fintype {x : alpha // x ∈ M}] :
    (Finset.univ : Finset {x : alpha // x ∈ M}).val.map Subtype.val =
      M.dedup := by
  classical
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact (Finset.univ : Finset {x : alpha // x ∈ M}).nodup.map
      Subtype.val_injective
  · exact Multiset.nodup_dedup M
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact Multiset.mem_dedup.mpr x.2
    · intro ha
      exact ⟨⟨a, Multiset.mem_dedup.mp ha⟩, rfl⟩

/-- **The normalization step.**  The raw S2454 cycle type, indexed by the
subtype of normalized factors of the reduction, is exactly
`(factorDegrees (fbar f p)).filter (fun n => n != 1)`. -/
theorem S2491permBar_cycleType_normalized
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) :
    (permBar (f := f) p P).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  haveI : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
  letI : Fintype
      {g : ((RingOfIntegers K) ⧸ p)[X] //
        g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
    s2453Beta_fintype K f p
  have hraw := s2454PermBar_cycleType_raw (K := K) (L := L)
    f p P hmonic hsep hsplit
  rw [hraw]
  have hM :
      (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).Nodup := by
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (s2397Fbar_ne_zero f p P hmonic)).mp hsep.squarefree
  have hmap :
      (Finset.univ :
          Finset {g : ((RingOfIntegers K) ⧸ p)[X] //
            g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}).val.map
          Subtype.val =
        UniqueFactorizationMonoid.normalizedFactors (fbar f p) := by
    rw [S2491map_univ_subtype_val
      (UniqueFactorizationMonoid.normalizedFactors (fbar f p)), hM.dedup]
  have h1 :
      (Finset.univ.filter
          (fun b : {g : ((RingOfIntegers K) ⧸ p)[X] //
            g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} =>
            2 ≤ b.1.natDegree)).val.map
          (fun b => b.1.natDegree) =
        ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).filter
          (fun g => 2 ≤ g.natDegree)).map
          (fun g => g.natDegree) := by
    rw [Finset.filter_val, ← hmap, Multiset.filter_map, Multiset.map_map]
    simp only [Function.comp_apply]
  have h3 :
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) =
        ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).filter
          (fun g => 2 ≤ g.natDegree)).map
          (fun g => g.natDegree) := by
    change ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map
      (fun g => g.natDegree)).filter (fun n => n ≠ 1) =
        ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).filter
          (fun g => 2 ≤ g.natDegree)).map (fun g => g.natDegree)
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro g hg
    have hpos : 0 < g.natDegree :=
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg).natDegree_pos
    constructor <;> intro h <;> omega
  rw [h1]
  exact h3.symm

/-- **The precise factorization/cycle theorem (pointwise form).**  For every
arithmetic Frobenius at `P`, the cycle type of its permutation of the roots
of `f` is the multiset of degrees of the normalized irreducible factors of
the reduction, with the linear factors removed. -/
theorem S2491DedekindFrobeniusCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K))
    (H : IsArithFrobAt (RingOfIntegers K) sigma P) :
    rootCycleType K L f hsplit sigma =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  rw [← s2427RootPermBar_cycleType_rootCycleType (K := K) (L := L)
    f p P hmonic hsep hsplit sigma H]
  rw [s2427RootPermBar_cycleType_bar (K := K) (L := L)
    f p P hmonic hsep hsplit]
  exact S2491permBar_cycleType_normalized
    (K := K) (L := L) (f := f) (p := p) (P := P)
    (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)

/-- **The concrete sigma corollary.**  If the reduction at `p` has factor
degrees `{2, 10}`, then every arithmetic Frobenius at `P` has root cycle
type `{2, 10}`.  At `K = Q`, `p = (29)` and the monic model of psi_5 this
is the mod-29 Frobenius computation. -/
theorem S2491rootCycleType_of_factorDegrees
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (hfac : factorDegrees (fbar f p) = ({2, 10} : Multiset ℕ))
    (sigma : Gal(L/K))
    (H : IsArithFrobAt (RingOfIntegers K) sigma P) :
    rootCycleType K L f hsplit sigma = ({2, 10} : Multiset ℕ) := by
  rw [S2491DedekindFrobeniusCycleType
    (K := K) (L := L) (f := f) (p := p) (P := P)
    (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
    (sigma := sigma) (H := H), hfac]
  decide

/-- The concrete mod-29 factor-degree input for the corollary above.  This is
the finite computation of Section 2; the remaining arithmetic task is to put
it in the exact monic-integral form required by
`S2491DedekindFrobeniusCycleType` (the actual integral model
`S2132Psi5Z` has leading coefficient `5`, not `1`). -/
theorem S2491ConcreteMod29FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) :=
  S2491FactorDegrees

/-! ## 4. The actual paper target and the exact missing input -/

/-- The actual paper target: the range cycle type at the selected basis
`S1982Basis` (S2203/S2480). -/
abbrev S2491ActualTarget : Prop := S2480Target

/-- The exact first missing form used by S2480: an actual absolute Galois
element of F' whose mod-5 matrix has pair cycle type `(10, 2)`. -/
abbrev S2491ExactFirstMissing : Prop := S2480FirstMissing

/-- The target as the existence of an actual absolute Galois element with
pair cycle type `(10, 2)`. -/
theorem S2491ActualTarget_iff_exists_sigma :
    S2491ActualTarget ↔ ∃ sigma : S1725AbsoluteGalois,
      (S2009DicksonActual.pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation
          S1987Five S1982Basis sigma)).cycleType =
            ({10, 2} : Multiset ℕ) :=
  S2480Target_iff_exists_sigma

/-- The exact first missing is equivalent to the actual target. -/
theorem S2491ExactFirstMissing_iff_target :
    S2491ExactFirstMissing ↔ S2491ActualTarget :=
  S2480FirstMissing_iff_target

/-- A sufficient concrete arithmetic witness: if an actual absolute Galois
element has matrix exactly the S2009 matrix `g102`, then the actual target
holds.  The remaining arithmetic task is to construct such an element (or,
more generally, one whose matrix has the same cycle type). -/
theorem S2491ActualTarget_of_sigma_eq_g102
    (sigma : S1725AbsoluteGalois)
    (hsigma :
      S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis
          sigma = S2009DicksonActual.g102) :
    S2491ActualTarget :=
  S2480Target_iff_range.mpr
    ⟨S2009DicksonActual.g102,
      MonoidHom.mem_range.mpr ⟨sigma, hsigma⟩,
      S2009DicksonActual.cycleType_pairPerm_g102⟩

/-- The finite matrix side of the paper target is completely settled: the
required cycle type is realised by the explicit S2009 matrix. -/
theorem S2491FiniteMatrixSideComplete :
    ∃ h : S2009DicksonActual.GL2,
      (S2009DicksonActual.pairPermHom h).cycleType =
        ({10, 2} : Multiset ℕ) :=
  ⟨S2491PairMatrix, S2491PairMatrix_pairCycleType⟩

/-! ## Axiom-footprint declarations (informational; the parent build must
check them with a serial build) -/

#print axioms S2491PairMatrix_pairCycleType
#print axioms S2491Factor2_irreducible
#print axioms S2491Factor10_irreducible
#print axioms S2491FactorDegrees
#print axioms S2491permBar_cycleType_normalized
#print axioms S2491DedekindFrobeniusCycleType
#print axioms S2491rootCycleType_of_factorDegrees
#print axioms S2491ActualTarget_of_sigma_eq_g102

end LeanFormal.IUT.XiFPaper.S2491CycleComputationActualAdapted

end
