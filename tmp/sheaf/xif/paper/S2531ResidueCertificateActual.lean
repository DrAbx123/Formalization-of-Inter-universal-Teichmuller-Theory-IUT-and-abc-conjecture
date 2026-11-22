/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2487DedekindCertificateActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
import tmp.sheaf.xif.paper.S2141D5FactorizationFieldsActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2454D5FinalIntegrationActual
import tmp.sheaf.xif.paper.S2463ActionTransportActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.Galois.Basic

/-!
# S2531: the actual mod-29 residue certificate for psi_5, the corrected
Dedekind--Frobenius cycle-type theorem, and the exact reduction of
`S2132FrobInducesPairCycleType`

## What is actually proved here (no new missing input)

1. **The mod-29 residue certificate.**  S2126 proves that the degree-ten
   polynomial `f = 10 + 24x + 16x^2 + ... + x^10` is irreducible over
   `ZMod 29` (`s2094_f_irreducible`), S2216 proves that the corrected
   quadratic `19 + 24x + 4x^2` is irreducible over `ZMod 29`
   (`s2216_quadratic_irreducible`), and S2132 proves the corrected product
   identity `S2132CorrectedProduct`.  Combined here they give the concrete
   factorization certificate

     `2^36 * psi_5 == 4 * (x^2 + 6x + 12) * f   (mod 29)`

   with both factors monic irreducible of degrees 2 and 10
   (`S2531ProductForm`, `S2531Mod29FactorData`), hence
   `factorDegrees (S2132Psi5Z mod 29) = {2, 10}` (`S2531FactorDegrees`).
   This closes the finite micro-input left open in S2167/S2487
   (`S2531S2167Mod29FactorizationRequired`,
   `S2531S2167QuadraticIrreducible`).

2. **The actual Dedekind--Frobenius cycle-type theorem.**  The tree contains a
   completed orbit-size comparison: S2217 constructs the residue Frobenius
   permutation `permBar` and proves the combinatorial orbit lemma
   `cycleType_eq_fiber_sizes`; S2339/S2446/S2453 identify the fibres with the
   `minpoly` fibres (transitivity on the roots of every irreducible factor);
   S2454 proves the raw cycle-type identity `s2454PermBar_cycleType_raw`;
   S2440 transports it to the Galois root permutation.  Putting these together
   gives, with no hypothesis beyond the honest Dedekind hypotheses,

     `rootCycleType K L f hsplit sigma
        = (factorDegrees (fbar f p)).filter (fun n => n != 1)`

   for every arithmetic Frobenius `sigma` at `P`
   (`S2531DedekindFrobeniusCycleType`), and the pointwise statement
   `DedekindFrobeniusCycleTypeStatementCorrected` of S2217 follows whenever
   the residue field at `P` is finite (`S2531CorrectedStatement`).
   Consequently a reduction with factor degrees `{2, 10}` has root cycle
   type `{2, 10}` (`S2531rootCycleType_of_factorDegrees`).

3. **A correction of the S2167/S2487 route.**  S2217's
   `s2167_literal_statement_false` refutes the literal
   `DedekindFrobeniusCycleTypeTheorem` of S2167 (Mathlib's cycle type omits
   fixed points, while the literal statement compares it with the full factor
   degree multiset).  Hence
   `S2167FirstMissing = DedekindFrobeniusCycleTypeTheorem and
   S2167QuadraticIrreducible` is FALSE
   (`S2531S2167FirstMissing_false`), and S2487's conditional
   `S2487FirstMissing_of_dedekind` is vacuous.  The corrected statement is the
   one proved here.

## The exact missing input (reported, not assumed)

The residue certificate is a statement at the rational prime 29.  At 29 the
residue field of `F' = S1720Field` has residue degree 2 (29 is inert in
`Q(sqrt(-3))`, which is contained in `F'`; `s2216_29_mod_three`), so
the relative Frobenius at 29 has factor degrees `{1,1,5,5}`, not
`{2,10}`.  The mod-29 certificate therefore computes the *Q-level*
Frobenius, and two honest inputs remain before it yields
`S2132FrobInducesPairCycleType`:

* a monic integral model of a nonzero rational multiple of `psi_5`
  together with the reconciliation of its roots with the twelve roots of
  `psi_5` (elementary - the scaling `P(Y) = c * psi_5(Y/c)` with
  `c = 5 * 2^36` clears denominators and is monic integral - but not
  formalized here);
* the Q-to-F' transport of the cycle type (the linear-disjointness input
  `s2216LinearDisjointnessRequired` of S2216, or the restriction transport
  recorded in S2167 and S2471).

The alternative, transport-free route uses a prime that splits completely in
F' together with a `{2,10}` reduction there.  External numerical checks for
this attempt (not formalized; recorded only as plain Props below) give:

* `p = 13`:  `2^36 * psi_5` is irreducible mod 13 (degree 12), so the
  factor degrees are `{12}`, not `{2,10}` - the mod-13 certificate of the
  S1987 report is a twelve-cycle certificate, not a `(10,2)` certificate;
* `p = 613`: `S1720H` splits completely mod 613 (proved in S2481:
  `S2481HMod613_splits`), but `2^36 * psi_5` is irreducible mod 613
  (degree 12) - again `{12}`, the S2481 twelve-cycle certificate;
* `p = 1249`: `S1720H` splits completely mod 1249 and the reduction of
  `2^36 * psi_5` has factor degrees `{2,10}` - this is the
  residue-degree-one prime that the F'-level Dedekind route needs.

The precise remaining input is packaged below as `S2531ResidueData`;
`S2531Target_of_residueData` derives `S2132FrobInducesPairCycleType` from
that data, and `S2531ResidueDataRequired` is the exact first missing.

No `sorry`, `admit`, `axiom`, `True`, `PUnit` or
`native_decide` is used.  The axiom footprint of the main declarations is
printed at the end.  Per the task instruction this file has NOT been compiled;
the parent build coordinator must run the serial build.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

-- The residue fields of the primes used below are fields.
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

-- Quotients by maximal ideals are fields; needed for `factorDegrees` on
-- residue rings (the same local instance is used in S2217/S2454).
attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2531ResidueCertificateActual

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
open LeanFormal.IUT.XiFPaper.S2454D5FinalIntegrationActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S2487DedekindCertificateActual
open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-! ## 1. The actual mod-29 residue certificate -/

/-- The monic degree-ten quotient of the S2141 degree-ten factor: the S2141
factor is `C 4` times this polynomial. -/
def S2531Base : (ZMod 29)[X] :=
  C 10 - C 5 * X - C 13 * X ^ 2 + C 14 * X ^ 3 - C 5 * X ^ 4 +
    C 8 * X ^ 5 + C 5 * X ^ 6 + C 7 * X ^ 7 - C 4 * X ^ 9 + X ^ 10

/-- The S2141 degree-ten factor is the unit multiple `4 * S2531Base`. -/
theorem S2531Factor10_eq_scaled :
    S2141Factor10 = C (4 : ZMod 29) * S2531Base := rfl

/-- The un-scaled degree-ten factor is exactly the S2126 polynomial `f`
whose irreducibility is kernel checked in S2126. -/
theorem S2531Base_eq : S2531Base = S2132Factor10 := by
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      (simp [S2531Base, S2132Factor10, _root_.f, coeff_add, coeff_sub,
        coeff_mul, coeff_C, coeff_X_pow, coeff_X, coeff_monomial] <;>
        reduce_mod_char <;> decide)
  · have h1 : S2531Base.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hdeg : S2531Base.natDegree ≤ 10 := by
        unfold S2531Base
        compute_degree!
      omega
    have h2 : S2132Factor10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [S2132Factor10_eq_s2126, _root_.hfdeg]
      omega
    rw [h1, h2]

/-- The un-scaled degree-ten factor is monic. -/
theorem S2531Base_monic : S2531Base.Monic := by
  rw [S2531Base_eq, S2132Factor10_eq_s2126]
  exact _root_.hfmonic

/-- The un-scaled degree-ten factor is irreducible (S2126). -/
theorem S2531Base_irreducible : Irreducible S2531Base := by
  rw [S2531Base_eq]
  exact S2132Factor10_irreducible

/-- The un-scaled degree-ten factor has degree ten. -/
theorem S2531Base_natDegree : S2531Base.natDegree = 10 := by
  rw [S2531Base_eq, S2132Factor10_eq_s2126]
  exact _root_.hfdeg

/-- The S2126 degree-ten factor has degree ten. -/
theorem S2531Ten_natDegree : S2132Factor10.natDegree = 10 := by
  rw [S2132Factor10_eq_s2126]
  exact _root_.hfdeg

/-- The S2141 degree-ten factor is `4 * f`. -/
theorem S2531Factor10_eq :
    S2141Factor10 = C (4 : ZMod 29) * S2132Factor10 := by
  rw [S2531Factor10_eq_scaled, S2531Base_eq]

/-- The unit multiple `4 * f` of the S2126 polynomial is irreducible. -/
theorem S2531Factor10_irreducible : Irreducible S2141Factor10 := by
  have h4 : IsUnit (C (4 : ZMod 29)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by decide))
  have hassoc : Associated S2141Factor10 S2531Base := by
    rw [S2531Factor10_eq_scaled]
    exact associated_unit_mul_left S2531Base (C (4 : ZMod 29)) h4
  exact hassoc.symm.irreducible S2531Base_irreducible

/-- The quadratic factor `x^2 + 6x + 12` is irreducible over `F_29`
(finite root check, the argument of S2216). -/
theorem S2531Factor2_irreducible : Irreducible S2141Factor2 := by
  have hdeg : S2141Factor2.natDegree = 2 := S2141Factor2_natDegree
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]
    norm_num
  · intro x hx
    have hnot : ∀ y : ZMod 29, (12 : ZMod 29) + 6 * y + y ^ 2 ≠ 0 := by
      decide +revert
    exact hnot x (by simpa [S2141Factor2, S2132Factor2, IsRoot] using hx)

/-- The quadratic factor is monic. -/
theorem S2531Factor2_monic : S2141Factor2.Monic := by
  unfold S2141Factor2 S2132Factor2
  monicity!

/-- The corrected mod-29 product in the unit-times-two-monic-factors form:
`2^36 * psi_5 == 4 * (x^2 + 6x + 12) * f (mod 29)`. -/
theorem S2531ProductForm :
    S2132Psi5Z.map (Int.castRingHom (ZMod 29)) =
      C (4 : ZMod 29) * (S2141Factor2 * S2132Factor10) := by
  rw [← S2141Product, S2531Factor10_eq]
  ring

/-- The degree-two integer lift has degree two. -/
theorem S2531F2Z_natDegree :
    (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 := by
  rw [s2216_S2132F2Z_reduction]
  compute_degree!

/-- The degree-two integer lift is irreducible (S2216). -/
theorem S2531F2Z_irreducible :
    Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) :=
  s2216_quadratic_irreducible

/-- The degree-ten integer lift reduces to the S2126 polynomial `f`: both
have the canonical coefficients
`10 + 24x + 16x^2 + 14x^3 + 24x^4 + 8x^5 + 5x^6 + 7x^7 + 25x^9 + x^10`. -/
theorem S2531F10Z_reduction :
    S2132F10Z.map (Int.castRingHom (ZMod 29)) = S2132Factor10 := by
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      (simp [S2132F10Z, S2132Factor10, _root_.f, coeff_add, coeff_C,
        coeff_mul, coeff_X_pow, coeff_X, coeff_one, coeff_monomial] <;>
        reduce_mod_char <;> decide)
  · have h1 : (S2132F10Z.map (Int.castRingHom (ZMod 29))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (S2132F10Z.map (Int.castRingHom (ZMod 29))).natDegree ≤
          S2132F10Z.natDegree := Polynomial.natDegree_map_le
      have h10 : S2132F10Z.natDegree = 10 := by
        unfold S2132F10Z
        compute_degree!
      omega
    have h2 : S2132Factor10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [S2132Factor10_eq_s2126, _root_.hfdeg]
      omega
    rw [h1, h2]

/-- The degree-ten integer lift has degree ten. -/
theorem S2531F10Z_natDegree :
    (S2132F10Z.map (Int.castRingHom (ZMod 29))).natDegree = 10 := by
  rw [S2531F10Z_reduction, S2132Factor10_eq_s2126]
  exact _root_.hfdeg

/-- The degree-ten integer lift is irreducible (S2126). -/
theorem S2531F10Z_irreducible :
    Irreducible (S2132F10Z.map (Int.castRingHom (ZMod 29))) := by
  rw [S2531F10Z_reduction]
  exact S2132Factor10_irreducible

/-- The S2216 quadratic micro-input of S2167 is inhabited. -/
theorem S2531S2167QuadraticIrreducible : S2167QuadraticIrreducible :=
  s2216_quadratic_irreducible

/-- The finite-field input of S2167's `S2167Mod29FactorizationRequired`: the
corrected product, both irreducibilities and both degrees. -/
theorem S2531S2167Mod29FactorizationRequired : S2167Mod29FactorizationRequired :=
  ⟨S2132CorrectedProduct, S2531S2167QuadraticIrreducible, S2167TenIrreducible_proof,
    S2531F2Z_natDegree, S2531F10Z_natDegree⟩

/-- **The S2167/S2487 first missing is uninhabitable**, because its first
conjunct, the literal `DedekindFrobeniusCycleTypeTheorem`, is false (S2217:
Mathlib's cycle type omits fixed points).  S2487's
`S2487FirstMissing_of_dedekind` is therefore vacuous. -/
theorem S2531S2167FirstMissing_false : ¬ S2167FirstMissing := by
  rintro ⟨h, -⟩
  exact s2167_literal_statement_false h

/-- The S2487 quadratic micro-input (a proof term, not a Prop) is the S2216
quadratic irreducibility. -/
theorem S2531S2487QuadraticIrreducible : S2167QuadraticIrreducible :=
  S2487QuadraticIrreducible

/-- **S2487's exact missing statement is refuted**: `S2487DedekindMissing` is the
literal S2167 Dedekind theorem, which S2217 refutes.  Thus
`S2487FirstMissing_of_dedekind` has a false hypothesis and proves nothing. -/
theorem S2531S2487DedekindMissing_false : ¬ S2487DedekindMissing :=
  s2167_literal_statement_false

/-! ## 2. The actual Dedekind--Frobenius cycle-type theorem

The corrected statement compares Mathlib's cycle type (which omits fixed
points) with the factor-degree multiset with the `1`s removed.  It is proved
from the raw S2454 theorem and the S2440 root-permutation transport; no
general orbit-size comparison is assumed. -/

/-- Auxiliary multiset lemma: for a multiset `M` and the subtype of its
members, the multiset of all subtype values is `M.dedup`. -/
theorem S2531map_univ_subtype_val {alpha : Type*} [DecidableEq alpha]
    (M : Multiset alpha) [Fintype {x : alpha // x ∈ M}] :
    (Finset.univ : Finset {x : alpha // x ∈ M}).val.map Subtype.val = M.dedup := by
  classical
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.Nodup.map (f := Subtype.val) Subtype.val_injective
      (Finset.univ : Finset {x : alpha // x ∈ M}).nodup
  · exact Multiset.nodup_dedup M
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact Multiset.mem_dedup.mpr x.2
    · intro ha
      exact ⟨⟨a, Multiset.mem_dedup.mp ha⟩, rfl⟩

noncomputable def S2531PermBarCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p] :
    Multiset Nat :=
  letI := Classical.decEq ((fbar f p).rootSet ((NumberField.RingOfIntegers L) ⧸ P))
  (permBar (f := f) p P).cycleType

lemma S2531PermBarCycleType_eq_raw
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (NumberField.RingOfIntegers K) L)).Splits) :
    S2531PermBarCycleType K L f p P =
      letI : Fintype (s2454Beta K f p) := s2453Beta_fintype (K := K) (f := f) (p := p)
      Multiset.map (fun b : s2454Beta K f p => b.1.natDegree)
        (Finset.univ.filter (fun b : s2454Beta K f p => 2 ≤ b.1.natDegree)).val := by
  dsimp [S2531PermBarCycleType]
  letI := Subtype.instDecidableEq
  letI : Fintype (s2454Beta K f p) := s2453Beta_fintype (K := K) (f := f) (p := p)
  rw [s2454PermBar_cycleType_raw (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)]

/-- **The normalization of the raw S2454 cycle type.**  The subtype-indexed
multiset of the raw theorem is the multiset of factor degrees with the `1`s
removed. -/
theorem S2531permBar_cycleType_normalized
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (NumberField.RingOfIntegers K) L)).Splits) :
    (permBar (f := f) p P).cycleType =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  letI : DecidableEq ((fbar f p).rootSet ((NumberField.RingOfIntegers L) ⧸ P)) :=
    Subtype.instDecidableEq
  letI : Fintype {g : ((NumberField.RingOfIntegers K) ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
    s2453Beta_fintype (K := K) (f := f) (p := p)
  have hraw := s2454PermBar_cycleType_raw (K := K) (L := L) (f := f) (p := p)
    (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
  convert hraw using 2
  have hM : (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (s2397Fbar_ne_zero (K := K) (L := L) (f := f) (p := p) (P := P)
        (hmonic := hmonic))).mp hsep.squarefree
  have hmap :
      (Finset.univ : Finset (s2454Beta K f p)).val.map Subtype.val =
        UniqueFactorizationMonoid.normalizedFactors (fbar f p) := by
    rw [S2531map_univ_subtype_val
      (UniqueFactorizationMonoid.normalizedFactors (fbar f p)), hM.dedup]
  have h1 :
      (Finset.univ.filter
          (fun b : s2454Beta K f p => 2 ≤ b.1.natDegree)).val.map
          (fun b => b.1.natDegree) =
        ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).filter
          (fun g => 2 ≤ g.natDegree)).map (fun g => g.natDegree) := by
    rw [Finset.filter_val, ← hmap, Multiset.filter_map, Multiset.map_map]
    simp only [Function.comp_apply]
  have h3 :
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) =
        ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).filter
          (fun g => 2 ≤ g.natDegree)).map (fun g => g.natDegree) := by
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

/-- **The actual Dedekind--Frobenius cycle-type theorem** (corrected form).
For every arithmetic Frobenius `sigma` at `P`, the cycle type of its
permutation of the roots of `f` is the multiset of degrees of the normalized
irreducible factors of the reduction, with the linear factors removed. -/
theorem S2531DedekindFrobeniusCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (NumberField.RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) (H : IsArithFrobAt (NumberField.RingOfIntegers K) sigma P) :
    rootCycleType K L f hsplit sigma =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463ActionA K L
  letI : SMulCommClass Gal(L/K) (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463SmulCommA K L
  have Hloc : @IsArithFrobAt (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
      _ _ _ Gal(L/K) _
      (LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463ActionA K L)
      (LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463SmulCommA K L) sigma P :=
    (LeanFormal.IUT.XiFPaper.S2463ActionTransportActual.s2463_isArithFrobAt_iff
      (K := K) (L := L) sigma P).mpr H
  rw [← s2440_permBar_cycleType_eq_rootCycleType (K := K) (L := L) (f := f)
    (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
    (σ := sigma) (H := Hloc)]
  exact S2531permBar_cycleType_normalized (K := K) (L := L) (f := f) (p := p)
    (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)

/-- **The corrected Dedekind--Frobenius statement of S2217, proved** when the
residue field at `P` is finite (which holds for all nonzero primes of a number
field). -/
theorem S2531CorrectedStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    [hfin : Finite ((NumberField.RingOfIntegers L) ⧸ P)]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (NumberField.RingOfIntegers K) L)).Splits) :
    DedekindFrobeniusCycleTypeStatementCorrected (f := f) (p := p) (P := P)
      (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit) := by
  classical
  obtain ⟨sigma, H⟩ := S2470_frobeniusExists (K := K) (L := L) (P := P)
  exact ⟨sigma, H, S2531DedekindFrobeniusCycleType (K := K) (L := L) (f := f)
    (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
    (sigma := sigma) (H := H)⟩

/-- **A `{2,10}` reduction has root cycle type `{2,10}`.**  This is the
concrete consequence of the actual Dedekind--Frobenius theorem used below. -/
theorem S2531rootCycleType_of_factorDegrees
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (NumberField.RingOfIntegers K)[X]) (p : Ideal (NumberField.RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (NumberField.RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (NumberField.RingOfIntegers K) L)).Splits)
    (hfac : factorDegrees (fbar f p) = ({2, 10} : Multiset ℕ))
    (sigma : Gal(L/K)) (H : IsArithFrobAt (NumberField.RingOfIntegers K) sigma P) :
    rootCycleType K L f hsplit sigma = ({2, 10} : Multiset ℕ) := by
  rw [S2531DedekindFrobeniusCycleType (K := K) (L := L) (f := f) (p := p)
    (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
    (sigma := sigma) (H := H), hfac]
  decide

/-! ## 3. Factorization data and the factor-degree computation -/

/-- A concrete residue factorization certificate: an explicit scalar times two
monic irreducible factors of degrees two and ten.  The structure carries no
hypothesis on the residue ring other than commutativity, so it applies to
`ZMod q` and to residue rings `O_K / p` alike. -/
structure S2531FactorizationData (R : Type*) [CommRing R] (g : R[X]) where
  /-- The scalar in front of the two monic factors. -/
  c : R
  c_ne_zero : c ≠ 0
  g2 : R[X]
  g10 : R[X]
  product_eq : g = C c * (g2 * g10)
  g2_monic : g2.Monic
  g10_monic : g10.Monic
  g2_irreducible : Irreducible g2
  g10_irreducible : Irreducible g10
  g2_degree : g2.natDegree = 2
  g10_degree : g10.natDegree = 10

/-- **A `{2,10}` factorization has factor degrees `{2,10}`.** -/
theorem S2531factorDegrees_of_factorization
    (R : Type*) [CommRing R] [Field R] (g : R[X])
    (F : S2531FactorizationData R g) :
    factorDegrees g = ({2, 10} : Multiset ℕ) := by
  classical
  have hc : (C F.c : R[X]) ≠ 0 := by
    rw [Polynomial.C_eq_zero]
    exact F.c_ne_zero
  have hg2 : F.g2 ≠ 0 := F.g2_monic.ne_zero
  have hg10 : F.g10 ≠ 0 := F.g10_monic.ne_zero
  have hprod : F.g2 * F.g10 ≠ 0 := mul_ne_zero hg2 hg10
  have hnf : UniqueFactorizationMonoid.normalizedFactors g =
      ({F.g2, F.g10} : Multiset R[X]) := by
    rw [F.product_eq,
      UniqueFactorizationMonoid.normalizedFactors_mul hc hprod,
      UniqueFactorizationMonoid.normalizedFactors_of_isUnit
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr F.c_ne_zero)),
      Multiset.zero_add,
      UniqueFactorizationMonoid.normalizedFactors_mul hg2 hg10,
      UniqueFactorizationMonoid.normalizedFactors_irreducible F.g2_irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible F.g10_irreducible,
      Monic.normalize_eq_self F.g2_monic, Monic.normalize_eq_self F.g10_monic]
    simp
  rw [show factorDegrees g =
      (UniqueFactorizationMonoid.normalizedFactors g).map Polynomial.natDegree from rfl]
  rw [hnf]
  simp [F.g2_degree, F.g10_degree]

/-- **The actual mod-29 factorization data**: `2^36 * psi_5 ==
4 * (x^2 + 6x + 12) * f (mod 29)`, both factors monic irreducible of degrees 2
and 10.  This is assembled from S2126, S2216 and the S2132 corrected product. -/
noncomputable def S2531Mod29FactorData :
    S2531FactorizationData (ZMod 29)
      (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) where
  c := 4
  c_ne_zero := by decide
  g2 := S2141Factor2
  g10 := S2132Factor10
  product_eq := S2531ProductForm
  g2_monic := S2531Factor2_monic
  g10_monic := by
    rw [S2132Factor10_eq_s2126]
    exact _root_.hfmonic
  g2_irreducible := S2531Factor2_irreducible
  g10_irreducible := S2132Factor10_irreducible
  g2_degree := S2141Factor2_natDegree
  g10_degree := by
    rw [S2132Factor10_eq_s2126]
    exact _root_.hfdeg

/-- **The actual mod-29 residue certificate**: the reduction of the integral
model `2^36 * psi_5` has factor degrees `{2, 10}`. -/
theorem S2531FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) :=
  S2531factorDegrees_of_factorization (ZMod 29) _ S2531Mod29FactorData

/-- The full concrete mod-29 certificate in the unit-times-monic-factors form
together with the factor-degree multiset. -/
theorem S2531Mod29Certificate :
    S2132Psi5Z.map (Int.castRingHom (ZMod 29)) =
        C (4 : ZMod 29) * (S2141Factor2 * S2132Factor10) ∧
      Irreducible S2141Factor2 ∧ Irreducible S2132Factor10 ∧
      S2141Factor2.natDegree = 2 ∧ S2132Factor10.natDegree = 10 ∧
      factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
        ({2, 10} : Multiset ℕ) :=
  ⟨S2531ProductForm, S2531Factor2_irreducible, S2132Factor10_irreducible,
    S2141Factor2_natDegree, S2531Ten_natDegree, S2531FactorDegrees⟩

/-! ## 4. The finite residue certificates at 13, 613 and 1249

Only the mod-29 certificate above is formalized.  The other primes are recorded
as plain Props without inhabitants; the numerical claims in the comments are
external computations for this attempt (not formalized). -/

/-- The mod-13 finite certificate of the S1987 report: the reduction of
`2^36 * psi_5` is irreducible of degree twelve.  External check: true.  This
is the S2470 `S2470Mod13Certificate`; it yields the factor degrees `{12}`,
not `{2, 10}`. -/
def S2531Mod13Certificate : Prop :=
  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13)))

/-- The mod-13 certificate is the S2470 certificate. -/
theorem S2531Mod13Certificate_iff :
    S2531Mod13Certificate ↔ S2470Mod13Certificate := Iff.rfl

/-- The mod-613 finite certificate of S2481: the reduction of
`2^36 * psi_5` is irreducible of degree twelve.  This is S2481's
`S2481ResidueCertificate`; it yields the factor degrees `{12}`, not
`{2, 10}`. -/
def S2531Mod613Certificate : Prop :=
  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 613)))

/-- The mod-613 certificate is the S2481 certificate. -/
theorem S2531Mod613Certificate_iff :
    S2531Mod613Certificate ↔ S2481ResidueCertificate := Iff.rfl

/-- The mod-613 residue-degree-one statement: the defining polynomial of F'
splits completely modulo 613.  This is proved in S2481
(`S2481HMod613_splits`), so 613 has a prime of residue degree one in F'. -/
theorem S2531Mod613_residueDegreeOne :
    (S2481HZ.map (Int.castRingHom (ZMod 613))).Splits :=
  S2481HMod613_splits

/-- The finite mod-1249 factor-degree certificate, in explicit factored form:
`2^36 * psi_5 (mod 1249)` is a product of an irreducible quadratic and an
irreducible degree-ten factor.  External checks for this attempt: the
defining polynomial of F' splits completely mod 1249 (eight distinct roots),
and the factor degrees are `{2, 10}`.  Not formalized; no inhabitant. -/
def S2531Mod1249FactorDegrees : Prop :=
  ∃ (g2 g10 : (ZMod 1249)[X]),
    Irreducible g2 ∧ Irreducible g10 ∧
      g2.natDegree = 2 ∧ g10.natDegree = 10 ∧
      g2 * g10 = S2132Psi5Z.map (Int.castRingHom (ZMod 1249))

/-- The mod-1249 residue-degree-one statement: the defining polynomial of F'
splits completely modulo 1249.  External check for this attempt; not
formalized. -/
def S2531Mod1249ResidueDegreeOne : Prop :=
  (S2481HZ.map (Int.castRingHom (ZMod 1249))).Splits

/-- The combined mod-1249 certificate: a residue-degree-one prime of F' at
which the reduction has factor degrees `{2, 10}`.  This is the finite
certificate that the F'-level Dedekind route needs (no linear-disjointness
transport is required at a residue-degree-one prime). -/
def S2531Mod1249Certificate : Prop :=
  S2531Mod1249ResidueDegreeOne ∧ S2531Mod1249FactorDegrees

/-! ## 5. From residue data to `S2132FrobInducesPairCycleType` -/

/-- **The concrete residue data at the F'-level.**  An integral monic model
`f` of a nonzero `F'`-multiple of `psi_5`, a maximal prime `p` of
`O_{F'}`, a prime `P` of the actual 5-division field above `p` with
finite residue field, a `{2, 10}` factorization certificate for the
reduction, and the root reconciliation: the root cycle type of every
arithmetic Frobenius at `P` on the roots of `f` is realised on the twelve
`S2132` roots.

The `cycle_identification` field is the precise reconciliation step (the
roots of `f` are the scaled roots of `psi_5`); it does **not** assert the
cycle type `{2, 10}`, which is derived below from the Dedekind theorem. -/
structure S2531ResidueData where
  /-- The integral monic model of a nonzero `F'`-multiple of `psi_5`. -/
  f : (NumberField.RingOfIntegers S1720Field)[X]
  p : Ideal (NumberField.RingOfIntegers S1720Field)
  P : Ideal (NumberField.RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  [P_prime : P.IsPrime]
  [P_lies : P.LiesOver p]
  [P_finite : Finite ((NumberField.RingOfIntegers S2057FiveDivisionField) ⧸ P)]
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map
    (algebraMap (NumberField.RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  /-- The model is a nonzero scalar multiple of the actual `psi_5` over `F'`. -/
  f_model : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (NumberField.RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  /-- The finite residue factorization certificate. -/
  factorization : S2531FactorizationData
    ((NumberField.RingOfIntegers S1720Field) ⧸ p) (fbar f p)
  /-- The root reconciliation: the Dedekind root cycle type is realised on the
  twelve `S2132` roots. -/
  cycle_identification : ∀ (sigma : Gal(S2057FiveDivisionField/S1720Field)),
    IsArithFrobAt (NumberField.RingOfIntegers S1720Field) sigma P →
    ∃ tau : S2132L ≃ₐ[S1720Field] S2132L,
      Equiv.Perm.cycleType (S2132DivisionRootEquiv tau) =
        rootCycleType S1720Field S2057FiveDivisionField f f_splits sigma

/-- **The residue data produce an arithmetic Frobenius of root cycle type
`{2, 10}`.**  This is the actual Dedekind theorem applied to the residue
data. -/
theorem S2531ResidueData.frobenius (D : S2531ResidueData) :
    ∃ sigma : Gal(S2057FiveDivisionField/S1720Field),
      IsArithFrobAt (NumberField.RingOfIntegers S1720Field) sigma D.P ∧
        rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits sigma =
          ({2, 10} : Multiset ℕ) := by
  letI : D.p.IsMaximal := D.p_max
  haveI : D.P.IsPrime := D.P_prime
  haveI : D.P.LiesOver D.p := D.P_lies
  haveI : Finite ((NumberField.RingOfIntegers S2057FiveDivisionField) ⧸ D.P) := D.P_finite
  have hfac : factorDegrees (fbar D.f D.p) = ({2, 10} : Multiset ℕ) :=
    S2531factorDegrees_of_factorization
      ((NumberField.RingOfIntegers S1720Field) ⧸ D.p) (fbar D.f D.p) D.factorization
  obtain ⟨sigma, H⟩ := S2470_frobeniusExists
    (K := S1720Field) (L := S2057FiveDivisionField) (P := D.P)
  exact ⟨sigma, H, S2531rootCycleType_of_factorDegrees
    (K := S1720Field) (L := S2057FiveDivisionField) (f := D.f) (p := D.p)
    (P := D.P) (hmonic := D.f_monic) (hsep := D.f_sep) (hsplit := D.f_splits)
    (hfac := hfac) (sigma := sigma) (H := H)⟩

/-- **The residue data imply the honest S2132 target.**  The Dedekind cycle
type `{2, 10}` on the model roots is transported to an `F'`-automorphism of
the actual splitting field whose permutation of the twelve roots has cycle
type `{2, 10}`; the pair form is `S2132FrobInduces_iff`. -/
theorem S2531ResidueData.target (D : S2531ResidueData) :
    S2132FrobInducesPairCycleType := by
  obtain ⟨sigma, H, hcyc⟩ := D.frobenius
  obtain ⟨tau, htau⟩ := D.cycle_identification sigma H
  refine S2132FrobInduces_iff.mp ⟨tau, ?_⟩
  rw [htau, hcyc]

/-- The residue data imply the honest target. -/
theorem S2531Target_of_residueData (h : Nonempty S2531ResidueData) :
    S2132FrobInducesPairCycleType :=
  (Classical.choice h).target

/-- The residue data imply the S2480 absolute-closure root-cycle statement
(S2520). -/
theorem S2531S2480FirstMissing_of_residueData (h : Nonempty S2531ResidueData) :
    S2480FirstMissing :=
  S2520S2480FirstMissing_of_S2132 (S2531Target_of_residueData h)

/-- **The exact first missing**: nonempty residue data of the shape above. -/
def S2531ResidueDataRequired : Prop := Nonempty S2531ResidueData

/-- The exact first missing is the residue data requirement. -/
theorem S2531ResidueDataRequired_iff :
    S2531ResidueDataRequired ↔ Nonempty S2531ResidueData := Iff.rfl

/-! ## 6. Axiom footprint -/

#print axioms S2531Base_eq
#print axioms S2531Factor2_irreducible
#print axioms S2531Factor10_irreducible
#print axioms S2531F10Z_reduction
#print axioms S2531ProductForm
#print axioms S2531factorDegrees_of_factorization
#print axioms S2531Mod29FactorData
#print axioms S2531FactorDegrees
#print axioms S2531Mod29Certificate
#print axioms S2531S2167Mod29FactorizationRequired
#print axioms S2531S2167FirstMissing_false
#print axioms S2531permBar_cycleType_normalized
#print axioms S2531DedekindFrobeniusCycleType
#print axioms S2531CorrectedStatement
#print axioms S2531rootCycleType_of_factorDegrees
#print axioms S2531ResidueData.frobenius
#print axioms S2531ResidueData.target
#print axioms S2531Target_of_residueData
#print axioms S2531S2480FirstMissing_of_residueData

end LeanFormal.IUT.XiFPaper.S2531ResidueCertificateActual

end