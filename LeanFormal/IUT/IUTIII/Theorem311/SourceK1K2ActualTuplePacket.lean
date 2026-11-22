import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationFamilyCutActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionFromContract
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralLogTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# Actual finite-place tuple packet and its attained hull cut

This file constructs a `SourcePacketRealization` whose carrier is the actual
finite-place arithmetic tensor block

  `ArithmeticTensorTupleBlock places tuple`

and whose log-volume is the actual additive Haar log-volume of the actual
`p^n`-scaled canonical tuple hull.  The possible-image family is the actual
finite initial segment of these hull log-volumes, and the ambient set is their
range.  The two main results are

* `actualTuplePossibleImage_familyCutAttained`:
  `FamilyCutAttainedIn (range volume) (fun n => {volume k | k ≤ n})`;
* `actualTuplePacket_nonempty_attainedHullCut`:
  the corresponding `Nonempty (AttainedHullCut ...)`.

The family-cut proof uses only the actual Haar scaling law
`μ (p • S) = p^{-finrank} μ S`, the positivity and finiteness of the canonical
hull measure, and the resulting strict antitonicity of the log-volume
sequence.  No attainment law is assumed as a structure field.

Truth boundary.  The packet's arithmetic side is actual: the carrier is the
tensor block of the specified finite places, and the log-volume is the Haar
log-volume of the actual scaled canonical hull.  The `possibleImage` family
constructed here is the *actual hull-volume initial segment*, not the paper's
full `possibleImage` family, and the procession uses the canonical identity
Hodge theater built from a supplied `SourceDefinition31Data`; the paper's
actual Hodge theater / full LGP procession is not constructed here.  Hence
this file proves a source-layer K1K2 packet with an attained family cut, but
it does not by itself close the paper's source `possibleImage` realization,
N4--N7 as a whole, or the IUT-to-ABC chain.

The precise missing source bridge is recorded below as a comment, not as an
assumed field.  It requires a place `v`, a source-image realization `R`, a
map from the tensor block to `I.ThetaPilotPoint v` preserving the actual
log-degree, a map from the scale index to the finite source procession
carrier, and the equality of the hull-volume initial segments with the
log-volumes of `I.possibleThetaPilotImageSet` / `I.sourceHolomorphicHull`.
None of these maps is constructed or assumed here.
-/

set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT
namespace K1K2Realization
namespace HullPresentationActualTuplePacket

open MeasureTheory
open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Pointwise

universe u v w s

section ActualHullVolumes

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

/-- The actual `p^n` scalar used to scale the canonical tuple hull. -/
noncomputable def arithmeticTuplePowerScale (n : Nat) : ℚ_[p] :=
  (p : ℚ_[p]) ^ n

/-- The actual `p^n`-scaled canonical arithmetic-tuple hull. -/
noncomputable def arithmeticTuplePowerScaledHull (n : Nat) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTuplePowerScale (p := p) n •
    arithmeticTupleCanonicalHull places tuple

/-- The actual Haar measure of the `p^n`-scaled canonical hull, as a real
number. -/
noncomputable def actualTupleHullMeasure (n : Nat) : Real :=
  (μ (arithmeticTuplePowerScaledHull (p := p) places tuple n)).toReal

/-- The actual real Haar log-volume of the `p^n`-scaled canonical hull. -/
noncomputable def actualTupleHullLogVolume (n : Nat) : Real :=
  Real.log (actualTupleHullMeasure (p := p) places tuple μ n)

/-- The scaled canonical hull has positive finite Haar measure at every scale. -/
theorem arithmeticTuplePowerScaledHull_measure_pos_lt_top (n : Nat) :
    0 < μ (arithmeticTuplePowerScaledHull (p := p) places tuple n) ∧
      μ (arithmeticTuplePowerScaledHull (p := p) places tuple n) < ⊤ := by
  induction n with
  | zero =>
      simpa [arithmeticTuplePowerScaledHull, arithmeticTuplePowerScale] using
        (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1
  | succ n ih =>
      let r := Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
      have hp0 : (p : ENNReal) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
      have hfactor_pos : 0 < ((p : ENNReal) ^ r)⁻¹ :=
        ENNReal.inv_pos.mpr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p))
      have hfactor_lt_top : ((p : ENNReal) ^ r)⁻¹ < ⊤ :=
        ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (pow_ne_zero r hp0))
      have hstep : arithmeticTuplePowerScaledHull (p := p) places tuple (n + 1) =
          (p : ℚ_[p]) • arithmeticTuplePowerScaledHull (p := p) places tuple n := by
        unfold arithmeticTuplePowerScaledHull arithmeticTuplePowerScale
        rw [pow_succ', smul_smul]
      rw [hstep, LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional]
      exact ⟨ENNReal.mul_pos hfactor_pos.ne' ih.1.ne',
        ENNReal.mul_lt_top hfactor_lt_top ih.2⟩

/-- The real Haar measure of the scaled hull is positive. -/
theorem actualTupleHullMeasure_pos (n : Nat) :
    0 < actualTupleHullMeasure (p := p) places tuple μ n :=
  ENNReal.toReal_pos
    (arithmeticTuplePowerScaledHull_measure_pos_lt_top (p := p) places tuple μ n).1.ne'
    (arithmeticTuplePowerScaledHull_measure_pos_lt_top (p := p) places tuple μ n).2.ne

/-- The actual Haar scaling law in log form: one further `p`-scaling lowers the
log-volume by `finrank * log p`. -/
theorem actualTupleHullLogVolume_succ (n : Nat) :
    actualTupleHullLogVolume (p := p) places tuple μ (n + 1) =
      actualTupleHullLogVolume (p := p) places tuple μ n -
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          Real.log (p : Real) := by
  have hstep : arithmeticTuplePowerScaledHull (p := p) places tuple (n + 1) =
      (p : ℚ_[p]) • arithmeticTuplePowerScaledHull (p := p) places tuple n := by
    unfold arithmeticTuplePowerScaledHull arithmeticTuplePowerScale
    rw [pow_succ', smul_smul]
  unfold actualTupleHullLogVolume actualTupleHullMeasure
  rw [hstep]
  rw [LeanFormal.IUT.FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
    (p := p) μ (arithmeticTuplePowerScaledHull_measure_pos_lt_top places tuple μ n).1
    (arithmeticTuplePowerScaledHull_measure_pos_lt_top places tuple μ n).2]
  ring

/-- Closed form of the actual hull log-volume sequence. -/
theorem actualTupleHullLogVolume_eq (n : Nat) :
    actualTupleHullLogVolume (p := p) places tuple μ n =
      actualTupleHullLogVolume (p := p) places tuple μ 0 -
        (n : Real) *
          (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
            Real.log (p : Real) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [actualTupleHullLogVolume_succ, ih]
      push_cast
      ring

theorem real_log_prime_pos : 0 < Real.log (p : Real) := by
  have hpgt : (1 : Real) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact Real.log_pos hpgt

/-- The actual hull log-volume sequence is strictly decreasing in the scale
index. -/
theorem actualTupleHullLogVolume_strictAnti {m n : Nat} (hmn : m < n) :
    actualTupleHullLogVolume (p := p) places tuple μ n <
      actualTupleHullLogVolume (p := p) places tuple μ m := by
  have hrank : (0 : Real) <
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) := by
    exact_mod_cast finrank_arithmeticTensorTupleBlock_pos (places := places) tuple
  have hlog : 0 < Real.log (p : Real) := real_log_prime_pos (p := p)
  have hc : 0 <
      (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
        Real.log (p : Real) := mul_pos hrank hlog
  have hdiff : (m : Real) < (n : Real) := by exact_mod_cast hmn
  have hmul : (m : Real) *
        ((Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          Real.log (p : Real)) <
      (n : Real) *
        ((Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          Real.log (p : Real)) :=
    mul_lt_mul_of_pos_right hdiff hc
  have hmul' : (m : Real) *
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          Real.log (p : Real) <
      (n : Real) *
        (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
          Real.log (p : Real) := by
    calc
      (m : Real) *
          (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
            Real.log (p : Real) =
        (m : Real) *
          ((Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
            Real.log (p : Real)) := by ring
      _ < (n : Real) *
          ((Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
            Real.log (p : Real)) := hmul
      _ = (n : Real) *
          (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : Real) *
            Real.log (p : Real) := by ring
  have hn := actualTupleHullLogVolume_eq (p := p) places tuple μ n
  have hm := actualTupleHullLogVolume_eq (p := p) places tuple μ m
  linarith [hn, hm, hmul']

/-- The actual hull log-volume sequence is antitone. -/
theorem actualTupleHullLogVolume_antitone {m n : Nat} (hmn : m ≤ n) :
    actualTupleHullLogVolume (p := p) places tuple μ n ≤
      actualTupleHullLogVolume (p := p) places tuple μ m := by
  rcases lt_or_eq_of_le hmn with hlt | heq
  · exact le_of_lt (actualTupleHullLogVolume_strictAnti (p := p) places tuple μ hlt)
  · subst n
    exact le_rfl

/-- The actual hull log-volume at scales zero and one differs, witnessing
non-degeneracy. -/
theorem actualTupleHullLogVolume_ne_zero_one :
    actualTupleHullLogVolume (p := p) places tuple μ 0 ≠
      actualTupleHullLogVolume (p := p) places tuple μ 1 := by
  exact ne_of_gt
    (actualTupleHullLogVolume_strictAnti (p := p) places tuple μ (by omega : 0 < 1))

/-- The actual real measure sequence is antitone. -/
theorem actualTupleHullMeasure_antitone {m n : Nat} (hmn : m ≤ n) :
    actualTupleHullMeasure (p := p) places tuple μ n ≤
      actualTupleHullMeasure (p := p) places tuple μ m := by
  have hlog : Real.log (actualTupleHullMeasure (p := p) places tuple μ n) ≤
      Real.log (actualTupleHullMeasure (p := p) places tuple μ m) :=
    actualTupleHullLogVolume_antitone (p := p) places tuple μ hmn
  exact (Real.log_le_log_iff (actualTupleHullMeasure_pos (p := p) places tuple μ n)
    (actualTupleHullMeasure_pos (p := p) places tuple μ m)).mp hlog

/-- The actual hull-volume possible-image initial segment at scale index `n`. -/
noncomputable def actualTuplePossibleImage (n : Nat) : Set Real :=
  {x | ∃ k ≤ n, x = actualTupleHullLogVolume (p := p) places tuple μ k}

/-- The actual range of all power-scaled hull log-volumes. -/
noncomputable def actualTupleLogVolumeSet : Set Real :=
  Set.range (actualTupleHullLogVolume (p := p) places tuple μ)

omit [BorelSpace (ArithmeticTensorTupleBlock places tuple)] [μ.IsAddHaarMeasure] in
theorem actualTuplePossibleImage_nonempty (n : Nat) :
    (actualTuplePossibleImage (p := p) places tuple μ n).Nonempty :=
  ⟨actualTupleHullLogVolume (p := p) places tuple μ n, n, le_rfl, rfl⟩

omit [BorelSpace (ArithmeticTensorTupleBlock places tuple)] [μ.IsAddHaarMeasure] in
theorem actualTuplePossibleImage_subset_logVolumeSet (n : Nat) :
    actualTuplePossibleImage (p := p) places tuple μ n ⊆
      actualTupleLogVolumeSet (p := p) places tuple μ := by
  rintro x ⟨k, _hk, rfl⟩
  exact Set.mem_range_self k

/-- The actual log-volume range is bounded above by its first value. -/
theorem actualTupleLogVolumeSet_subset_Iic :
    actualTupleLogVolumeSet (p := p) places tuple μ ⊆
      Set.Iic (actualTupleHullLogVolume (p := p) places tuple μ 0) := by
  rintro x ⟨n, rfl⟩
  exact actualTupleHullLogVolume_antitone (p := p) places tuple μ (Nat.zero_le n)

/-- The actual log-volume range is not the whole real line. -/
theorem actualTupleLogVolumeSet_ne_univ :
    actualTupleLogVolumeSet (p := p) places tuple μ ≠ Set.univ := by
  intro h
  have hmem : actualTupleHullLogVolume (p := p) places tuple μ 0 + 1 ∈
      actualTupleLogVolumeSet (p := p) places tuple μ := by
    rw [h]
    exact Set.mem_univ _
  have hle : actualTupleHullLogVolume (p := p) places tuple μ 0 + 1 ≤
      actualTupleHullLogVolume (p := p) places tuple μ 0 :=
    actualTupleLogVolumeSet_subset_Iic (p := p) places tuple μ hmem
  linarith

/-- No actual possible-image initial segment is the whole real line. -/
theorem actualTuplePossibleImage_ne_univ (n : Nat) :
    actualTuplePossibleImage (p := p) places tuple μ n ≠ Set.univ := by
  intro h
  have hmem : actualTupleHullLogVolume (p := p) places tuple μ 0 + 1 ∈
      actualTuplePossibleImage (p := p) places tuple μ n := by
    rw [h]
    exact Set.mem_univ _
  have hsub := actualTuplePossibleImage_subset_logVolumeSet (p := p) places tuple μ n hmem
  have hle : actualTupleHullLogVolume (p := p) places tuple μ 0 + 1 ≤
      actualTupleHullLogVolume (p := p) places tuple μ 0 :=
    actualTupleLogVolumeSet_subset_Iic (p := p) places tuple μ hsub
  linarith

/-- Exact description of the actual possible-image initial segment as the
ambient range cut at the current scale. -/
theorem actualTuplePossibleImage_eq_logVolumeSet_inter_Ici (n : Nat) :
    actualTuplePossibleImage (p := p) places tuple μ n =
      actualTupleLogVolumeSet (p := p) places tuple μ ∩
        Set.Ici (actualTupleHullLogVolume (p := p) places tuple μ n) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Set.mem_range_self k,
      actualTupleHullLogVolume_antitone (p := p) places tuple μ hk⟩
  · rintro ⟨⟨k, rfl⟩, hkn⟩
    have hk : k ≤ n := by
      by_contra hnot
      have hnk : n < k := Nat.lt_of_not_ge hnot
      have hlt := actualTupleHullLogVolume_strictAnti (p := p) places tuple μ hnk
      exact (not_lt_of_ge hkn) hlt
    exact ⟨k, hk, rfl⟩

/-- The actual possible-image initial segment is up-closed inside the actual
log-volume range.  This is the first of the three characterization conditions. -/
theorem actualTuplePossibleImage_upClosedIn :
    FamilyUpClosedIn (actualTupleLogVolumeSet (p := p) places tuple μ)
      (actualTuplePossibleImage (p := p) places tuple μ) := by
  intro n x hx y hy hxy
  rcases hx with ⟨k, hk, rfl⟩
  rcases hy with ⟨j, rfl⟩
  have hjn : j ≤ n := by
    by_contra h
    have hnj : n < j := Nat.lt_of_not_ge h
    have hvolj : actualTupleHullLogVolume (p := p) places tuple μ j <
        actualTupleHullLogVolume (p := p) places tuple μ n :=
      actualTupleHullLogVolume_strictAnti (p := p) places tuple μ hnj
    have hvoln : actualTupleHullLogVolume (p := p) places tuple μ n ≤
        actualTupleHullLogVolume (p := p) places tuple μ k :=
      actualTupleHullLogVolume_antitone (p := p) places tuple μ hk
    exact (not_lt_of_ge hxy) (lt_of_lt_of_le hvolj hvoln)
  exact ⟨j, hjn, rfl⟩

/-- Every actual possible-image initial segment is bounded below.  This is the
second characterization condition. -/
theorem actualTuplePossibleImage_bddBelow (n : Nat) :
    BddBelow (actualTuplePossibleImage (p := p) places tuple μ n) := by
  refine ⟨actualTupleHullLogVolume (p := p) places tuple μ n, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  exact actualTupleHullLogVolume_antitone (p := p) places tuple μ hk

/-- The infimum of the actual possible-image initial segment is its first
element.  This is the third characterization condition. -/
theorem actualTuplePossibleImage_sInf_eq (n : Nat) :
    sInf (actualTuplePossibleImage (p := p) places tuple μ n) =
      actualTupleHullLogVolume (p := p) places tuple μ n := by
  apply le_antisymm
  · exact csInf_le (actualTuplePossibleImage_bddBelow (p := p) places tuple μ n)
      ⟨n, le_rfl, rfl⟩
  · exact le_csInf (actualTuplePossibleImage_nonempty (p := p) places tuple μ n)
      (fun x hx => by
        rcases hx with ⟨k, hk, rfl⟩
        exact actualTupleHullLogVolume_antitone (p := p) places tuple μ hk)

/-- The infimum of every actual possible-image initial segment belongs to it. -/
theorem actualTuplePossibleImage_sInf_mem (n : Nat) :
    sInf (actualTuplePossibleImage (p := p) places tuple μ n) ∈
      actualTuplePossibleImage (p := p) places tuple μ n := by
  rw [actualTuplePossibleImage_sInf_eq]
  exact ⟨n, le_rfl, rfl⟩

/-- The actual tuple hull-volume family attains the family cut on its actual
log-volume range. -/
theorem actualTuplePossibleImage_familyCutAttained :
    FamilyCutAttainedIn (actualTupleLogVolumeSet (p := p) places tuple μ)
      (actualTuplePossibleImage (p := p) places tuple μ) :=
  (HullPresentationFamilyCutActual.familyCutAttainedIn_iff_upClosedIn_and_sInf_mem
    (L := actualTupleLogVolumeSet (p := p) places tuple μ)
    (S := actualTuplePossibleImage (p := p) places tuple μ)
    (actualTuplePossibleImage_nonempty (p := p) places tuple μ)).mpr
    ⟨actualTuplePossibleImage_upClosedIn (p := p) places tuple μ,
      actualTuplePossibleImage_bddBelow (p := p) places tuple μ,
      fun n _ => actualTuplePossibleImage_sInf_mem (p := p) places tuple μ n⟩

end ActualHullVolumes

section Packet

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{s} l)

/-- A shape procession for the actual tuple packet.  The source theater is the
canonical identity theater built from the supplied Definition 3.1 datum,
`ind3` lowers the scale index, and the horizontal actions are identities.
This is not the paper's full LGP procession. -/
noncomputable def actualTupleProcession :
    SourceLGPProcession l (ULift.{s} ℤ) Nat where
  hodge := SourceProcessionAttack.canonicalSourceHodgeTheaterSystem (Choice := Nat) S
  base := 0
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun _ c => c
  ind3 := fun n c => c - n
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => by simp
  ind3_add := fun m n c => by
    rw [Nat.sub_sub]
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => le_rfl
  source_index := fun _ => (0 : Nat)
  ind1_index := fun _ _ => rfl
  ind2_index := fun _ _ => rfl
  ind3_index := fun _ _ => rfl

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

/-- The actual finite-place tuple/hull packet.  Its carrier is the actual tensor
block, its determinant is the actual Haar measure of the scaled canonical hull,
and its possible-image family is the actual hull-volume initial segment. -/
noncomputable def actualTuplePacket :
    SourcePacketRealization (actualTupleProcession (l := l) S) where
  carrier := fun _ => ArithmeticTensorTupleBlock places tuple
  distinguished := fun _ => 0
  logVolume := actualTupleHullLogVolume (p := p) places tuple μ
  determinant := actualTupleHullMeasure (p := p) places tuple μ
  determinant_positive := actualTupleHullMeasure_pos (p := p) places tuple μ
  log_determinant := fun _ => rfl
  possibleImage := actualTuplePossibleImage (p := p) places tuple μ
  possibleImage_nonempty := actualTuplePossibleImage_nonempty (p := p) places tuple μ
  ind1_volume := fun _ _ => rfl
  ind2_volume := fun _ _ => rfl
  ind3_volume := fun n c =>
    actualTupleHullLogVolume_antitone (p := p) places tuple μ (Nat.sub_le c n)
  ind1_determinant := fun _ _ => rfl
  ind2_determinant := fun _ _ => rfl
  ind3_determinant := fun n c =>
    actualTupleHullMeasure_antitone (p := p) places tuple μ (Nat.sub_le c n)
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := fun n c z hz => by
    rcases hz with ⟨k, hk, rfl⟩
    by_cases hkn : k ≤ c - n
    · exact ⟨actualTupleHullLogVolume (p := p) places tuple μ k,
        ⟨k, hkn, rfl⟩, le_rfl⟩
    · have hnk : c - n < k := Nat.lt_of_not_ge hkn
      exact ⟨actualTupleHullLogVolume (p := p) places tuple μ (c - n),
        ⟨c - n, le_rfl, rfl⟩,
        le_of_lt (actualTupleHullLogVolume_strictAnti (p := p) places tuple μ hnk)⟩

/-- The actual tuple packet attains the family cut on its actual hull-volume
range. -/
theorem actualTuplePacket_familyCutAttained :
    FamilyCutAttainedIn (actualTupleLogVolumeSet (p := p) places tuple μ)
      (actualTuplePacket (l := l) S places tuple μ).possibleImage := by
  simpa [actualTuplePacket] using
    actualTuplePossibleImage_familyCutAttained (p := p) places tuple μ

/-- The nonempty attained hull cut, derived from the actual family cut. -/
theorem actualTuplePacket_nonempty_attainedHullCut :
    Nonempty (HullPresentationAdoption.AttainedHullCut
      (actualTuplePacket (l := l) S places tuple μ)
      (actualTupleLogVolumeSet (p := p) places tuple μ)) :=
  (HullPresentationAdoption.nonempty_attainedHullCut_iff_familyCutAttainedIn
    (actualTuplePacket (l := l) S places tuple μ)
    (actualTupleLogVolumeSet (p := p) places tuple μ)).mpr
    (actualTuplePacket_familyCutAttained (l := l) S places tuple μ)

/-- The gap-card form of the actual attained cut. -/
theorem actualTuplePacket_hullCutAttainmentGap :
    HullPresentationAdoption.HullCutAttainmentGap
      (actualTuplePacket (l := l) S places tuple μ)
      (actualTupleLogVolumeSet (p := p) places tuple μ) :=
  actualTuplePacket_nonempty_attainedHullCut (l := l) S places tuple μ

end Packet

/-! ## Missing source bridge card (not assumed)

For fixed `l`, a place type `V`, a source input `I : OriginalInput l V`, a
place `v : V`, a source-image realization `R : I.SourceImageRealization v`,
and a scale map `σ : Nat → ThetaPilotCarrier l`, a genuine source
realization of the paper's possible-image family would require the following
data and equalities.

1. A map `φ : ArithmeticTensorTupleBlock places tuple → I.ThetaPilotPoint v`
   (or a family of maps on the scaled hulls).
2. Log-degree compatibility: for every `n`,
   `actualTupleHullLogVolume n = I.sourceLocalLogDegree v (φ (x n))`
   for a chosen `x n ∈ arithmeticTuplePowerScaledHull n`.
3. Possible-image compatibility: for every `n`,
   `actualTuplePossibleImage n =
      { y : Real | ∃ k ≤ n,
          y = Real.log (I.sourceSetVolume v
            (I.possibleThetaPilotImageSet v R (σ k))).toReal }`.
4. Hull compatibility: for every `n`,
   `actualTupleHullLogVolume n =
      Real.log (I.sourceHullVolume v R (σ n)).toReal`,
   where `I.sourceHullVolume v R (σ n)` is by definition
   `I.sourceSetVolume v (I.sourceHolomorphicHull v R (σ n))`.

The map `σ` cannot be injective: `ThetaPilotCarrier l = Fin (lStar l.value + 1)`
is finite, while the scale index `Nat` is infinite.  A genuine bridge must
therefore restrict the scale index or prove a periodic/stable identification.
None of the maps or equalities above is constructed or assumed in this file.
-/

/-! ## Axiom probe -/

#print axioms arithmeticTuplePowerScale
#print axioms arithmeticTuplePowerScaledHull
#print axioms actualTupleHullMeasure
#print axioms actualTupleHullLogVolume
#print axioms arithmeticTuplePowerScaledHull_measure_pos_lt_top
#print axioms actualTupleHullMeasure_pos
#print axioms actualTupleHullLogVolume_succ
#print axioms actualTupleHullLogVolume_eq
#print axioms real_log_prime_pos
#print axioms actualTupleHullLogVolume_strictAnti
#print axioms actualTupleHullLogVolume_antitone
#print axioms actualTupleHullLogVolume_ne_zero_one
#print axioms actualTupleHullMeasure_antitone
#print axioms actualTuplePossibleImage
#print axioms actualTupleLogVolumeSet
#print axioms actualTuplePossibleImage_nonempty
#print axioms actualTuplePossibleImage_subset_logVolumeSet
#print axioms actualTupleLogVolumeSet_subset_Iic
#print axioms actualTupleLogVolumeSet_ne_univ
#print axioms actualTuplePossibleImage_ne_univ
#print axioms actualTuplePossibleImage_eq_logVolumeSet_inter_Ici
#print axioms actualTuplePossibleImage_upClosedIn
#print axioms actualTuplePossibleImage_bddBelow
#print axioms actualTuplePossibleImage_sInf_eq
#print axioms actualTuplePossibleImage_sInf_mem
#print axioms actualTuplePossibleImage_familyCutAttained
#print axioms actualTupleProcession
#print axioms actualTuplePacket
#print axioms actualTuplePacket_familyCutAttained
#print axioms actualTuplePacket_nonempty_attainedHullCut
#print axioms actualTuplePacket_hullCutAttainmentGap

end HullPresentationActualTuplePacket
end K1K2Realization
end LeanFormal.IUT
