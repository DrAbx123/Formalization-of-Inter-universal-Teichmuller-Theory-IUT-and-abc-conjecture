import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Relative Haar log-mass under an actual topological group isomorphism

Haar uniqueness supplies a positive scaling constant on sets with compact
closure. Normalization by a second positive finite-mass region cancels this
constant. Positivity is retained explicitly: the total convention log(0)=0
does not obey this cancellation law for a zero-mass region.
-/

namespace LeanFormal.IUT.NormalizedHaarTransport

open MeasureTheory

noncomputable section

variable {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
variable [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]

theorem measure_eq_haarScalarFactor_mul_image
    (e : G ≃ₜ+ H) (μ : Measure G) (ν : Measure H)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S : Set G} (hS : IsCompact (closure S)) :
    μ S = ((μ.map e).addHaarScalarFactor ν : ENNReal) * ν (e '' S) := by
  letI : Measure.IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  have hmass : (μ.map e) (e '' S) = μ S := by
    change (μ.map e.toHomeomorph.toMeasurableEquiv) (e '' S) = μ S
    rw [MeasurableEquiv.map_apply]
    congr 1
    exact Set.preimage_image_eq _ e.injective
  rw [← hmass]
  exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure (μ.map e) ν
    ((hS.image e.continuous).closure_of_subset (Set.image_mono subset_closure))

theorem relative_log_mass_image_eq
    (e : G ≃ₜ+ H) (μ : Measure G) (ν : Measure H)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S C : Set G} (hS : IsCompact (closure S)) (hC : IsCompact (closure C))
    (hSpos : 0 < μ S) (hCpos : 0 < μ C) :
    Real.log (ν (e '' S)).toReal - Real.log (ν (e '' C)).toReal =
      Real.log (μ S).toReal - Real.log (μ C).toReal := by
  letI : Measure.IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  let c := (μ.map e).addHaarScalarFactor ν
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hSscale : μ S = (c : ENNReal) * ν (e '' S) :=
    measure_eq_haarScalarFactor_mul_image e μ ν hS
  have hCscale : μ C = (c : ENNReal) * ν (e '' C) :=
    measure_eq_haarScalarFactor_mul_image e μ ν hC
  have hSimagene : ν (e '' S) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hSscale
    exact hSpos.ne' hSscale
  have hCimagene : ν (e '' C) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hCscale
    exact hCpos.ne' hCscale
  have hSimagefin : ν (e '' S) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono subset_closure))
      (hS.image e.continuous).measure_lt_top
  have hCimagefin : ν (e '' C) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono subset_closure))
      (hC.image e.continuous).measure_lt_top
  rw [hSscale, hCscale]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul hc (ENNReal.toReal_pos hSimagene hSimagefin.ne).ne',
    Real.log_mul hc (ENNReal.toReal_pos hCimagene hCimagefin.ne).ne']
  ring

end

end LeanFormal.IUT.NormalizedHaarTransport
