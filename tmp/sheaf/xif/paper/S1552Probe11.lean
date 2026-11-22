import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

namespace S1552Probe11

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

theorem distribHaarChar_ringEquiv
    {A B : Type*} [Ring A] [Ring B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    [LocallyCompactSpace A] [LocallyCompactSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (u : Aˣ) :
    distribHaarChar A u =
      distribHaarChar B (Units.map e.toMonoidHom u) := by
  let eHomeo : A ≃ₜ B :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let ν : Measure B := Measure.addHaar
  let μ : Measure A := ν.map e.symm
  haveI hμ : Measure.IsAddHaarMeasure μ :=
    AddEquiv.isAddHaarMeasure_map ν e.symm.toAddEquiv he' he
  haveI hreg : Measure.Regular μ := by
    change (ν.map eHomeo.symm).Regular
    exact Measure.Regular.map ν eHomeo.symm
  let T : Set B := Metric.closedBall (0 : B) 1
  let S : Set A := e.symm '' T
  have hTpos : 0 < ν T := by
    apply Measure.measure_pos_of_nonempty_interior ν
    refine ⟨0, ?_⟩
    refine mem_interior_iff_mem_nhds.mpr ?_
    exact Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball])
  have hTfin : ν T < ⊤ := Metric.isCompact_closedBall (0 : B) 1 |>.measure_lt_top
  have hSpos : 0 < μ S := by
    change 0 < (ν.map e.symm) (e.symm '' T)
    rw [Measure.map_apply (eHomeo.symm.measurable) (Metric.isClosed_closedBall.measurableSet)]
    · simpa using hTpos
  have hSfin : μ S < ⊤ := by
    change (ν.map e.symm) (e.symm '' T) < ⊤
    rw [Measure.map_apply (eHomeo.symm.measurable) (Metric.isClosed_closedBall.measurableSet)]
    · simpa using hTfin
  have hSmeas : MeasurableSet (u • S) := by
    have hScompact : IsCompact S :=
      Metric.isCompact_closedBall (0 : B) 1 |>.image eHomeo.symm.continuous
    exact (hScompact.image (continuous_const.mul continuous_id)).isClosed.measurableSet
  have hscale : μ (u • S) = (distribHaarChar B (Units.map e.toMonoidHom u)) * μ S := by
    have hmap : e '' (u • S) = (Units.map e.toMonoidHom u : Bˣ) • T := by
      ext y
      constructor
      · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨e s, hs, by
          change e ((u : A) * s) = (e u) * e s
          rw [map_mul]⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(u : A) * e.symm t, ⟨e.symm t, ht, rfl⟩, ?_⟩
        change e ((u : A) * e.symm t) = e u * t
        rw [map_mul, e.apply_symm_apply]
    have hmap2 : e.symm ⁻¹' (u • S) = e '' (u • S) := by
      rw [e.image_eq_preimage_symm]
    have hmap3 : μ S = ν T := by
      change (ν.map e.symm) (e.symm '' T) = ν T
      rw [Measure.map_apply (eHomeo.symm.measurable) (Metric.isClosed_closedBall.measurableSet)]
      simp [Set.preimage_image_eq _ e.symm.injective]
    calc
      μ (u • S) = ν (e.symm ⁻¹' (u • S)) := by
        rw [Measure.map_apply (eHomeo.symm.measurable) hSmeas]
      _ = ν (e '' (u • S)) := by rw [hmap2]
      _ = ν ((Units.map e.toMonoidHom u : Bˣ) • T) := by rw [hmap]
      _ = (distribHaarChar B (Units.map e.toMonoidHom u)) * ν T :=
        (distribHaarChar_mul ν (Units.map e.toMonoidHom u) T).symm
      _ = (distribHaarChar B (Units.map e.toMonoidHom u)) * μ S := by rw [hmap3]
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hSpos.ne' hSfin.ne hscale

end S1552Probe11
