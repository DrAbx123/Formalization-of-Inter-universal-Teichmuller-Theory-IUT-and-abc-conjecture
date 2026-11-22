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

namespace S1552Probe12

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

local instance instAlgebraRatCompletionAux (P : NumberField.FinitePlace ℚ) :
    Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)

local instance factTargetPrime (P : NumberField.FinitePlace ℚ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

noncomputable def ringEquivCompletionPadic (P : NumberField.FinitePlace ℚ) :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val])

theorem distribHaarChar_completionPadic
    (P : NumberField.FinitePlace ℚ)
    (u : (Completion P)ˣ) :
    distribHaarChar (Completion P) u =
      distribHaarChar ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val]
        (Units.map (ringEquivCompletionPadic P).toMonoidHom u) := by
  let pP : ℕ := (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val
  letI : Fact (Nat.Prime pP) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩
  letI : MeasurableSpace ℚ_[pP] := borel ℚ_[pP]
  letI : BorelSpace ℚ_[pP] := ⟨rfl⟩
  let e : Completion P ≃+* ℚ_[pP] := ringEquivCompletionPadic P
  have he : Continuous e :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).continuous
  have he' : Continuous e.symm :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).symm.continuous
  let eHomeo : Completion P ≃ₜ ℚ_[pP] :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let ν : Measure ℚ_[pP] := Measure.addHaar
  let μ : Measure (Completion P) := ν.map eHomeo.symm
  haveI hνreg : Measure.Regular ν := inferInstance
  haveI hμ : Measure.IsAddHaarMeasure μ :=
    AddEquiv.isAddHaarMeasure_map ν e.symm.toAddEquiv he' he
  haveI hreg : Measure.Regular μ := by
    change (Measure.map eHomeo.symm ν).Regular
    exact Measure.Regular.map eHomeo.symm
  let T : Set ℚ_[pP] := Metric.closedBall (0 : ℚ_[pP]) 1
  let S : Set (Completion P) := eHomeo.symm '' T
  have hTpos : 0 < ν T := by
    apply Measure.measure_pos_of_nonempty_interior ν
    refine ⟨0, ?_⟩
    refine mem_interior_iff_mem_nhds.mpr ?_
    exact Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball])
  have hTfin : ν T < ⊤ := isCompact_closedBall (0 : ℚ_[pP]) 1 |>.measure_lt_top
  have hSpos : 0 < μ S := by
    change 0 < (Measure.map eHomeo.symm ν) (eHomeo.symm '' T)
    rw [Measure.map_apply eHomeo.symm.measurable (Metric.isClosed_closedBall.measurableSet)]
    simpa [Set.preimage_image_eq T eHomeo.symm.injective] using hTpos
  have hSfin : μ S < ⊤ := by
    change (Measure.map eHomeo.symm ν) (eHomeo.symm '' T) < ⊤
    rw [Measure.map_apply eHomeo.symm.measurable (Metric.isClosed_closedBall.measurableSet)]
    simpa [Set.preimage_image_eq T eHomeo.symm.injective] using hTfin
  have hSmeas : MeasurableSet (u • S) := by
    have hScompact : IsCompact S :=
      isCompact_closedBall (0 : ℚ_[pP]) 1 |>.image eHomeo.symm.continuous
    have hcont : Continuous (fun x : Completion P => (u : Completion P) * x) :=
      continuous_const.mul continuous_id
    exact (hScompact.image hcont).isClosed.measurableSet
  have hscale : μ (u • S) = (distribHaarChar ℚ_[pP] (Units.map e.toMonoidHom u)) * μ S := by
    have hmap : e '' (u • S) = (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨s, hs, rfl⟩
        refine ⟨e s, hs, ?_⟩
        change e ((u : Completion P) * s) = (e u) * e s
        rw [map_mul]
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(u : Completion P) * e.symm t, ?_, ?_⟩
        · exact ⟨e.symm t, ht, rfl⟩
        · change e ((u : Completion P) * e.symm t) = e u * t
          rw [map_mul, e.apply_symm_apply]
    have hpre : eHomeo.symm ⁻¹' (u • S) = e '' (u • S) := by
      rw [show eHomeo.symm = (e : Completion P ≃+* ℚ_[pP]).symm from rfl]
      rw [e.image_eq_preimage_symm]
    have hST : μ S = ν T := by
      change (Measure.map eHomeo.symm ν) (eHomeo.symm '' T) = ν T
      rw [Measure.map_apply eHomeo.symm.measurable (Metric.isClosed_closedBall.measurableSet)]
      simp [Set.preimage_image_eq T eHomeo.symm.injective]
    calc
      μ (u • S) = ν (eHomeo.symm ⁻¹' (u • S)) := by
        rw [Measure.map_apply eHomeo.symm.measurable hSmeas]
      _ = ν (e '' (u • S)) := by rw [hpre]
      _ = ν ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T) := by rw [hmap]
      _ = (distribHaarChar ℚ_[pP] (Units.map e.toMonoidHom u)) * ν T :=
        (distribHaarChar_mul ν (Units.map e.toMonoidHom u) T).symm
      _ = (distribHaarChar ℚ_[pP] (Units.map e.toMonoidHom u)) * μ S := by rw [hST]
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hSpos.ne' hSfin.ne hscale

end S1552Probe12
