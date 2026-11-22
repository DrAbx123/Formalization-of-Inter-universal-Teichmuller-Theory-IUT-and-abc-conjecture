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

namespace S1552Probe15

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
  let μ : Measure (Completion P) := ν.map e.symm
  haveI hνreg : Measure.Regular ν := inferInstance
  haveI hμ : Measure.IsAddHaarMeasure μ :=
    AddEquiv.isAddHaarMeasure_map ν e.symm.toAddEquiv he' he
  haveI hreg : Measure.Regular μ := by
    change (Measure.map eHomeo.symm ν).Regular
    exact Measure.Regular.map eHomeo.symm
  let T : Set ℚ_[pP] := Metric.closedBall (0 : ℚ_[pP]) 1
  let S : Set (Completion P) := e.symm '' T
  have hTpos : 0 < ν T := by
    apply Measure.measure_pos_of_nonempty_interior ν
    refine ⟨0, ?_⟩
    refine mem_interior_iff_mem_nhds.mpr ?_
    exact Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (by simp : (0 : ℚ_[pP]) ∈ Metric.ball 0 1))
      (by simp [T, Metric.ball_subset_closedBall])
  have hTfin : ν T < ⊤ := by
    simp only [T]
    exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.measure_lt_top
  have hSmeas : MeasurableSet (u • S) := by
    have hScompact : IsCompact S := by
      simp only [S, T]
      exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.image he'
    have hcont : Continuous (fun x : Completion P => (u : Completion P) * x) :=
      continuous_const.mul continuous_id
    exact (hScompact.image hcont).isClosed.measurableSet
  have hmapT : (Measure.map e.symm ν) (e.symm '' T) = ν T := by
    have hSmeasT : MeasurableSet (e.symm '' T) := by
      have hc : IsCompact (e.symm '' T) := by
        simp only [T]
        exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.image he'
      exact hc.isClosed.measurableSet
    rw [show (Measure.map e.symm ν) (e.symm '' T) =
        ν (e.symm ⁻¹' (e.symm '' T)) from
      Measure.map_apply (μ := ν) (f := e.symm) he'.measurable hSmeasT]
    rw [Set.preimage_image_eq _ e.symm.injective]
  have hST : μ S = ν T := by
    simp only [S, μ]
    exact hmapT
  have hSpos : 0 < μ S := by rw [hST]; exact hTpos
  have hSfin : μ S < ⊤ := by rw [hST]; exact hTfin
  have hscale : μ (u • S) = (distribHaarChar ℚ_[pP] (Units.map e.toMonoidHom u)) * μ S := by
    have hmap : e '' (u • S) = (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T := by
      ext y
      constructor
      · rw [Set.mem_smul_set]
        rintro ⟨x, hx, hxy⟩
        subst hxy
        rw [Set.mem_smul_set] at hx
        rcases hx with ⟨s, hs, hsmul⟩
        subst hsmul
        simp only [S, T] at hs
        rcases hs with ⟨t, ht, rfl⟩
        refine ⟨t, ht, ?_⟩
        calc
          (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • t = (e u : ℚ_[pP]) * t := by
            change ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) : ℚ_[pP]) * t = (e u : ℚ_[pP]) * t
            rfl
          _ = e u * e (e.symm t) := by rw [e.apply_symm_apply]
          _ = e (u * e.symm t) := by rw [map_mul]
          _ = e (u • e.symm t) := rfl
      · rw [Set.mem_smul_set]
        rintro ⟨t, ht, hty⟩
        subst hty
        rw [Set.mem_image]
        refine ⟨(u : Completion P) * e.symm t, ?_, ?_⟩
        · rw [Set.mem_smul_set]
          exact ⟨e.symm t, by simp only [S, T]; exact ⟨t, ht, rfl⟩, rfl⟩
        · calc
            e ((u : Completion P) * e.symm t) = e u * e (e.symm t) := by rw [map_mul]
            _ = e u * t := by rw [e.apply_symm_apply]
            _ = (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • t := by
              change (e u : ℚ_[pP]) * t = ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) : ℚ_[pP]) * t
              rfl
    have hpre : e.symm ⁻¹' (u • S) = e '' (u • S) :=
      (e.image_eq_preimage_symm (u • S)).symm
    have hcalc : μ (u • S) = ν ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T) := by
      calc
        μ (u • S) = ν (e.symm ⁻¹' (u • S)) := by
          change (Measure.map e.symm ν) (u • S) = _
          exact Measure.map_apply (μ := ν) (f := e.symm) he'.measurable hSmeas
        _ = ν (e '' (u • S)) := by rw [hpre]
        _ = ν ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T) := by rw [hmap]
    rw [hcalc, hST]
    exact (distribHaarChar_mul ν (Units.map e.toMonoidHom u) T).symm
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hSpos.ne' hSfin.ne hscale

end S1552Probe15
