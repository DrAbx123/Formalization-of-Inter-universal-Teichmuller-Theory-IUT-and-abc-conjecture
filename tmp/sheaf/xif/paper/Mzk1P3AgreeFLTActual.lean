/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Tactic

/-! # P3 AGREE-RAM / AGREE-FIELD via FLT completion BaseChange -/

noncomputable section
open scoped WithZero Valued TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 200000

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AgreeFLTActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable [FiniteDimensional k K] [Algebra.IsSeparable k K]
variable [Algebra (NumberField.RingOfIntegers k) K]
variable [IsScalarTower (NumberField.RingOfIntegers k) k K]
variable [IsScalarTower (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) K]
variable [IsScalarTower ℤ (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [Module.Finite (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [Module.IsTorsionFree (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [IsIntegralClosure (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers k) K]

instance instAlgebraIsIntegralRingOfIntegers :
    Algebra.IsIntegral (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) :=
  Algebra.IsIntegral.tower_top (R := ℤ)

noncomputable def lowerPlace (place : NumberField.FinitePlace K) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
  (comap (k := k) place).maximalIdeal

noncomputable def placeExtension (place : NumberField.FinitePlace K) :
    (lowerPlace (k := k) place).Extension (NumberField.RingOfIntegers K) :=
  ⟨place.maximalIdeal, by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change (place.maximalIdeal.asIdeal.under (NumberField.RingOfIntegers k)) =
      ((comap (k := k) place).maximalIdeal.asIdeal)
    rw [Ideal.under_def, NumberFieldFinitePlace.comap_maximalIdeal]⟩

theorem localRamificationIndex_eq_relativeRamificationIndex
    (place : NumberField.FinitePlace K) :
    localRamificationIndex (k := k) place = relativeRamificationIndex (k := k) place := by
  let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    lowerPlace (k := k) place
  let w : v.Extension (NumberField.RingOfIntegers K) := placeExtension (k := k) place
  have hlies : (w.1.completionIdeal K).LiesOver (v.completionIdeal k) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.liesOver_completionIdeal
      (K := k) (L := K) (w := w)
  have h := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_eq_ramificationIdx
    (K := k) (L := K) (w := w)
  haveI hliesI := hlies
  have hloc : localRamificationIndex (k := k) place =
      (w.1.completionIdeal K).ramificationIdx (v.adicCompletionIntegers k) := by
    unfold localRamificationIndex
    change (v.completionIdeal k).ramificationIdx' (w.1.completionIdeal K) = _
    haveI : IsScalarTower (v.adicCompletionIntegers k) (w.1.adicCompletionIntegers K)
        (w.1.adicCompletion K) := .of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower (v.adicCompletionIntegers k) (v.adicCompletion k)
        (w.1.adicCompletion K) := .of_algebraMap_smul fun _ _ => rfl
    haveI : FaithfulSMul (v.adicCompletionIntegers k) (w.1.adicCompletionIntegers K) :=
      FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion k) (w.1.adicCompletion K)
    exact Ideal.ramificationIdx'_eq_ramificationIdx (v.completionIdeal k)
      (w.1.completionIdeal K) (v.completionIdeal_ne_bot k)
  have hrel : relativeRamificationIndex (k := k) place =
      w.1.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) := by
    unfold relativeRamificationIndex
    change (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
      place.maximalIdeal.asIdeal = place.maximalIdeal.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k)
    haveI : (place.maximalIdeal.asIdeal).LiesOver
        ((comap (k := k) place).maximalIdeal.asIdeal) :=
      ⟨by rw [Ideal.under_def, NumberFieldFinitePlace.comap_maximalIdeal]⟩
    exact Ideal.ramificationIdx'_eq_ramificationIdx
      ((comap (k := k) place).maximalIdeal.asIdeal) place.maximalIdeal.asIdeal
      ((comap (k := k) place).maximalIdeal.ne_bot)
  exact hloc.trans (h.trans hrel.symm)

theorem localInertiaDegree_eq_relativeResidueDegree
    (place : NumberField.FinitePlace K) :
    localInertiaDegree (k := k) place = relativeResidueDegree (k := k) place := by
  let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    lowerPlace (k := k) place
  let w : v.Extension (NumberField.RingOfIntegers K) := placeExtension (k := k) place
  have hlies : (w.1.completionIdeal K).LiesOver (v.completionIdeal k) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.liesOver_completionIdeal
      (K := k) (L := K) (w := w)
  have h := IsDedekindDomain.HeightOneSpectrum.adicCompletion.inertiaDeg_eq_inertiaDeg
    (K := k) (L := K) (w := w)
  haveI hliesI := hlies
  haveI hpmax : (v.completionIdeal k).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal (v.adicCompletionIntegers k)
  haveI hqmax : (w.1.completionIdeal K).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal (w.1.adicCompletionIntegers K)
  have hloc : localInertiaDegree (k := k) place =
      (w.1.completionIdeal K).inertiaDeg (v.adicCompletionIntegers k) := by
    unfold localInertiaDegree
    change (v.completionIdeal k).inertiaDeg' (w.1.completionIdeal K) = _
    exact Ideal.inertiaDeg'_eq_inertiaDeg (v.completionIdeal k) (w.1.completionIdeal K)
  have hrel : relativeResidueDegree (k := k) place =
      w.1.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    unfold relativeResidueDegree
    change (comap (k := k) place).maximalIdeal.asIdeal.inertiaDeg'
      place.maximalIdeal.asIdeal = place.maximalIdeal.asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k)
    haveI : (place.maximalIdeal.asIdeal).LiesOver
        ((comap (k := k) place).maximalIdeal.asIdeal) :=
      ⟨by rw [Ideal.under_def, NumberFieldFinitePlace.comap_maximalIdeal]⟩
    haveI hpm : ((comap (k := k) place).maximalIdeal.asIdeal).IsMaximal :=
      (comap (k := k) place).maximalIdeal.isPrime.isMaximal
        (comap (k := k) place).maximalIdeal.ne_bot
    haveI hqm : (place.maximalIdeal.asIdeal).IsMaximal :=
      place.maximalIdeal.isPrime.isMaximal place.maximalIdeal.ne_bot
    exact Ideal.inertiaDeg'_eq_inertiaDeg
      ((comap (k := k) place).maximalIdeal.asIdeal) place.maximalIdeal.asIdeal
  exact hloc.trans (h.symm.trans hrel.symm)

theorem localDataAgreesWithPlaceData_of_implies
    (place : NumberField.FinitePlace K) :
    localDataAgreesWithPlaceData (k := k) place :=
  ⟨localRamificationIndex_eq_relativeRamificationIndex place,
    localInertiaDegree_eq_relativeResidueDegree place⟩

def agreeFLTRows : List (String × String × String) :=
  [ ("AGREE-RAM", "ramificationIdx via FLT BaseChange:685", "PROVED (conditional)"),
    ("AGREE-FIELD", "inertiaDeg via FLT BaseChange:721", "PROVED (conditional)"),
    ("AGREE", "localDataAgreesWithPlaceData_of_implies", "PROVED (conditional)") ]

theorem agreeFLTRows_length : agreeFLTRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3AgreeFLTActual

end