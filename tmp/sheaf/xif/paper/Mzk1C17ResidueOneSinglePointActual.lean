/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import Mathlib.Tactic

/-! # C17 residue-one: single-point log-residue equivalence -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem localResidueDegree_eq_one_iff_log_residue_eq
    (b : Bad (nativePlaceSelection T)) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 ↔
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))) := by
  rw [log_residue_sectionK_eq_degree_mul]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have hpos : 0 < Real.log (residueNormBase
        (comap (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b))) :=
      log_residueNormBase_pos _
    have hf : (localResidueDegree (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b) : Real) = 1 := by
      nlinarith [hpos, h]
    exact_mod_cast hf
theorem localResidueDegree_eq_one_of_log_residue_eq
    (b : Bad (nativePlaceSelection T))
    (h : Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b)))) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 :=
  (localResidueDegree_eq_one_iff_log_residue_eq T b).mpr h
theorem localResidueDegree_qVFam_eq_one_iff_log_residue_eq
    (b : Bad (nativePlaceSelection T)) :
    localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1 ↔
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b))) := by
  rw [log_residue_nativeF_eq_degree_mul]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have hpos : 0 < Real.log (residueNormBase
        (comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b))) :=
      log_residueNormBase_pos _
    have hf : (localResidueDegree (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b) : Real) = 1 := by
      nlinarith [hpos, h]
    exact_mod_cast hf

end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
