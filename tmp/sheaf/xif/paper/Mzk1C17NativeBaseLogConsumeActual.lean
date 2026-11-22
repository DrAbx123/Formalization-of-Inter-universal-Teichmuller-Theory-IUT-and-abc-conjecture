/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17NativeBaseResidueOneActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseLogConsumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem log_residue_nativeBase_eq_of_input
    (h : NativeBaseResidueFieldEquivInput T)
    (b : Bad (nativePlaceSelection T)) :
    Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
      Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b))) := by
  have hf := localResidueDegree_nativeBase_eq_one_of_input T h b
  rw [log_residue_sectionK_eq_degree_mul, hf]
  norm_num


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseLogConsumeActual
