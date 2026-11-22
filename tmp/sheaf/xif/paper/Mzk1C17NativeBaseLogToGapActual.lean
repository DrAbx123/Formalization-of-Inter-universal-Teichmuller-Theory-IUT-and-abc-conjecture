/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17NativeBaseLogConsumeActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseLogToGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseLogConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapLogActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
theorem resNormDegreeGap_of_nativeBaseInput_and_qVFamLog
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : ∀ b : Bad (nativePlaceSelection T),
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b)))) :
    ResNormDegreeGap T :=
  resNormDegreeGap_of_log_residue_eq T
    (fun b => log_residue_nativeBase_eq_of_input T hbase b) hF


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseLogToGapActual
