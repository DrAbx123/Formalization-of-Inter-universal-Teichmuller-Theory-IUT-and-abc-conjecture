/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneSinglePointActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1P1CountValuationSignActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneSinglePointActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import tmp.sheaf.xif.paper.Mzk1B5HproductGeneralAttemptActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorValuationRelationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothSidesActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1CountValuationSignActual

variable {l : PrimeGeFive}
variable {k : Type} [Field k] [NumberField k]
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem residueOne_nativeBase_iff_log
    (b : Bad (nativePlaceSelection T)) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 ↔
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))) :=
  localResidueDegree_eq_one_iff_log_residue_eq T b
theorem residueOne_qVFam_iff_log
    (b : Bad (nativePlaceSelection T)) :
    localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = 1 ↔
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b))) :=
  localResidueDegree_qVFam_eq_one_iff_log_residue_eq T b


end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneBothSidesActual
