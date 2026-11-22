/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1GeneratorValuationRelationActual
import tmp.sheaf.xif.paper.Mzk1P1CountValuationSignActual
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

namespace LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationSignIffActual

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

theorem localValuation_neg_iff_count_pos
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (h : CountValuationBridge (k := k) d) :
    localValuation v d.generator < 0 ↔ 0 < countExponent v I := by
  have hval : localValuation v d.generator = - (countExponent v I : Int) := h
  rw [hval]
  omega


end LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationSignIffActual
