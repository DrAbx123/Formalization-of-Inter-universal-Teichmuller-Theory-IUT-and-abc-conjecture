/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerGeneralActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import tmp.sheaf.xif.paper.Mzk1B5HproductGeneralAttemptActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapLogActual
import tmp.sheaf.xif.paper.Mzk1C17ResNormDegreeGapOfResidueOneActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneSinglePointActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueOneBothSidesActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralPowActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResNormDegreeGapOfResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueOneSinglePointActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual

variable {l : PrimeGeFive}
variable {k : Type} [Field k] [NumberField k]
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem idealMapPowerStatement_pow_of_count_map
    (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k) (n : Nat)
    (hcount : (Associates.mk (underlyingPrime v).asIdeal).count
      (Associates.mk (I ^ n)).factors = n)
    (hmap : Ideal.map (algebraMap (NumberField.RingOfIntegers k)
      (LocalRing (k := k) v)) (I ^ n) =
      (completionIdealOf (k := k) v) ^ n) :
    IdealMapPowerStatement (k := k) (I ^ n) (pow_ne_zero n hI) v := by
  unfold IdealMapPowerStatement
  rw [hcount, hmap]


end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralPowActual
