/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PrimeConductorWeightOneActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorLogSumActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorResNormActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorUnconditionalActual
import Mathlib.Tactic

/-! # P3 L7 assembly: SSIneqExplicit from actual content data

CONDITIONAL assembly; combines WeightOne + LogSum + ResNorm + task-118.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3L7AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorUnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorWeightOneActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem ssIneqExplicit_of_actual_data
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lR arch : ℝ) (hl : 11 ≤ lR)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    [Nonempty (Bad (nativePlaceSelection T))]
    (hres : PrimeConductorResidueNormData T C)
    (hfinite : ∀ b : Bad (nativePlaceSelection T),
      Module.Finite
        ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
          T.arithmetic.Fmod)
        ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : ∀ b : Bad (nativePlaceSelection T),
      localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (htame : ∀ b : Bad (nativePlaceSelection T),
      relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1
      ∧ relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (harch : 0 ≤ arch) :
    SSIneqExplicit (sL lR) ((C.e : ℝ) * Real.log (C.p : ℝ)) lR
      (((lR + 5) / 4) * (nativeDExact T arch)) :=
  primeConductor_ssIneqExplicit_of_actual_residueNorm T hMO C lR arch hl hlogp hres
    (fun b => nativeBadLocalWeight_eq_one_of_tame_data T b (hfinite b) (hagree b)
      (htame b).1 (htame b).2) harch

def assemblyRows : List (String × String × String) :=
  [ ("ssIneqExplicit_of_actual_data", "SSIneqExplicit from actual content data", "PROVED (conditional)"),
    ("inputs", "Mestre-Oesterle external param + RESNORM + FINITE + AGREE + UNRAM/RESIDUE + arch>=0", "conditional") ]

theorem assemblyRows_length : assemblyRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3L7AssemblyActual

end
