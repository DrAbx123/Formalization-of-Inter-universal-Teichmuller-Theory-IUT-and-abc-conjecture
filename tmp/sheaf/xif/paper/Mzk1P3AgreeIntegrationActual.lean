/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3AgreeFLTActual
import tmp.sheaf.xif.paper.Mzk1P3BadCharPipelineActual
import Mathlib.Tactic

/-! # P3 AGREE integration: FLT AGREE replaces the hAgree input of the pipeline -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 200000

namespace LeanFormal.IUT.XiFPaper.Mzk1P3AgreeIntegrationActual

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
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorBadCharActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1P3L7AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPipelineActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeFLTActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem ssIneqExplicit_of_under_and_deg_agreed
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lR arch : ℝ) (hl : 11 ≤ lR)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    [Nonempty (Bad (nativePlaceSelection T))]
    [FiniteDimensional T.arithmetic.Fmod T.arithmetic.K]
    [Algebra.IsSeparable T.arithmetic.Fmod T.arithmetic.K]
    [Algebra (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.K]
    [IsScalarTower (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.Fmod T.arithmetic.K]
    [IsScalarTower (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K) T.arithmetic.K]
    [IsScalarTower ℤ (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [Module.Finite (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [Module.IsTorsionFree (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [IsIntegralClosure (NumberField.RingOfIntegers T.arithmetic.K)
      (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.K]
    (hfinite : ∀ b : Bad (nativePlaceSelection T),
      Module.Finite
        ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
          T.arithmetic.Fmod)
        ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (htame : ∀ b : Bad (nativePlaceSelection T),
      relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1
      ∧ relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hunder : ∀ b : Bad (nativePlaceSelection T),
      (b.1).maximalIdeal.asIdeal.under ℤ = Ideal.span {(C.p : ℤ)})
    (hinert : ∀ b : Bad (nativePlaceSelection T), residueInertiaDegree (b.1) = 1)
    (harch : 0 ≤ arch) :
    SSIneqExplicit (sL lR) ((C.e : ℝ) * Real.log (C.p : ℝ)) lR
      (((lR + 5) / 4) * (nativeDExact T arch)) :=
  ssIneqExplicit_of_under_and_deg T hMO C lR arch hl hlogp
    hfinite
    (fun b => localDataAgreesWithPlaceData_of_implies
      (k := T.arithmetic.Fmod) (K := T.arithmetic.K) (nativeBadToKPlace T b))
    htame hdeg hunder hinert harch

def agreeIntegrationRows : List (String × String × String) :=
  [ ("AGREE input", "localDataAgreesWithPlaceData", "PROVED by FLT AgreeFLT (no longer an input)"),
    ("FINITE input", "Module.Finite completed valuation rings", "still an input (GAP-PC-FINITE)"),
    ("ssIneqExplicit_of_under_and_deg_agreed", "end-to-end SSIneqExplicit without hAgree", "PROVED (conditional)") ]

theorem agreeIntegrationRows_length : agreeIntegrationRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3AgreeIntegrationActual

end