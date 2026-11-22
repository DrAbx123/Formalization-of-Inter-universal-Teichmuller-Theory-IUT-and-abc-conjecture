/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3FiniteFLTActual
import tmp.sheaf.xif.paper.Mzk1P3AgreeIntegrationActual
import Mathlib.Tactic

/-! # P3-E final conditional assembly

The end-to-end `SSIneqExplicit` with:
* AGREE discharged by FLT (AgreeFLT),
* FINITE discharged by the FLT completion finiteness instance (FiniteFLT),
* RESNORM data + tame + under/inertia + arch kept as explicit inputs,
* Mestre-Oesterle kept as an external Prop parameter.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 300000

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FinalAssemblyActual

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
open LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPipelineActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeFLTActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FiniteFLTActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeIntegrationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem ssIneqExplicit_final
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
  ssIneqExplicit_of_under_and_deg_agreed (T := T) hMO C lR arch hl hlogp
    (fun b => nativeBadToKPlace_moduleFinite T b)
    htame hdeg hunder hinert harch

def finalRows : List (String × String × String) :=
  [ ("AGREE", "FLT BaseChange :685/:721", "DISCHARGED (conditional on T arithmetic)"),
    ("FINITE", "FLT completion Module.Finite instance", "DISCHARGED (conditional on T arithmetic)"),
    ("RESNORM data", "hdeg + hunder + hinert", "input"),
    ("tame", "htame (relative e=f=1)", "input (GAP-PC-TAME)"),
    ("Mestre-Oesterle", "hMO", "EXTERNAL PARAM Prop"),
    ("ssIneqExplicit_final", "end-to-end", "PROVED (conditional)") ]

theorem finalRows_length : finalRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3FinalAssemblyActual

end