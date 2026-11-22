/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3NormFormulaProofActual
import tmp.sheaf.xif.paper.Mzk1P3BadCharPrimeEquivActual
import tmp.sheaf.xif.paper.Mzk1P3BadCharDegActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorBadCharActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorResNormActual
import tmp.sheaf.xif.paper.Mzk1P3L7AssemblyActual
import Mathlib.Tactic

/-! # P3 BADCHAR pipeline: under-ideal + residue degree one => RESNORM => SSIneqExplicit

CONDITIONAL assembly; composes NORMFORMULA (green), PRIME equivalence, DEG, RESNORM and L7.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPipelineActual

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
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NormFormulaProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPrimeEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1P3L7AssemblyActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem badCharData_of_under_and_deg
    (C : PrimeConductorCurve)
    (hunder : ∀ b : Bad (nativePlaceSelection T),
      (b.1).maximalIdeal.asIdeal.under ℤ = Ideal.span {(C.p : ℤ)})
    (hinert : ∀ b : Bad (nativePlaceSelection T), residueInertiaDegree (b.1) = 1) :
    BadCharData T C := by
  intro b
  have hchar : residueCharacteristic (b.1) = C.p :=
    (under_eq_span_iff_residueCharacteristic_eq (b.1) C).mp (hunder b)
  have hnorm := residueNormBase_eq_residueCharacteristic_pow (K := T.arithmetic.Fmod) (b.1)
  rw [hnorm, hchar, hinert b, pow_one]

theorem primeConductorResidueNormData_of_under_and_deg
    (C : PrimeConductorCurve)
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hunder : ∀ b : Bad (nativePlaceSelection T),
      (b.1).maximalIdeal.asIdeal.under ℤ = Ideal.span {(C.p : ℤ)})
    (hinert : ∀ b : Bad (nativePlaceSelection T), residueInertiaDegree (b.1) = 1) :
    PrimeConductorResidueNormData T C :=
  primeConductorResidueNormData_of_data T C hdeg
    (fun b => badCharData_of_under_and_deg T C hunder hinert b)

theorem ssIneqExplicit_of_under_and_deg
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lR arch : ℝ) (hl : 11 ≤ lR)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    [Nonempty (Bad (nativePlaceSelection T))]
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
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hunder : ∀ b : Bad (nativePlaceSelection T),
      (b.1).maximalIdeal.asIdeal.under ℤ = Ideal.span {(C.p : ℤ)})
    (hinert : ∀ b : Bad (nativePlaceSelection T), residueInertiaDegree (b.1) = 1)
    (harch : 0 ≤ arch) :
    SSIneqExplicit (sL lR) ((C.e : ℝ) * Real.log (C.p : ℝ)) lR
      (((lR + 5) / 4) * (nativeDExact T arch)) :=
  ssIneqExplicit_of_actual_data T hMO C lR arch hl hlogp
    (primeConductorResidueNormData_of_under_and_deg T C hdeg hunder hinert)
    hfinite hagree htame harch

def badCharPipelineRows : List (String × String × String) :=
  [ ("badCharData_of_under_and_deg", "under span C.p + f=1 => residueNormBase b.1 = C.p", "PROVED (conditional)"),
    ("primeConductorResidueNormData_of_under_and_deg", "RESNORM from under/f data + RESDEG", "PROVED (conditional)"),
    ("ssIneqExplicit_of_under_and_deg", "SSIneqExplicit end-to-end", "PROVED (conditional)") ]

theorem badCharPipelineRows_length : badCharPipelineRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3BadCharPipelineActual

end
