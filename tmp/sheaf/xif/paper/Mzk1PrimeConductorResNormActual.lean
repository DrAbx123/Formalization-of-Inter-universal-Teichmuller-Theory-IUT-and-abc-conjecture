/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorLogSumActual
import Mathlib.Tactic

/-! # GAP-PC-RESNORM: actual residue norm of the bad section place

Green inputs:
* `residueNormBase_eq_lower_pow` (ArithmeticQPilotBaseChange:126):
  `residueNormBase w = residueNormBase (comap w) ^ localResidueDegree w`;
* `nativeBaseSectionPlace_comap` (BaseQFamilyActual:71):
  `comap (nativeBaseSectionPlace T b) = b.1`.

Remaining named inputs:
* **GAP-PC-RESDEG** — the actual local residue degree at the bad section place
  is one (tame case);
* **GAP-PC-BADCHAR** — the bad moduli place `b.1` has residue norm equal to the
  prime conductor `C.p` (the prime-conductor identification).

Both are content-level hypotheses; no sorry/axiom, no new mathematical assumption
beyond the named objects.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Residue norm of the bad section place in terms of the contracted place. -/
theorem residueNormBase_nativeBaseSectionPlace_eq_pow
    (b : Bad (nativePlaceSelection T)) :
    residueNormBase (nativeBaseSectionPlace T b) =
      residueNormBase (b.1) ^
        localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) := by
  rw [residueNormBase_eq_lower_pow (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b),
    nativeBaseSectionPlace_comap]

/-- **GAP-PC-RESNORM (per place)**: residue degree one plus the bad-character
identification gives `residueNormBase = C.p`. -/
theorem residueNormBase_nativeBaseSectionPlace_eq_Cp
    (C : PrimeConductorCurve) (b : Bad (nativePlaceSelection T))
    (hdeg : localResidueDegree (k := T.arithmetic.Fmod)
      (nativeBaseSectionPlace T b) = 1)
    (hlower : residueNormBase (b.1) = (C.p : ℝ)) :
    residueNormBase (nativeBaseSectionPlace T b) = (C.p : ℝ) := by
  rw [residueNormBase_nativeBaseSectionPlace_eq_pow T b, hdeg, pow_one, hlower]

/-- **GAP-PC-RESNORM (all bad places)**: the candidate Prop from the LOGSUM file. -/
theorem primeConductorResidueNormData_of_data
    (C : PrimeConductorCurve)
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hlower : ∀ b : Bad (nativePlaceSelection T), residueNormBase (b.1) = (C.p : ℝ)) :
    PrimeConductorResidueNormData T C :=
  fun b => residueNormBase_nativeBaseSectionPlace_eq_Cp T C b (hdeg b) (hlower b)

/-- LOGSUM consumer: under GAP-PC-RESDEG + GAP-PC-BADCHAR + nonempty bad set and
`log C.p ≥ 0`, the abstract log-sum inequality holds for the actual base q family. -/
theorem log_le_sum_baseQLogMagnitude_of_data
    (C : PrimeConductorCurve) [Fintype (Bad (nativePlaceSelection T))]
    [Nonempty (Bad (nativePlaceSelection T))]
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hlower : ∀ b : Bad (nativePlaceSelection T), residueNormBase (b.1) = (C.p : ℝ))
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    Real.log (C.p : ℝ) ≤ ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b :=
  log_le_sum_baseQLogMagnitude T C
    (primeConductorResidueNormData_of_data T C hdeg hlower) hlogp

/-- Status rows. -/
def resNormRows : List (String × String × String) :=
  [ ("residueNormBase_eq_lower_pow", "residue norm = lower norm ^ local residue degree", "PROVED (existing)"),
    ("nativeBaseSectionPlace_comap", "comap of the bad section place = b.1", "PROVED (existing)"),
    ("residueNormBase_nativeBaseSectionPlace_eq_pow", "residue norm in terms of b.1", "PROVED"),
    ("residueNormBase_nativeBaseSectionPlace_eq_Cp", "unit residue degree + bad char => = C.p", "PROVED (conditional)"),
    ("primeConductorResidueNormData_of_data", "GAP-PC-RESNORM from named data", "PROVED (conditional)"),
    ("log_le_sum_baseQLogMagnitude_of_data", "LOGSUM with RESNORM discharged", "PROVED (conditional)"),
    ("GAP-PC-RESDEG", "localResidueDegree (nativeBadSectionPlace) = 1", "GAP (tame case, input)"),
    ("GAP-PC-BADCHAR", "residueNormBase (b.1) = C.p", "GAP (prime-conductor identification, input)") ]

theorem resNormRows_length : resNormRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual

end
