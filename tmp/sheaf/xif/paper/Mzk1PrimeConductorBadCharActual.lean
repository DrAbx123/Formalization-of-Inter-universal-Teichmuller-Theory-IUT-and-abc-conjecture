/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorResNormActual
import Mathlib.Tactic

/-! # GAP-PC-BADCHAR: `residueNormBase (b.1) = C.p` reduced to residue data

The bad moduli place `b.1` is a finite place of `T.arithmetic.Fmod`.  Its
residue norm is the absolute norm of its maximal ideal.  We decompose the target
into three named data items:

* **GAP-PC-NORMFORMULA**: `residueNormBase place = residueCharacteristic place ^
  residueInertiaDegree place` (plausible from
  `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver` plus
  `under_eq_span_residueCharacteristic` at
  `FinitePlaceDegreeSumBound:39`; not assembled here);
* **GAP-PC-BADCHAR-PRIME**: the residue characteristic of `b.1` is the prime
  conductor `C.p`;
* **GAP-PC-BADCHAR-DEG**: the residue degree of `b.1` over its residue
  characteristic is one.

No sorry/axiom; all three are explicit content hypotheses, not new axioms.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorBadCharActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **GAP-PC-BADCHAR** as a Prop (same shape as the RESNORM input). -/
def BadCharData (C : PrimeConductorCurve) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), residueNormBase (b.1) = (C.p : ℝ)

/-- **GAP-PC-NORMFORMULA** for the bad places: residue norm
`= residueCharacteristic ^ residueInertiaDegree`. -/
def ResidueNormPowerFormula : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    residueNormBase (b.1) =
      (residueCharacteristic (b.1) : ℝ) ^ residueInertiaDegree (b.1)

/-- **GAP-PC-BADCHAR-PRIME**: residue characteristic of the bad place is `C.p`. -/
def BadCharPrimeData (C : PrimeConductorCurve) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), residueCharacteristic (b.1) = C.p

/-- **GAP-PC-BADCHAR-DEG**: residue degree of the bad place over its residue
characteristic is one. -/
def BadCharInertiaOne : Prop :=
  ∀ b : Bad (nativePlaceSelection T), residueInertiaDegree (b.1) = 1

/-- **BADCHAR from the three named data items.** -/
theorem badCharData_of_data
    (C : PrimeConductorCurve)
    (hnorm : ResidueNormPowerFormula T)
    (hprime : BadCharPrimeData T C)
    (hinert : BadCharInertiaOne T) :
    BadCharData T C := by
  intro b
  rw [hnorm b, hprime b, hinert b, pow_one]

/-- Compose BADCHAR data with the RESNORM reduction: with the additional
GAP-PC-RESDEG input, the full `PrimeConductorResidueNormData` is obtained. -/
theorem resNormData_of_badChar
    (C : PrimeConductorCurve)
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1)
    (hnorm : ResidueNormPowerFormula T)
    (hprime : BadCharPrimeData T C)
    (hinert : BadCharInertiaOne T) :
    PrimeConductorResidueNormData T C :=
  primeConductorResidueNormData_of_data T C hdeg
    (fun b => badCharData_of_data T C hnorm hprime hinert b)

/-- Status rows. -/
def badCharRows : List (String × String × String) :=
  [ ("BadCharData", "residueNormBase (b.1) = C.p", "DEF (target Prop)"),
    ("ResidueNormPowerFormula", "residue norm = residueCharacteristic ^ residueInertiaDegree", "GAP-PC-NORMFORMULA (content input)"),
    ("BadCharPrimeData", "residueCharacteristic (b.1) = C.p", "GAP-PC-BADCHAR-PRIME (content input)"),
    ("BadCharInertiaOne", "residueInertiaDegree (b.1) = 1", "GAP-PC-BADCHAR-DEG (content input)"),
    ("badCharData_of_data", "three data items => BADCHAR", "PROVED (conditional)") ]

theorem badCharRows_length : badCharRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorBadCharActual

end
