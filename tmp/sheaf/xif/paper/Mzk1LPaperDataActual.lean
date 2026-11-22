/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormComparisonConditionalActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import Mathlib.Tactic

/-!
# L-side paper data: signed readout, raw calibration, exact source gaps

thetaNormReadL is a signed log-volume, not the magnitude, and it is not assumed
equal to the global product readout.  The raw calibration keeps the reference
log mass: thetaReadActual = d * V_R + logMuR, d > 0; unitMass = 1 is NOT assumed.
The conditional consumer needs hlock (signed), hbound, hlog.  This file records
those exact inputs and the obstruction.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

namespace LeanFormal.IUT.XiFPaper.Mzk1LPaperDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormComparisonConditionalActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Raw Haar calibration for the L theta hull: log mu(H) = d V_R(H) + log mu(R). -/
structure LHaarCalibrationSource
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) where
  d : Nat
  d_pos : 0 < d
  logMuR : Real
  V_R : Real
  raw_eq : thetaReadActual I place = (d : Real) * V_R + logMuR

/-- Exact calibrated form of the signed L readout (reference mass retained). -/
theorem thetaNormReadL_eq_calibration_sub_logUnitMass
    (C : LHaarCalibrationSource I place) :
    thetaNormReadL (I := I) (place := place) =
      (C.d : Real) * C.V_R + C.logMuR -
        Real.log (actualUnitMassL (I := I) (place := place)) := by
  unfold thetaNormReadL
  rw [C.raw_eq]

/-- The three exact inputs of LPaperInstance_of_bounds.  The Fintype instance is
an explicit parameter so the global product readout is well-typed without
instance-synthesis ambiguity. -/
structure LPaperSourceData
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
    (T : SourceNativeInitialThetaData.{0} l)
    (inst : Fintype (Bad (nativePlaceSelection T))) where
  hlock : thetaNormReadL (I := I) (place := place) =
    @Mzk1P0LNormReadoutProductActual.thetaNormReadProduct l T inst
  hbound : qReadActual I place ≤
    @Mzk1P0LNormReadoutProductActual.thetaNormReadProduct l T inst
  hlog : 0 ≤ Real.log (actualUnitMassL (I := I) (place := place))

/-- Conditional construction of LPaperInstance from the exact source data. -/
theorem LPaperInstance_of_sourceData (D : LPaperSourceData I place T inferInstance) :
    LPaperInstance I place :=
  LPaperInstance_of_bounds (I := I) (place := place) (T := T)
    D.hlock D.hbound D.hlog

/-- Exact source obstruction for the L paper data: signed object lock, numerical
bound, and unit-mass sign.  All three are explicit and unproved. -/
def LPaperDataSourceGap : Prop :=
  thetaNormReadL (I := I) (place := place) =
      @Mzk1P0LNormReadoutProductActual.thetaNormReadProduct l T inferInstance ∧
    qReadActual I place ≤
      @Mzk1P0LNormReadoutProductActual.thetaNormReadProduct l T inferInstance ∧
      0 ≤ Real.log (actualUnitMassL (I := I) (place := place))

/-- The signed L readout (hlock uses this, not the magnitude). -/
def thetaSignedReadL : Real := thetaNormReadL (I := I) (place := place)

/-- The magnitude of the signed L readout; it is not substituted for thetaSignedReadL. -/
def thetaMagnitudeReadL : Real := |thetaSignedReadL (I := I) (place := place)|

theorem thetaMagnitudeReadL_eq_abs :
    thetaMagnitudeReadL (I := I) (place := place) =
      |thetaSignedReadL (I := I) (place := place)| := rfl

def lPaperDataRows : List (String × String × String) :=
  [ ("LHaarCalibrationSource", "log mu(H)=d V_R+log mu(R), d>0; reference mass kept", "DEFINED"),
    ("thetaNormReadL_eq_calibration_sub_logUnitMass", "signed readout = d V_R + logMuR - log unitMass", "PROVED"),
    ("LPaperSourceData", "hlock(signed)+hbound+hlog", "DEFINED"),
    ("LPaperInstance_of_sourceData", "source data => LPaperInstance", "PROVED (conditional)"),
    ("LPaperDataSourceGap", "signed lock + bound + unitMass sign", "EXPLICIT SOURCE GAP"),
    ("thetaSignedReadL / thetaMagnitudeReadL", "signed vs |signed|; not conflated", "DEFINED") ]

theorem lPaperDataRows_length : lPaperDataRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1LPaperDataActual
end
