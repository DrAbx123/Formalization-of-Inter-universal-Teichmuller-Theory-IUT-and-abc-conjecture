import tmp.sheaf.xif.paper.SignedHnormalActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.n8.closure.C3Actual

/-! # PaperSignedHull hnormal from the signed unit-factor normalization

The only source equality separating the actual C6 Haar hull log-volume from the
signed theta procession average is the signed unit-factor identity

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu canonicalUnitReference).toReal
  = (c3ThetaSignedProcession actualSignedC3).average.

This file proves that this identity ALONE implies SignedHnormal, without the
separate UnitReferenceMeasureGeOne hypothesis. The proof uses the actual C6
unit-factor formula and the actual nonnegativity of the signed theta average:
the signed unit-factor identity rewrites the canonical-hull log to a
nonnegative quantity, so the ENNReal readback is exact.

It then constructs the actual source-theater PaperSignedHull from that
identity and records the precise remaining equality as the normalization
obstruction. No hnormal/True is faked; the conclusion is a proved conditional
construction from the exact source equality.

No sorry, axiom, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperSignedHullNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedHnormalActual

open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

variable (D : SourcePilotRegionDonors I)

/-- The exact source equality left for hnormal: the signed unit-factor
normalization identity. -/
def PaperSignedHullNormalizationObstruction : Prop :=
  SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu D

#check @PaperSignedHullNormalizationObstruction

/-- The signed unit-factor identity alone implies the real C6 Haar/signed-average
identity; no separate unit-reference measure lower bound is needed. -/
theorem signedRealHaarIdentity_of_unitFactor_noUnit
    (hfactor :
      SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu D) :
    SignedRealHaarIdentity (l := l) (V := V) (I := I)
      places tuple mu D := by
  have hnonneg :
      0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal := by
    rw [canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu,
      hfactor]
    exact actualSignedC3_signedAverage_nonneg (l := l) (V := V) (I := I) D
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  unfold SignedRealHaarIdentity
  rw [haarLogVolume_of_lt_top hmeasure,
    ENNReal.toReal_ofReal hnonneg,
    canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu]
  exact hfactor

/-- The signed unit-factor identity alone implies SignedHnormal. -/
theorem signedHnormal_of_unitFactor_noUnit
    (hfactor :
      SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  (signedHnormal_iff_signedRealHaarIdentity
    (l := l) (V := V) (I := I) places tuple mu D).mpr
    (signedRealHaarIdentity_of_unitFactor_noUnit
      (l := l) (V := V) (I := I) places tuple mu D hfactor)

/-- Actual source-theater PaperSignedHull from the exact signed unit-factor
identity. -/
noncomputable def paperSignedHullOfUnitFactor
    (hfactor : PaperSignedHullNormalizationObstruction
      (l := l) (V := V) (I := I) places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  sourceTheaterSignedPaperSignedHull (l := l) (V := V) (I := I)
    places tuple mu D
    (actualSignedC3_hlog (l := l) (V := V) (I := I) D)
    (signedHnormal_of_unitFactor_noUnit
      (l := l) (V := V) (I := I) places tuple mu D hfactor)

/-- The constructed PaperSignedHull carries the actual signed source-theater
procession. -/
theorem paperSignedHullOfUnitFactor_procession
    (hfactor : PaperSignedHullNormalizationObstruction
      (l := l) (V := V) (I := I) places tuple mu D) :
    (paperSignedHullOfUnitFactor (l := l) (V := V) (I := I)
      places tuple mu D hfactor).procession =
      c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D) :=
  rfl

/-- The normalization obstruction is exactly the equality needed for the
PaperSignedHull hnormal field. -/
theorem paperSignedHull_normalization_obstruction_iff :
    PaperSignedHullNormalizationObstruction (l := l) (V := V) (I := I)
        places tuple mu D ↔
      SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu D := Iff.rfl

end LeanFormal.IUT.XiFPaper.PaperSignedHullNormalizationActual

end