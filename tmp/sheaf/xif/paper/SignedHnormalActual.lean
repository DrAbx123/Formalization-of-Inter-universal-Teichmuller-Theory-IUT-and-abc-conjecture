import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.HaarUnitFactorProof
import tmp.sheaf.xif.paper.PaperProcessionNormalization

/-! # CONDITIONAL STATUS (xi-f)

Conditional on SignedUnitFactorThetaIdentity and UnitReferenceMeasureGeOne. The actual unit-factor value object is built, but the Haar/product identity is missing; no unconditional hnormal.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Deep attempt: SignedHnormal from the actual Haar/unit-factor data

Target (from PaperThetaMagnitudeSignedActual):

  SignedHnormal D :=
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
      (C6ActualIQData.actual places tuple mu).hull =
    ENNReal.ofReal
      (c3ThetaSignedProcession (actualSignedC3 D)).average.

Actual data used:
* actual C6 hull log-volume is the canonical-hull haarLogVolume
  (PaperProcessionNormalization.c6_hull_logVolume_eq_haarLogVolume);
* the canonical-hull real log has the actual unit-factor decomposition
  (HaarUnitFactorProof.canonicalHullLog_eq_unitFactor);
* canonical-hull nonnegativity follows from the actual unit-reference measure
  identity (HaarUnitFactorProof.canonicalHullLog_nonneg_of_unitReferenceMeasureGeOne);
* the signed theta procession average is nonnegative because the source-theater
  theta packet q = 1/5 gives hlog (PaperSignedHullSignedActual).

Proved:
* SignedHnormal is equivalent to the real canonical-hull identity
  (haarLogVolume canonicalHull).toReal = signed theta average;
* the real identity follows from the exact unit-factor signed identity
  unitFactor = signed theta average, plus unit-reference measure >= 1.

Exact missing source identity: the canonical-hull unit factor equals the signed
theta procession average. No production theorem identifies the canonical Haar
unit factor with the signed theta packet average. No toy/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace SignedHnormalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uL uC uG uX uLabel

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

variable (D : LeanFormal.IUT.N8Closure.C3Actual.SourcePilotRegionDonors I)

/-- The real form of SignedHnormal: the canonical-hull Haar log-volume equals
the signed theta procession average. -/
def SignedRealHaarIdentity : Prop :=
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
    (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average

/-- Exact missing unit-factor identity: the canonical-hull unit factor equals
the signed theta procession average. -/
def SignedUnitFactorThetaIdentity : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average

/-- The actual signed C3 has a nonnegative signed theta procession average
(the source-theater q = 1/5 gives hlog). -/
theorem actualSignedC3_signedAverage_nonneg :
    0 <= (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
  c3ThetaSignedProcession_average_nonneg
    (actualSignedC3 (l := l) (V := V) (I := I) D)
    (actualSignedC3_hlog (l := l) (V := V) (I := I) D)

/-- SignedHnormal is exactly the real canonical-hull/signed-average identity. -/
theorem signedHnormal_iff_signedRealHaarIdentity :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D ↔
      SignedRealHaarIdentity (l := l) (V := V) (I := I) places tuple mu D := by
  unfold SignedHnormal SignedRealHaarIdentity
  have hhaar :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).iqInterface.hull =
        haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) := by
    simpa [C6ActualIQData.actual, arithmeticTupleIQHullLogVolumeInterface_hull] using
      c6_hull_logVolume_eq_haarLogVolume (places := places) (tuple := tuple) (mu := mu)
  rw [hhaar]
  constructor
  · intro h
    have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
      rw [haarLogVolume_of_lt_top
        (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2]
      exact ENNReal.ofReal_lt_top
    have hnonneg :
        0 <= (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
      actualSignedC3_signedAverage_nonneg (l := l) (V := V) (I := I) D
    calc
      (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
          (ENNReal.ofReal
            (c3ThetaSignedProcession
              (actualSignedC3 (l := l) (V := V) (I := I) D)).average).toReal := by
        rw [h]
      _ = (c3ThetaSignedProcession
            (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
        ENNReal.toReal_ofReal hnonneg
  · intro h
    have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
      rw [haarLogVolume_of_lt_top
        (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2]
      exact ENNReal.ofReal_lt_top
    have hnonneg :
        0 <= (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
      actualSignedC3_signedAverage_nonneg (l := l) (V := V) (I := I) D
    rw [← ENNReal.ofReal_toReal (ne_of_lt hfin), h]

/-- The real identity from the exact unit-factor signed identity and the actual
unit-reference measure identity. -/
theorem signedRealHaarIdentity_of_unitFactor
    (hUnit :
      UnitReferenceMeasureGeOne places tuple mu)
    (hfactor :
      SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I) places tuple mu D) :
    SignedRealHaarIdentity (l := l) (V := V) (I := I) places tuple mu D := by
  have hnonneg :
      0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal :=
    canonicalHullLog_nonneg_of_unitReferenceMeasureGeOne
      places tuple mu hUnit
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  unfold SignedRealHaarIdentity
  rw [haarLogVolume_of_lt_top hmeasure,
    ENNReal.toReal_ofReal hnonneg,
    canonicalHullLog_eq_unitFactor]
  exact hfactor

/-- Conditional actual SignedHnormal from the exact unit-factor identity and
the positive unit-reference measure. -/
theorem signedHnormal_of_unitFactor
    (hUnit :
      UnitReferenceMeasureGeOne places tuple mu)
    (hfactor :
      SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I) places tuple mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  (signedHnormal_iff_signedRealHaarIdentity
    (l := l) (V := V) (I := I) places tuple mu D).mpr
    (signedRealHaarIdentity_of_unitFactor
      (l := l) (V := V) (I := I) places tuple mu D hUnit hfactor)

/-- Exact missing object: the unit-reference measure identity and the signed
unit-factor theta identity. No inhabitant is asserted. -/
structure MissingSignedHnormalObject : Prop where
  unitReferenceMeasureGeOne : UnitReferenceMeasureGeOne places tuple mu
  unitFactorSignedTheta :
    SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I) places tuple mu D

/-- The exact missing signed Hnormal object supplies SignedHnormal. -/
theorem signedHnormal_of_missingSignedHnormalObject
    (M : MissingSignedHnormalObject (l := l) (V := V) (I := I)
      places tuple mu D) :
    SignedHnormal (l := l) (V := V) (I := I) places tuple mu D :=
  signedHnormal_of_unitFactor (l := l) (V := V) (I := I)
    places tuple mu D M.unitReferenceMeasureGeOne M.unitFactorSignedTheta

end SignedHnormalActual
end XiFPaper
end LeanFormal.IUT
end
