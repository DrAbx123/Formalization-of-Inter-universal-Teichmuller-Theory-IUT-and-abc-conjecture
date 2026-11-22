import tmp.sheaf.xif.paper.SignedHnormalActual
import tmp.sheaf.xif.paper.UnitFactorThetaActual
import tmp.sheaf.xif.paper.HaarSignedAverageProof

/-! # CONDITIONAL STATUS (xi-f)

Conditional equivalence to SignedProductHaarThetaIdentity. The actual product/Fubini spec is missing; no unconditional signed unit-factor identity.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Deep attempt: SignedUnitFactorThetaIdentity (write-only)

Target: arithmeticTupleHullUnitLogVolume places tuple +
Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
(c3ThetaSignedProcession C3).average.

Actual ingredients: C6 unit-factor identity; signed theta average formula;
product/field-decomposition specification of arithmeticTupleHullUnitLogVolume.

Reduction proved: target iff the actual product/Fubini specification with
value signedAverage - log(mu unitReference).  Exact missing identity is that
product Haar/Fubini identity; no arbitrary equality/toy is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedUnitFactorThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.HaarSignedAverageProof
open LeanFormal.IUT.XiFPaper.UnitFactorThetaActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui

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
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

def SignedUnitFactorThetaIdentity : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    (c3ThetaSignedProcession C3).average

theorem signedAverage_eq_neg_theta_div_card :
    (c3ThetaSignedProcession C3).average =
      -(C3.thetaPacket.logVolume / (c3ThetaCard (l := l) : Real)) :=
  signedAverage_eq_neg_theta_div_card (l := l) (V := V) (I := I) C3

def SignedProductHaarThetaIdentity : Prop :=
  ArithmeticTupleHullUnitLogVolumeSpec places tuple
    ((c3ThetaSignedProcession C3).average -
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

theorem signedUnitFactorThetaIdentity_iff_product :
    SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3 ↔
      SignedProductHaarThetaIdentity (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 := by
  constructor
  · intro h
    unfold SignedUnitFactorThetaIdentity at h
    unfold SignedProductHaarThetaIdentity
    have hval : arithmeticTupleHullUnitLogVolume places tuple =
        (c3ThetaSignedProcession C3).average -
          Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
      linarith
    simpa [hval] using arithmeticTupleHullUnitLogVolume_spec places tuple
  · intro h
    unfold SignedProductHaarThetaIdentity at h
    unfold SignedUnitFactorThetaIdentity
    have huniq := existsUnique_arithmeticTupleHullUnitLogVolume places tuple
    have hval : arithmeticTupleHullUnitLogVolume places tuple =
        (c3ThetaSignedProcession C3).average -
          Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
      huniq.unique (arithmeticTupleHullUnitLogVolume_spec places tuple) h
    linarith

def MissingSignedProductHaarThetaIdentity : Prop :=
  SignedProductHaarThetaIdentity (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3

theorem signedUnitFactorThetaIdentity_of_missingProduct
    (h : MissingSignedProductHaarThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3) :
    SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3 :=
  (signedUnitFactorThetaIdentity_iff_product (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3).mpr h

theorem missingProduct_of_signedUnitFactorThetaIdentity
    (h : SignedUnitFactorThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3) :
    MissingSignedProductHaarThetaIdentity (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3 :=
  (signedUnitFactorThetaIdentity_iff_product (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3).mp h

theorem signedAverage_nonneg
    (hlog : ThetaPacketLogVolumeNonpos (C3 := C3)) :
    0 <= (c3ThetaSignedProcession C3).average :=
  signedAverage_nonneg (l := l) (V := V) (I := I) C3 hlog

end LeanFormal.IUT.XiFPaper.SignedUnitFactorThetaActual

end
