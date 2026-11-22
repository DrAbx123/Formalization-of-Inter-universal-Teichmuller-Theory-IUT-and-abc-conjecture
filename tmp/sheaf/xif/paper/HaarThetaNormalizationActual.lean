import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullCertificateActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-! # CONDITIONAL STATUS (xi-f)

Conditional on UnitFactorThetaIdentity and CanonicalHullLogNonneg. The Haar/theta normalization identity is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual Haar/theta normalization: construction attempt and exact missing object

The paper comparison is
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal
    = thetaLogVolume l / card(sourceFiniteLabel l).

This file constructs the comparison conditionally from the actual C6
canonical-hull normalization decomposition plus one exact missing source
identity. It does not fabricate the missing identity.

Actual decomposition used (from FinitePlaceIQHullInterface):
  Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal
    = arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal.

Exact missing object (computed analytically, not arbitrary):
  unitFactorThetaIdentity :
    arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
    = thetaLogVolume l / card(sourceFiniteLabel l);
  canonicalHullLog_nonneg :
    0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal.

The nonnegativity is required because haarLogVolume is ENNReal.ofReal of the
real log; a negative real log would be truncated to zero and the comparison
would fail independently of the theta identity.

No Fubini/product/cardinality theorem in the tree equates the canonical-hull
unit factor with the theta packet average. No arbitrary equality, toy data,
forbidden declaration, or unfilled proof is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.SignedHullNormalizationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open MeasureTheory
open scoped BigOperators

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota -> Type w}
variable (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable {l : PrimeGeFive}

/-- The actual Haar/theta normalization comparison. -/
def HaarThetaNormalizationIdentity (l : PrimeGeFive) : Prop :=
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- Exact missing unit-factor theta identity. -/
def UnitFactorThetaIdentity (l : PrimeGeFive) : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- Exact missing nonnegativity of the canonical-hull real log. -/
def CanonicalHullLogNonneg : Prop :=
  0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal

/-- The exact missing object: unit-factor theta identity plus real-log
nonnegativity. -/
structure ExactMissingHaarThetaObject (l : PrimeGeFive) : Prop where
  unitFactorTheta : UnitFactorThetaIdentity (l := l) places tuple mu
  canonicalHullLog_nonneg : CanonicalHullLogNonneg places tuple mu

/-- Actual canonical-hull normalization decomposition, from the C6 interface. -/
theorem canonicalHullLog_eq_unitFactor :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) mu

/-- Conditional construction of the actual Haar/theta identity from the exact
missing object. -/
theorem haarThetaNormalizationIdentity_of_missingObject
    (H : ExactMissingHaarThetaObject (l := l) places tuple mu) :
    HaarThetaNormalizationIdentity (l := l) places tuple mu := by
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  unfold HaarThetaNormalizationIdentity
  rw [haarLogVolume_of_lt_top hmeasure,
    ENNReal.toReal_ofReal H.canonicalHullLog_nonneg,
    canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu]
  exact H.unitFactorTheta

/-- The paper procession average in theta-packet form. -/
theorem procession_average_eq_theta_div_card :
    (SignedHullNormalizationActual.procession l).average =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rw [SignedHullNormalizationActual.procession_average_eq_packet_div_card,
    SignedHullNormalizationActual.hullPacket_logVolume_eq_theta]

/-- Conditional actual C6 ENNReal normalization equality from the exact
missing object. -/
theorem c6_hnormal_of_missingObject
    (H : ExactMissingHaarThetaObject (l := l) places tuple mu) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).hull =
      ENNReal.ofReal (SignedHullNormalizationActual.procession l).average := by
  have hreal := haarThetaNormalizationIdentity_of_missingObject
    places tuple mu H
  have hc6 :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) := by
    simp [C6ActualIQData.actual,
      arithmeticTupleIQHullLogVolumeInterface_logVolume,
      arithmeticTupleIQHullLogVolumeInterface_hull]
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
    rw [haarLogVolume_of_lt_top hmeasure]
    exact ENNReal.ofReal_lt_top
  rw [hc6, ← ENNReal.ofReal_toReal (ne_of_lt hfin), hreal,
    ← procession_average_eq_theta_div_card]

end LeanFormal.IUT.XiFPaper

end
