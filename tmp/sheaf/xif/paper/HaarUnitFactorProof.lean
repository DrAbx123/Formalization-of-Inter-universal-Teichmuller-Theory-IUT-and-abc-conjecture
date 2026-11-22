import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-! # CONDITIONAL STATUS (xi-f)

Conditional on UnitReferenceMeasureGeOne and UnitFactorThetaIdentity. No unconditional Haar theta average identity.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Canonical-hull nonnegativity and unit-factor theta identity

This file proves the canonical-hull real-log nonnegativity from one exact
measure identity on the actual canonical unit reference:

  UnitReferenceMeasureGeOne :
    1 <= (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal.

The proof uses the actual relative-log identity
  Real.log (mu canonicalHull).toReal - Real.log (mu unitReference).toReal
    = arithmeticTupleHullUnitLogVolume places tuple
and arithmeticTupleHullUnitLogVolume_nonneg.

The separate theta identity

  UnitFactorThetaIdentity :
    arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu unitReference).toReal
    = thetaLogVolume l / card(sourceFiniteLabel l)

is not derived: no existing theorem relates the canonical unit factor to the
theta packet average. It is stated as the exact missing measure/Fubini identity.
The conditional theorems show that the two exact fields suffice for the full
Haar/theta normalization comparison.

No arbitrary equality, toy data, axiom, or unfilled proof is introduced.
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

/-- Exact missing measure identity: the actual canonical unit reference has
real measure at least one. -/
def UnitReferenceMeasureGeOne : Prop :=
  1 <= (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal

/-- Exact missing unit-factor theta identity. -/
def UnitFactorThetaIdentity (l : PrimeGeFive) : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- Canonical-hull real-log nonnegativity. -/
def CanonicalHullLogNonneg : Prop :=
  0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal

/-- Exact missing measure/Fubini object for the two remaining fields. -/
structure ExactMissingHaarUnitFactorObject (l : PrimeGeFive) : Prop where
  unitReferenceMeasureGeOne : UnitReferenceMeasureGeOne places tuple mu
  unitFactorThetaIdentity : UnitFactorThetaIdentity (l := l) places tuple mu

/-- Proven implication: the exact unit-reference measure identity implies
canonical-hull real-log nonnegativity. -/
theorem canonicalHullLog_nonneg_of_unitReferenceMeasureGeOne
    (h : UnitReferenceMeasureGeOne places tuple mu) :
    CanonicalHullLogNonneg places tuple mu := by
  have hrel :=
    arithmeticTupleCanonicalRegions_relativeLogVolume places tuple mu
  have hlogUnit : 0 <= Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
    Real.log_nonneg h
  have hvol : 0 <= arithmeticTupleHullUnitLogVolume places tuple :=
    arithmeticTupleHullUnitLogVolume_nonneg places tuple
  unfold CanonicalHullLogNonneg
  linarith

/-- Actual C6 canonical-hull log equals the unit factor. -/
theorem canonicalHullLog_eq_unitFactor :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) mu

/-- The paper procession average in theta-packet form. -/
theorem procession_average_eq_theta_div_card :
    (SignedHullNormalizationActual.procession l).average =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rw [SignedHullNormalizationActual.procession_average_eq_packet_div_card,
    SignedHullNormalizationActual.hullPacket_logVolume_eq_theta]

/-- Conditional Haar/theta normalization identity from the exact missing object. -/
theorem haarLogVolume_eq_theta_average_of_exactMissingObject
    (H : ExactMissingHaarUnitFactorObject (l := l) places tuple mu) :
    (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  have hnonneg := canonicalHullLog_nonneg_of_unitReferenceMeasureGeOne
    places tuple mu H.unitReferenceMeasureGeOne
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  rw [haarLogVolume_of_lt_top hmeasure, ENNReal.toReal_ofReal hnonneg,
    canonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu]
  exact H.unitFactorThetaIdentity

end LeanFormal.IUT.XiFPaper

end
