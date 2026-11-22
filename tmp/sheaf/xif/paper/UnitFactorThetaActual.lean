import tmp.sheaf.xif.paper.HaarThetaAverageProof
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-! # CONDITIONAL STATUS (xi-f)

Conditional reduction to the product/Fubini identity; no production Haar product theorem supplies it.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Deep attempt: actual Haar unit-factor / theta identity

Task-606 attempts

  UnitFactorThetaIdentity:
    arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
    = thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real).

Actual ingredients:

* the C6 unit-factor identity
    Real.log (mu canonicalHull).toReal
      = arithmeticTupleHullUnitLogVolume places tuple
        + Real.log (mu canonicalUnitReference).toReal
  (FinitePlaceIQHullInterface);
* the product/field-decomposition specification of
  arithmeticTupleHullUnitLogVolume (FinitePlaceArithmeticTupleHullVolume);
* the theta packet/procession average
  thetaLogVolume l / card (SignedHullNormalizationActual);
* Haar normalization and compactness/finiteness of the canonical regions.

No theorem currently identifies the canonical-hull unit factor
(arithmeticTupleHullUnitLogVolume + unit-reference Haar log) with the theta
packet average.  The exact missing measure product identity is stated below.
This file proves the actual unit-factor formula, the product-measure form, and
conditional reductions.  No unconditional identity is asserted.  No toy,
True/PUnit/axiom/sorry.  WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace UnitFactorThetaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.SignedHullNormalizationActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.HaarThetaAverageProof
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

/-! ## 1. Actual C6 unit-factor identity -/

/-- The actual C6 canonical-hull Haar log is the unit factor plus the
unit-reference term. -/
theorem haarCanonicalHullLog_eq_unitFactor_actual :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  haarCanonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu

/-- The actual product/field-decomposition specification of the unit factor. -/
theorem unitFactor_product_spec :
    ArithmeticTupleHullUnitLogVolumeSpec places tuple
      (arithmeticTupleHullUnitLogVolume places tuple) :=
  arithmeticTupleHullUnitLogVolume_spec places tuple

/-! ## 2. Target identity and its product-measure form -/

/-- The exact target identity. -/
def UnitFactorThetaIdentity : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- The exact product-measure form: for any actual field-product decomposition,
the normalized hull volume plus the unit-reference Haar log equals the theta
packet average.  This is equivalent to the unit-factor identity through the
actual uniqueness/specification of arithmeticTupleHullUnitLogVolume, but the
identity is kept explicit here. -/
def ProductHaarThetaIdentity : Prop :=
  ArithmeticTupleHullUnitLogVolumeSpec places tuple
    (thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) -
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

/-- The target identity is exactly the product-measure identity when the unit
factor is read through its actual specification. -/
theorem unitFactorThetaIdentity_iff_product :
    UnitFactorThetaIdentity (l := l) places tuple mu <->
      ProductHaarThetaIdentity (l := l) places tuple mu := by
  constructor
  · intro h
    unfold UnitFactorThetaIdentity at h
    unfold ProductHaarThetaIdentity
    have hval : arithmeticTupleHullUnitLogVolume places tuple =
        thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) -
          Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
      linarith
    simpa [hval] using arithmeticTupleHullUnitLogVolume_spec places tuple
  · intro h
    unfold ProductHaarThetaIdentity at h
    unfold UnitFactorThetaIdentity
    have huniq := existsUnique_arithmeticTupleHullUnitLogVolume places tuple
    have hval : arithmeticTupleHullUnitLogVolume places tuple =
        thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) -
          Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
      huniq.unique (arithmeticTupleHullUnitLogVolume_spec places tuple) h
    linarith

/-! ## 3. Actual real-log nonnegativity/readback condition -/

/-- Nonnegativity of the canonical-hull real Haar log, needed for the
ENNReal.toReal readback. -/
def CanonicalHullRealLogNonneg : Prop :=
  0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal

/-- Exact missing package: the unit-factor/theta identity plus nonnegativity of
the real Haar log. -/
def ExactMissingUnitFactorTheta : Prop :=
  UnitFactorThetaIdentity (l := l) places tuple mu ∧
    CanonicalHullRealLogNonneg places tuple mu

/-! ## 4. Conditional reduction to the theta average -/

/-- Conditional proof: the missing unit-factor identity plus real-log
nonnegativity gives the Haar/theta average comparison. -/
theorem haarLogVolume_eq_theta_average_of_missingIdentity
    (h : ExactMissingUnitFactorTheta (l := l) places tuple mu) :
    (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rcases h with ⟨hidentity, hnonneg⟩
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  rw [haarLogVolume_of_lt_top hmeasure,
    ENNReal.toReal_ofReal hnonneg,
    haarCanonicalHullLog_eq_unitFactor_actual (places := places) (tuple := tuple) mu]
  exact hidentity

/-! ## 5. Exact missing identity -/

/-- The exact missing measure product identity, as a named proposition. -/
def MissingUnitFactorThetaIdentity : Prop :=
  UnitFactorThetaIdentity (l := l) places tuple mu

/-- The product-measure form of the exact missing identity. -/
def MissingProductHaarThetaIdentity : Prop :=
  ProductHaarThetaIdentity (l := l) places tuple mu

/-- The missing unit-factor identity is exactly the missing product identity. -/
theorem missingUnitFactorTheta_iff_product :
    MissingUnitFactorThetaIdentity (l := l) places tuple mu <->
      MissingProductHaarThetaIdentity (l := l) places tuple mu :=
  unitFactorThetaIdentity_iff_product (l := l) places tuple mu

end UnitFactorThetaActual
end XiFPaper
end LeanFormal.IUT
