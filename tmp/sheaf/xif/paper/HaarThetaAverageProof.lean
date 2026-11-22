import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullCertificateActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# Haar hull log-volume versus theta packet average: deep reduction

Target:
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal
    = thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real).

The actual C6 canonical-hull Haar log-volume is not definitionally a theta
packet quantity. This file reduces the target to the exact missing analytic
factorization, using the existing actual normalization theorem

  arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal :

  Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal
    = arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal.

The exact missing factorization is therefore

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  = thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real),

together with nonnegativity of the canonical-hull real log (so that the
ENNReal.toReal of haarLogVolume does not truncate to zero).

No C6/Fubini/product theorem in the tree identifies the canonical-hull Haar
volume or its unit factor with the theta packet log-volume. No arbitrary
equality, toy data, axiom, or unfilled proof is introduced.
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

/-- Exact unit-factor form of the actual canonical-hull Haar log-volume,
proved by the existing interface normalization theorem. -/
theorem haarCanonicalHullLog_eq_unitFactor :
    Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) mu

/-- The exact missing analytic factorization: the actual unit factor of the
canonical hull equals the theta packet average. -/
def UnitFactorThetaComparison (l : PrimeGeFive) : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- The real canonical-hull log is nonnegative, so haarLogVolume.toReal is the
real logarithm rather than the ENNReal.ofReal truncation. -/
def CanonicalHullRealLogNonneg : Prop :=
  0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal

/-- Exact missing factorization bundle. -/
def ExactMissingHaarThetaFactorization (l : PrimeGeFive) : Prop :=
  UnitFactorThetaComparison (l := l) places tuple mu ∧
    CanonicalHullRealLogNonneg places tuple mu

/-- Conditional deep reduction: the exact missing unit-factor factorization and
real-log nonnegativity give the paper Haar/theta average comparison. -/
theorem haarLogVolume_eq_theta_average_of_missingFactorization
    (h : ExactMissingHaarThetaFactorization (l := l) places tuple mu) :
    (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rcases h with ⟨hfactor, hnonneg⟩
  have hfin : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  rw [haarLogVolume_of_lt_top hfin,
    ENNReal.toReal_ofReal hnonneg,
    haarCanonicalHullLog_eq_unitFactor (places := places) (tuple := tuple) mu]
  exact hfactor

/-- The paper procession average is the theta packet average. -/
theorem procession_average_eq_theta_div_card :
    (SignedHullNormalizationActual.procession l).average =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rw [SignedHullNormalizationActual.procession_average_eq_packet_div_card,
    SignedHullNormalizationActual.hullPacket_logVolume_eq_theta]

/-- Conditional final form: exact missing factorization plus nonnegativity gives
the actual C6 ENNReal normalization equality. -/
theorem c6_hnormal_of_missingFactorization
    (h : ExactMissingHaarThetaFactorization (l := l) places tuple mu) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).hull =
      ENNReal.ofReal (SignedHullNormalizationActual.procession l).average := by
  have hreal :=
    haarLogVolume_eq_theta_average_of_missingFactorization
      (l := l) places tuple mu h
  have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
    have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
      (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
    rw [haarLogVolume_of_lt_top hmeasure]
    exact ENNReal.ofReal_lt_top
  have hc6 :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) := by
    simp [C6ActualIQData.actual,
      arithmeticTupleIQHullLogVolumeInterface_logVolume,
      arithmeticTupleIQHullLogVolumeInterface_hull]
  rw [hc6, ← ENNReal.ofReal_toReal (ne_of_lt hfin), hreal,
    ← procession_average_eq_theta_div_card (l := l)]

end LeanFormal.IUT.XiFPaper

end
