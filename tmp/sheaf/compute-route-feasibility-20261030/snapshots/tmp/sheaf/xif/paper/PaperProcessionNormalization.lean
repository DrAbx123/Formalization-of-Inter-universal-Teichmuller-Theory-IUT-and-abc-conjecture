import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-! # CONDITIONAL STATUS (xi-f)

Conditional on paperProcessionNormalizationComparison. The Haar canonical-hull / theta average identity is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Paper procession normalization: exact missing Haar comparison

The actual C6 IQ hull interface is the Haar log-volume of the actual canonical
arithmetic-tuple hull:

  (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
    (C6ActualIQData.actual places tuple mu).hull
  = haarLogVolume mu (arithmeticTupleCanonicalHull places tuple),

while the paper procession average is

  (SignedHullNormalizationActual.procession l).average
  = packetLogVolume (hullPacket l) / card
  = thetaLogVolume l / card.

The file reduces the proposed paper procession normalization comparison to the
single exact missing Haar-packet equality

  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal
    = thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real).

No existing theorem in the tree relates the canonical-hull Haar log-volume to
the theta packet log-volume or to the source theta normalization. The equality
is therefore stated as the exact missing comparison, not postulated. The
conditional theorem shows that this single real identity is sufficient;
hnormal_of_haar_theta gives the corresponding ENNReal form for
PaperSignedHull.hull_logVolume_eq_average.

No arbitrary equality, toy data, degenerate placeholder, axiom, or unfilled
proof is introduced.
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

/-- The exact paper procession normalization comparison in real form: the
actual canonical-hull Haar log-volume equals the theta packet average. -/
def paperProcessionNormalizationComparison (l : PrimeGeFive) : Prop :=
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
    thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)

/-- The actual C6 IQ hull log-volume is the canonical-hull Haar log-volume. -/
theorem c6_hull_logVolume_eq_haarLogVolume :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).hull =
      haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) := by
  simp [C6ActualIQData.actual,
    arithmeticTupleIQHullLogVolumeInterface_logVolume,
    arithmeticTupleIQHullLogVolumeInterface_hull]

/-- The actual procession average is thetaLogVolume divided by the label
cardinality. -/
theorem procession_average_eq_theta_div_card (l : PrimeGeFive) :
    (SignedHullNormalizationActual.procession l).average =
      thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real) := by
  rw [SignedHullNormalizationActual.procession_average_eq_packet_div_card,
    SignedHullNormalizationActual.hullPacket_logVolume_eq_theta]

/-- Exact missing comparison in the interface shape used by
SignedHullNormalizationBridge: the real canonical-hull Haar log-volume equals
the actual procession average. -/
def paperProcessionNormalizationComparisonInterface (l : PrimeGeFive) : Prop :=
  (haarLogVolume mu (arithmeticTupleCanonicalHull places tuple)).toReal =
    (SignedHullNormalizationActual.procession l).average

/-- The two forms of the missing comparison are equivalent. -/
theorem paperProcessionNormalizationComparison_iff_interface :
    paperProcessionNormalizationComparison (l := l) places tuple mu <->
      paperProcessionNormalizationComparisonInterface (l := l) places tuple mu := by
  unfold paperProcessionNormalizationComparison
    paperProcessionNormalizationComparisonInterface
  rw [procession_average_eq_theta_div_card (l := l)]

/-- Conditional closure: the exact Haar-packet comparison gives the actual C6
IQ hull log-volume as the ENNReal of the paper procession average. -/
theorem hnormal_of_paperComparison
    (h : paperProcessionNormalizationComparison (l := l) places tuple mu) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).hull =
      ENNReal.ofReal (SignedHullNormalizationActual.procession l).average := by
  have hreal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (thetaLogVolume l / (Fintype.card (sourceFiniteLabel l) : Real)) := by
    rw [c6_hull_logVolume_eq_haarLogVolume]
    have hfin : haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := by
      rw [haarLogVolume_of_lt_top
        (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2]
      exact ENNReal.ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (ne_of_lt hfin)]
    exact congrArg ENNReal.ofReal h
  rw [hreal, procession_average_eq_theta_div_card (l := l)]

end LeanFormal.IUT.XiFPaper

end
