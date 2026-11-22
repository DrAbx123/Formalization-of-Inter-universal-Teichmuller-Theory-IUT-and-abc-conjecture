import tmp.sheaf.xif.paper.SignedHullNormalizationActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# Bridge: signed-hull containment and paper normalization comparison

This file proves the containability field of the signed-hull packet from the
actual theta scales and isolates the exact missing normalization comparison
between the actual C6 IQ hull log-volume and the paper procession average.

Proved here (actual data):
1. procession_hcontains: under the exact source field ScalingSource l
   (theta_scales_ge_one), every actual procession value is at most the actual
   packet log-volume. This is the hcontains field of SignedHullFromSource.

Not derived (exact missing comparison):
2. paperProcessionNormalizationComparison: the actual C6 IQ hull log-volume
   (haarLogVolume of arithmeticTupleCanonicalHull) equals the paper procession
   average packetLogVolume / card. This is not a packet-log identity: the C6
   interface log-volume is a Haar measure on the canonical hull, while the
   procession average is a finite sum of theta log-scales. No existing theorem
   identifies them. hnormal_of_comparison turns this exact comparison into the
   ENNReal equality required by PaperSignedHull.

No arbitrary equality, degenerate placeholder, axiom, or unfilled proof is
introduced.
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

/-- The actual C6 IQ carrier of the arithmetic tensor tuple block. -/
abbrev C6Carrier (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> V i) : Type (max u v) :=
  C6IQCarrier places tuple

/-- The actual C6 IQ hull interface. -/
noncomputable def c6IQInterface :
    IQHullLogVolumeInterface (C6Carrier places tuple) :=
  (C6ActualIQData.actual places tuple mu).iqInterface

/-- Actual signed-hull containment: under the exact theta scaling source, every
procession log-scale is at most the actual packet log-volume. -/
theorem procession_hcontains (S : ScalingSource l) :
    forall j : sourceFiniteLabel l,
      (SignedHullNormalizationActual.procession l).value j <=
        packetLogVolume (SignedHullNormalizationActual.hullPacket l) := by
  intro j
  have hnonneg : forall i : sourceFiniteLabel l,
      0 <= (SignedHullNormalizationActual.procession l).value i := by
    intro i
    rw [SignedHullNormalizationActual.procession_value]
    exact Real.log_nonneg (S.theta_scales_ge_one i)
  have hle :
      (SignedHullNormalizationActual.procession l).value j <=
        Finset.sum Finset.univ
          (fun i : sourceFiniteLabel l =>
            (SignedHullNormalizationActual.procession l).value i) :=
    Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j)
  have hsum :
      Finset.sum Finset.univ
          (fun i : sourceFiniteLabel l =>
            (SignedHullNormalizationActual.procession l).value i) =
        packetLogVolume (SignedHullNormalizationActual.hullPacket l) := by
    unfold SignedHullNormalizationActual.procession packetLogVolume
    rfl
  rwa [hsum] at hle

/-- Exact missing paper comparison: the real Haar log-volume of the actual
canonical C6 hull equals the actual theta-packet procession average. -/
def paperProcessionNormalizationComparison (l : PrimeGeFive) : Prop :=
  ((C6ActualIQData.actual places tuple mu).iqInterface.logVolume
      (C6ActualIQData.actual places tuple mu).iqInterface.hull).toReal =
    (SignedHullNormalizationActual.procession l).average

/-- Conditional ENNReal form: the exact missing real comparison implies the
PaperSignedHull normalization equality. -/
theorem hnormal_of_paperComparison
    (hcomp : paperProcessionNormalizationComparison (l := l) places tuple mu) :
    (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).iqInterface.hull =
      ENNReal.ofReal (SignedHullNormalizationActual.procession l).average := by
  have hfin :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
        (C6ActualIQData.actual places tuple mu).iqInterface.hull < ⊤ :=
    ((C6ActualIQData.actual places tuple mu).iqInterface).hull_logVolume_lt_top
  rw [← hcomp]
  exact (ENNReal.ofReal_toReal (ne_of_lt hfin)).symm


end LeanFormal.IUT.XiFPaper

end
