import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib

noncomputable section
open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3130QCLeHCActual

universe u

/-- Batch A data on one fixed C: the paper-level ambient hull interface plus the
signed q readout `Q_C` (an actual real value; the paper q-mark source is NOT
constructed here). The hull readout is `H_C = (logVolume hull).toReal`. -/
structure S3130QCLeHCData (X : Type u) where
  /-- The fixed ambient hull/log-volume interface of the same input `C`. -/
  W : IQHullLogVolumeInterface X
  /-- Signed q readout `Q_C`. This is a real number parameter; its paper
  q-mark provenance is an explicit missing source link, not proved here. -/
  qReadout : ℝ

/-- The hull readout `H_C`. -/
noncomputable def S3130QCLeHCData.HC (D : S3130QCLeHCData X) : ℝ :=
  (D.W.logVolume D.W.hull).toReal

/-- The signed q readout `Q_C`. -/
def S3130QCLeHCData.QC (D : S3130QCLeHCData X) : ℝ := D.qReadout

/-- **Actual part 1 (finiteness).** The ambient hull log-volume is finite by the
already-proved `hull_logVolume_lt_top`, so `H_C` is a genuine real number. -/
theorem S3130QCLeHCData.HC_finite (D : S3130QCLeHCData X) :
    D.W.logVolume D.W.hull < ⊤ := D.W.hull_logVolume_lt_top

/-- **Actual part 2 (monotonicity).** Any region contained in the ambient hull has
log-volume at most the hull log-volume. -/
theorem S3130QCLeHCData.logVolume_le_HC {D : S3130QCLeHCData X} {S : Set X}
    (hS : S ⊆ D.W.hull) : D.W.logVolume S ≤ D.W.logVolume D.W.hull := D.W.logVolume_mono hS

/-- **Actual part 3 (ambient hull bound).** `H_C` is bounded by any explicit ambient
bound for the hull log-volume. -/
theorem S3130QCLeHCData.HC_le_ambient (D : S3130QCLeHCData X) {amb : ℝ}
    (hamb : (D.W.logVolume D.W.hull).toReal ≤ amb) : D.HC ≤ amb := hamb

/-- **The exact remaining gap of Batch A.** `Q_C ≤ H_C` is NOT proved: it is
recorded here as the single explicit comparison gap, with no ABC gap invoked. -/
def S3130QCLeHCGap (D : S3130QCLeHCData X) : Prop := D.QC ≤ D.HC

/-- Conditional assembly: the gap yields the Batch A comparison `Q_C ≤ H_C`. -/
theorem S3130QCLeHC_of_gap (D : S3130QCLeHCData X) (h : S3130QCLeHCGap D) :
    D.QC ≤ D.HC := h

#check S3130QCLeHCData
#check S3130QCLeHCData.HC
#check S3130QCLeHCData.HC_finite
#check S3130QCLeHCData.logVolume_le_HC
#check S3130QCLeHCData.HC_le_ambient
#check S3130QCLeHCGap
#check S3130QCLeHC_of_gap

end LeanFormal.IUT.XiFPaper.S3130QCLeHCActual
end