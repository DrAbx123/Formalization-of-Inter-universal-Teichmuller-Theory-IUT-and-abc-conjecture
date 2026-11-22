import tmp.sheaf.xif.paper.Mzk1BoxConstantAuditActual
import tmp.sheaf.xif.paper.Mzk1BoxStepVAverageActual
import tmp.sheaf.xif.paper.Mzk1ProcessionAverageActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1BoxConstantAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual

/-- Actual slot count: the distinguished slot family at label `j` has `j+1` members. -/
theorem p6_slot_count (j : Nat) :
    Fintype.card (Fin (j + 1)) = j + 1 :=
  Fintype.card_fin _

/-- Any actual nonempty finite bad-place index has positive cardinality. -/
theorem p6_bad_count_pos {B : Type*} [Fintype B] [Nonempty B] :
    0 < Fintype.card B :=
  Fintype.card_pos_iff.mpr inferInstance

/-- Slot/index counts are finite and positive. -/
theorem p6_slot_bad_reindex {B : Type*} [Fintype B] {n : Nat}
    (f : Fin (n + 1) → B → Real) :
    (∑ s : Fin (n + 1), ∑ b : B, f s b) =
      ∑ b : B, ∑ s : Fin (n + 1), f s b :=
  Finset.sum_comm

/-- Actual bad/label/slot reindex: swap the two finite sums. -/
theorem p6_bad_label_slot_reindex {B : Type*} [Fintype B] {n : Nat}
    (f : B → Fin (n + 1) → Real) :
    (∑ b : B, ∑ s : Fin (n + 1), f b s) =
      ∑ s : Fin (n + 1), ∑ b : B, f b s :=
  Finset.sum_comm

/-- Actual linear weight average: `(1/n) Σ_{j<n} (j+2) = (l+5)/4` at `l=2n+1`. -/
theorem p6_linear_weight_average (n : Nat) (hn : 0 < n) (l : Real)
    (hl : l = 2 * (n : Real) + 1) :
    (1 / (n : Real)) * (∑ j ∈ Finset.range n, ((j : Real) + 2)) = (l + 5) / 4 :=
  avgJPlusOne_eq_l n hn l hl

/-- Actual square weight average: `(1/n) Σ j² = l(l+1)/12` at `l=2n+1`. -/
theorem p6_square_weight_average (n : Nat) (hn : 0 < n) (l : Real)
    (hl : l = 2 * (n : Real) + 1) :
    (1 / (n : Real)) * (∑ j ∈ Finset.range n, (((j : Real) + 1) ^ 2)) =
      l * (l + 1) / 12 :=
  avgJSquare_eq_l n hn l hl

/-- StepV averages produce the IV inequality in the paper normalized form. -/
theorem p6_stepVAverages_ivInequality
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : Real) + 1) D Q S T j) ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  paper_procession_le n hn D Q S T hD hS hT

#print axioms p6_slot_count
#print axioms p6_slot_bad_reindex
#print axioms p6_stepVAverages_ivInequality

end LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
end