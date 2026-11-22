/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import tmp.sheaf.xif.paper.GenEll01bHeightLayerActual
import Mathlib.Tactic

/-! # GAP-NORM-ARCH-C-K consumer hook: replace heightWeight by archCK -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open LeanFormal.IUT.IUTIV.Estimates
namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.GenEll01bHeightLayerActual
variable {F : Type} [Field F] [NumberField F]

/-- Consumer entry: GenEll height-layer `hArc ≥ 0` with the explicit `archCK`
factor instead of the opaque `heightWeight` hypothesis. -/
theorem hArc_nonneg_via_archCK (x : F) : 0 ≤ hArc F x := by
  refine s3135_hArc_nonneg (F := F) x ?_
  rw [← archCK_eq_heightWeight]
  exact le_of_lt archCK_pos
theorem hNon_nonneg_via_archCK (x : F) : 0 ≤ hNon F x := by
  refine s3135_hNon_nonneg (F := F) x ?_
  rw [← archCK_eq_heightWeight]
  exact le_of_lt archCK_pos
theorem hBox_nonneg_via_archCK (x : F) : 0 ≤ hBox F x := by
  refine s3135_hBox_nonneg (F := F) x ?_
  rw [← archCK_eq_heightWeight]
  exact le_of_lt archCK_pos

/-- Replacement theorem: the consumer summand uses the same `archCK`. -/
theorem hArc_eq_archCK_mul_sum_consumer (x : F) :
    hArc F x = archCK F *
      ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x := by
  rw [hArc_eq_archCK_mul_sum]

def normArchConsumerRows : List (String × String) :=
  [ ("hArc_nonneg_via_archCK", "GenEll01b consumer, no heightWeight hypothesis"),
    ("hNon_nonneg_via_archCK", "consumer"),
    ("hBox_nonneg_via_archCK", "consumer"),
    ("hArc_eq_archCK_mul_sum_consumer", "same-factor replacement"),
    ("finite Haar ratio", "independent B3, GAP") ]
theorem normArchConsumerRows_length : normArchConsumerRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NormArchConsumerActual
