/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1InitialThetaCStageV2Actual

/-! # Initial Theta C-stage: consumer laws for stage sequences -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaCStageV2Actual

theorem CStageData.stage_eq_iterate_stage_zero {Carrier : Type*}
    (d : CStageData Carrier) (n : Nat) :
    d.stage n = (d.next^[n]) (d.stage 0) := by
  have h := d.stage_add 0 n
  simpa using h

theorem CStageData.stage_add_iterate {Carrier : Type*}
    (d : CStageData Carrier) (n k l : Nat) :
    d.stage (n + (k + l)) = (d.next^[l]) ((d.next^[k]) (d.stage n)) := by
  induction l with
  | zero => simp
  | succ l ih =>
      have h : n + (k + (l + 1)) = (n + (k + l)) + 1 := by omega
      rw [h, d.step, ih, Function.iterate_succ_apply']
      rfl

theorem CStageData.stage_two {Carrier : Type*}
    (d : CStageData Carrier) (n : Nat) :
    d.stage (n + 2) = d.next (d.next (d.stage n)) := by
  rw [show n + 2 = (n + 1) + 1 by ring, d.step (n + 1), d.step n]

theorem CStageData.stage_monotone_iterate {Carrier : Type*}
    (d : CStageData Carrier) {n m : Nat} (h : n ≤ m) :
    ∃ k : Nat, d.stage m = (d.next^[k]) (d.stage n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨k, d.stage_add n k⟩

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaCStageV2Actual
