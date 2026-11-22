import tmp.sheaf.xif.paper.Mzk1Stage4LanaIutIVEstimateActual
import tmp.sheaf.xif.paper.Mzk1Stage4GapTransformationsActual

/-! # Mzk1Stage4LanaGapContentActual (stage4 lane; LANA -> gap content)

A652 module (real mathematical content): derived height bounds from the LANA local
estimate.  From the LANA Gap-1/Gap-2 shapes we derive the honest `(1+ε)^2`-loss height
bound (no shortcuts: the loss is explicit and the hypotheses remain the LANA fields).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaGapContentActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaIutIVEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

universe u

/-- Step 1: the LANA local estimate bounds the height by `(1+ε)·region-volume`. -/
theorem lana_height_le_regionVolume {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (a b c : Nat) :
    E.height a b c ≤ (1 + ε) * E.vol (E.region a b c) :=
  E.height_le_region ε hε a b c

/-- Step 2: multiplying the region-volume bound by `(1+ε) ≥ 0` gives the height bound
with the honest `(1+ε)^2` loss. -/
theorem lana_height_bound_squared {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (D : Real)
    (hD : ∀ a b c : Nat, E.vol (E.region a b c) ≤
      (1 + ε) * E.weight a b c + E.thetaBound + D) (a b c : Nat) :
    E.height a b c ≤
      (1 + ε) * ((1 + ε) * E.weight a b c + E.thetaBound + D) :=
  le_trans (lana_height_le_regionVolume E ε hε a b c)
    (mul_le_mul_of_nonneg_left (hD a b c) (by linarith))

/-- Expanded form of the squared-loss bound. -/
theorem lana_height_bound_squared_expanded {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (D : Real)
    (hD : ∀ a b c : Nat, E.vol (E.region a b c) ≤
      (1 + ε) * E.weight a b c + E.thetaBound + D) (a b c : Nat) :
    E.height a b c ≤ (1 + ε) ^ 2 * E.weight a b c + (1 + ε) * (E.thetaBound + D) :=
  by
  have h := lana_height_bound_squared E ε hε D hD a b c
  nlinarith

/-- The per-triple Gap-1 structure transported to the scaled region volume. -/
theorem lana_gap1_scaled {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (c : Real) (hc : 0 < c) (a b c' : Nat) :
    Gap1 (c * E.height a b c') (c * ((1 + ε) * E.vol (E.region a b c'))) := by
  refine ⟨?_⟩
  exact mul_le_mul_of_nonneg_left (E.height_le_region ε hε a b c') (le_of_lt hc)

#check lana_height_le_regionVolume
#check lana_height_bound_squared
#check lana_height_bound_squared_expanded
#check lana_gap1_scaled

end LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaGapContentActual
end
