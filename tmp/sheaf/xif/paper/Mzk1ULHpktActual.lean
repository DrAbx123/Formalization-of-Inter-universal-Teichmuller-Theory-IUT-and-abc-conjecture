/- U-L Hpkt: raw local weighted C1 packet sum and the §5.4 hpaper reduction
from the Step (viii) intermediate expression to `κ(A - c_l Q) - M`. -/
import tmp.sheaf.xif.paper.Mzk1P6WeightedPacketHullActual
import tmp.sheaf.xif.paper.Mzk1UCC3Actual
import tmp.sheaf.xif.paper.Mzk1P6HConstActual
import LeanFormal.IUT.IUTIV.Estimates.Section2
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1P6WeightedPacketHullActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
/-- Hpkt = sum_a w_a * V_a: the raw local weighted C1 packet value. -/
noncomputable def Hpkt {A : Type*} [Fintype A]
    (w : A → Real) (V : A → Real) : Real :=
  ∑ a : A, w a * V a
/-- Hpkt is bounded by the weighted sum of the base StepV bounds. -/
theorem Hpkt_le_weighted_bound {A : Type*} [Fintype A]
    (w : A → Real) (V B : A → Real)
    (hw : ∀ a, 0 ≤ w a) (h : ∀ a, V a ≤ B a) :
    Hpkt w V ≤ ∑ a : A, w a * B a := by
  unfold Hpkt
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (hw a))
/-- The actual StepV weighted C1 value is the base packet hull upper. -/
theorem Hpkt_stepV_upper
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ULPacketHullValue n D Q S T ≤ ULPacketHullBound n D Q S T :=
  uL_weightedPacketHull_le n hn D Q S T hD hS hT
/-- The §5.4 arithmetic constant `A = (1 + 12 d_mod/l) S_ar + 10 E_ar`. -/
noncomputable def paperA (d_mod l S_ar E_ar : Real) : Real :=
  (1 + 12 * d_mod / l) * S_ar + 10 * E_ar
/-- route §5.4.4 actual arithmetic constant `E_ar = e*_mod · l + η_prm` with the
paper value `e*_mod = 2^12 · 3^3 · 5 · e_mod` (IUT IV Thm 1.10). -/
noncomputable def paperEar (eMod : Nat) (l eta_prm : Real) : Real :=
  (Mzk1P6HConstActual.eStarMod eMod : Real) * l + eta_prm
/-- The actual paper constant `E_ar` is nonnegative for `l ≥ 0`, `η_prm ≥ 0`. -/
theorem paperEar_nonneg {eMod : Nat} {l eta_prm : Real} (hl : 0 ≤ l) (heta : 0 ≤ eta_prm) :
    0 ≤ paperEar eMod l eta_prm := by
  unfold paperEar
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl) heta
/-- route §5.4.4 prime-count argument `x = e·l` (with `e = e*_mod`). -/
noncomputable def paperPrimeArgument (eMod : Nat) (l : Real) : Real :=
  (Mzk1P6HConstActual.eStarMod eMod : Real) * l
/-- route §5.4.4 small-prime logarithm `l*_mod log(s≤) = π(⌊x⌋₊)·log x`. -/
noncomputable def paperLstarLogs (eMod : Nat) (l : Real) : Real :=
  (Nat.primeCounting ⌊paperPrimeArgument eMod l⌋₊ : Real) * Real.log (paperPrimeArgument eMod l)
/-- The prime-count argument is nonnegative. -/
theorem paperPrimeArgument_nonneg {eMod : Nat} {l : Real} (hl : 0 ≤ l) :
    0 ≤ paperPrimeArgument eMod l :=
  mul_nonneg (Nat.cast_nonneg _) hl
/-- The prime-count argument is at least one (for `l ≥ 1`, `e_mod ≥ 1`), so its
logarithm is nonnegative. -/
theorem paperPrimeArgument_ge_one {eMod : Nat} (he : 1 ≤ eMod) {l : Real} (hl : 1 ≤ l) :
    1 ≤ paperPrimeArgument eMod l := by
  unfold paperPrimeArgument
  have he1 : (1 : Real) ≤ (Mzk1P6HConstActual.eStarMod eMod : Real) := by
    have := Mzk1P6HConstActual.eStarMod_cast_ge he
    linarith
  nlinarith
/-- `x = e·l ≤ E_ar` (since `η_prm ≥ 0`); route §5.4.4 uses this to replace
`(4/3)x` by `(4/3)E_ar` in the large-`x` branch. -/
theorem paperPrimeArgument_le_Ear {eMod : Nat} {l eta_prm : Real} (heta : 0 ≤ eta_prm) :
    paperPrimeArgument eMod l ≤ paperEar eMod l eta_prm := by
  unfold paperPrimeArgument paperEar
  linarith
/-- `η₀ ≤ E_ar` whenever the paper threshold `η_prm` dominates `η₀`
(route §5.4.4 selects `η_prm := max η₀ 2`); this is the small-`x` branch input. -/
theorem paperEar_ge_of_le {eMod : Nat} {l eta_prm eta0 : Real} (hl : 0 ≤ l)
    (heta0 : eta0 ≤ eta_prm) : eta0 ≤ paperEar eMod l eta_prm := by
  unfold paperEar
  have h1 : 0 ≤ (Mzk1P6HConstActual.eStarMod eMod : Real) * l :=
    mul_nonneg (Nat.cast_nonneg _) hl
  linarith
/-- **`hconst` producer from the paper constants (§5.4.4).**  With
`e_mod ≥ 1`, `η_prm ≥ 0`, `l ≥ 5` and `E_ar = e*_mod·l + η_prm`,
`2 log l + 56 ≤ (4/9) E_ar`.  This is `Mzk1P6HConstActual.two_log_add_56_le_four_ninths_Ear`
read through the actual `E_ar` definition. -/
theorem ul_hconst_of_paperConstants {eMod : Nat} (he : 1 ≤ eMod)
    {l eta_prm : Real} (hl : 5 ≤ l) (heta : 0 ≤ eta_prm) :
    2 * Real.log l + 56 ≤ (4 / 9) * paperEar eMod l eta_prm := by
  unfold paperEar
  exact Mzk1P6HConstActual.two_log_add_56_le_four_ninths_Ear he hl heta rfl
/-- **U-L hpaper (§5.4 steps 3-4).**  The Step (viii) intermediate expression
`κ{(1+12d_mod/l)S_ar + 2 log l + 56 - c_l Q + (20/3) l*_mod log(s≤)} - M` is at
most `κ(A - c_l Q) - M`, where `A = (1 + 12 d_mod/l) S_ar + 10 E_ar`.

This is exactly route §5.4.4: the actual prime-count bound gives
`l*_mod log(s≤) ≤ (4/3) E_ar` and `l ≥ 5` gives `2 log l + 56 ≤ (4/9) E_ar`, so
the exceptional part is `≤ (28/3) E_ar ≤ 10 E_ar`. -/
theorem ul_hpaper_of_stepVIII
    (l S_ar E_ar Q M d_mod lstar_logs H : Real)
    (hl : 0 < l) (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log l + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      H ≤ kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs) - M) :
    H ≤ kappa l * (paperA d_mod l S_ar E_ar - cL l * Q) - M := by
  have hk : 0 < kappa l := by
    unfold kappa
    linarith
  have hinner :
      (1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs ≤
        paperA d_mod l S_ar E_ar - cL l * Q := by
    unfold paperA
    nlinarith [hprime, hconst, hE]
  have hmul := mul_le_mul_of_nonneg_left hinner hk.le
  linarith
/-- **U-L hpaper, assembled form.**  If every per-packet value satisfies the C1
paper bound `V_a ≤ B_a` and the weighted Step (viii) intermediate bound holds
for `Σ w_a B_a`, then the actual weighted packet value satisfies
`Hpkt ≤ κ(A - c_l Q) - M`. -/
theorem ul_hpaper_assembled
    {A : Type*} [Fintype A]
    (w V B : A → Real)
    (hw : ∀ a, 0 ≤ w a) (hVB : ∀ a, V a ≤ B a)
    (l S_ar E_ar Q M d_mod lstar_logs : Real)
    (hl : 0 < l) (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log l + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      (∑ a : A, w a * B a) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs) - M) :
    Hpkt w V ≤ kappa l * (paperA d_mod l S_ar E_ar - cL l * Q) - M :=
  le_trans (Hpkt_le_weighted_bound w V B hw hVB)
    (ul_hpaper_of_stepVIII l S_ar E_ar Q M d_mod lstar_logs _ hl hE hprime hconst
      hstepVIII)
/-- **U-L hpaper with the paper constants.**  With `E_ar = e*_mod·l + η_prm`
(`e_mod ≥ 1`, `η_prm ≥ 0`, `l ≥ 5`), the weighted Step (viii) intermediate bound
for `Σ_a w_a B_a` implies `Hpkt ≤ κ(paperA − c_l Q) − M`. -/
theorem ul_hpaper_assembled_paperConstants
    {A : Type*} [Fintype A]
    (w V B : A → Real)
    (hw : ∀ a, 0 ≤ w a) (hVB : ∀ a, V a ≤ B a)
    {eMod : Nat} (he : 1 ≤ eMod)
    (l eta_prm S_ar Q M d_mod lstar_logs : Real)
    (hl : 5 ≤ l) (heta : 0 ≤ eta_prm)
    (hprime : lstar_logs ≤ (4 / 3) * paperEar eMod l eta_prm)
    (hstepVIII :
      (∑ a : A, w a * B a) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs) - M) :
    Hpkt w V ≤ kappa l * (paperA d_mod l S_ar (paperEar eMod l eta_prm) - cL l * Q) - M :=
  ul_hpaper_assembled w V B hw hVB l S_ar (paperEar eMod l eta_prm) Q M d_mod lstar_logs
    (by linarith) (paperEar_nonneg (by linarith) heta) hprime
    (ul_hconst_of_paperConstants he hl heta) hstepVIII
#print axioms Hpkt_le_weighted_bound
#print axioms Hpkt_stepV_upper
#print axioms ul_hpaper_of_stepVIII
#print axioms ul_hpaper_assembled
#print axioms paperEar_nonneg
#print axioms ul_hconst_of_paperConstants
#print axioms ul_hpaper_assembled_paperConstants
end LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
end
