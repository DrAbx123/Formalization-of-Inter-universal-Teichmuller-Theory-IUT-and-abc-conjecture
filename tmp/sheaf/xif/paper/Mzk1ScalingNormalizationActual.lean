/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionAverageActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1PaperNormThetaActual
import Mathlib.Tactic

/-! # A997: scaling normalization identity (v2 central gap) -/

/- Target identity: for `nC = (l-1)/2`, `sum_{j=1}^{nC} j^2 = nC * sFactor nC`
(`l=5`: 1+4=5=2*2.5).  Green source: `sFactor` is defined in
`Mzk1ShellArithmeticIdentitiesActual:16` as `(sum_{j<n} (j+1)^2)/n`; the
`avgJSquare_eq_l` (Mzk1ProcessionAverageActual) gives the closed form `l(l+1)/12`.
Remaining theorem of the v2 line: `(sF - 1) * A <= qPositiveSum`.
No sorry/axiom.  This file is written for watchdog compilation only (no manual compile). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual
open Finset
open scoped BigOperators

/-- `nC(l) = (l-1)/2` (the capsule count `l*`). -/
def nC (l : Nat) : Nat := (l - 1) / 2

/-- The j-square sum `sum_{j=1..nC} j^2`. -/
def jsqSum (l : Nat) : Real := ∑ j ∈ Finset.range (nC l), ((j + 1 : Real) ^ 2)

/-- `nC(l) > 0` for `l >= 5`. -/
theorem nC_pos {l : Nat} (hl : 5 ≤ l) : 0 < nC l := by
  unfold nC
  exact Nat.div_pos (by omega) (by norm_num)

/-- **Scaling normalization**: the j-square sum equals `nC * sFactor nC`. -/
theorem sum_jsq_eq_nC_mul_sFactor (l : Nat) (hl : 5 ≤ l) :
    jsqSum l = (nC l : Real) * sFactor (nC l) := by
  unfold jsqSum sFactor
  have hn : (nC l : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (nC_pos hl))
  field_simp [hn] <;> ring

/-- The negative q-scaling piece at a place: `-(1/(2l)) * sum_j j^2 * v_p(q) * log p`. -/
def qScalingNeg (vp logp : Real) (l : Nat) : Real :=
  - (1 / (2 * (l : Real))) * jsqSum l * vp * logp

/-- **q-scaling reduction**: the UNNORMALIZED negative sum equals `-(nC * sF) * A_p`
with `A_p = v_p(q) * log p / (2l)`; `nC = l*` counts the capsules. -/
theorem qScalingNeg_eq_neg_nC_mul_sF_mul_A (vp logp : Real) (l : Nat) (hl : 5 ≤ l) :
    qScalingNeg vp logp l =
      - ((nC l : Real) * sFactor (nC l)) * (vp * logp / (2 * (l : Real))) := by
  unfold qScalingNeg
  rw [sum_jsq_eq_nC_mul_sFactor l hl]
  have hl0 : (2 * (l : Real)) ≠ 0 := by
    have hlpos : (l : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by omega : 0 < l))
    exact mul_ne_zero (by norm_num) hlpos
  field_simp [hl0] <;> ring

/-- **Normalized q-scaling reduction**: dividing by `nC` (the procession average)
gives exactly `-sF * A_p`; this is the per-capsule coefficient used in `M`. -/
theorem qScalingNeg_div_nC_eq_neg_sF_mul_A (vp logp : Real) (l : Nat) (hl : 5 ≤ l) :
    qScalingNeg vp logp l / (nC l : Real) =
      - (sFactor (nC l)) * (vp * logp / (2 * (l : Real))) := by
  have hn : (nC l : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (nC_pos hl))
  rw [qScalingNeg_eq_neg_nC_mul_sF_mul_A vp logp l hl]
  have hl0 : (2 * (l : Real)) ≠ 0 := by
    have hlpos : (l : Real) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by omega : 0 < l))
    exact mul_ne_zero (by norm_num) hlpos
  field_simp [hn, hl0] <;> ring

/-- The remaining v2 inequality: the nonnegative part dominates `(sF-1)*A`. -/
def RemainingInequality (qPositiveSum A sF : Real) : Prop :=
  (sF - 1) * A <= qPositiveSum

/-- `M = qPositiveSum - (sF-1)*A >= 0` from the remaining inequality. -/
theorem M_nonneg_of_remaining {qPositiveSum A sF : Real}
    (h : RemainingInequality qPositiveSum A sF) : 0 <= qPositiveSum - (sF - 1) * A := by
  unfold RemainingInequality at h
  linarith

def qPositiveSources : List (String × String) :=
  [ ("tame shell", "componentVol_leastHull_tensorLogShell_eq_tame (VcI.lean:435) >= 0") ,
    ("archDefect", "archDefect_nonneg (Gap.lean:463) >= 0") ,
    ("shellDefect", "shellDefect_nonneg (Gap.lean:442) >= 0") ,
    ("ind2Term", "ind2Term_nonneg (Gap.lean:756) >= 0 (entry into M not yet proved)") ,
    ("orderVol", "orderVol_nonpos (VcI.102) <= 0 (negative side)") ,
    ("packetWeight", "packetWeight_pos (LogVolume.lean:153) > 0") ,
    ("lgp integral", "logVol_lgp_integral = -sF*absLogQ (IdentifiedCopies:444, GREEN; negative m-linear term)") ]

theorem qPositiveSources_length : qPositiveSources.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ScalingNormalizationActual