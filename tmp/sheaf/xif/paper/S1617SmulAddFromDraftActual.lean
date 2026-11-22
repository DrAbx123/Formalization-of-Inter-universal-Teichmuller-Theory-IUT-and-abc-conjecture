import tmp.sheaf.xif.paper.S1612ZSMulPointFinalActual
import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual
import tmp.sheaf.xif.paper.S1600RelatorNormalFormActual
import tmp.sheaf.xif.paper.S1601ZSMulPointFormulaActual

/-!
# S1617: chord-addition identities from the TauCeti ZSMul draft

This file ports the two remaining point-level chord identities

* smulX_add
* smulY_add_sub_negY

from the TauCeti draft tmp/sheaf/xif/paper/_PRZSMul.lean (lines 280--311) to the
current production layer, and packages them as the S1612 targets
S1612SmulXAdd and S1612SmulYAddSubNegY.

The draft names are mapped as follows.

* smulX_add_aux             -> the local private s1617_smulX_add_aux
* smulY_add_sub_negY_aux    -> the local private s1617_smulY_add_sub_negY_aux
* smulX_sub_smulX           -> WeierstrassCurve.Universal.smulX_sub_smulX (S1600)
* smulX_sub_sub_smulX_add   -> WeierstrassCurve.Universal.smulX_sub_sub_smulX_add (S1601)
* smulY_sub_negY            -> s1605_smulY_sub_negY (S1605)
* net_ψᵤ                    -> s1617_rel_ψᵤ, from s1599IsEllipticNet_ψᵤ
* EllSequence.net_add_sub_iff -> s1617_rel_nsm, the expansion of
  ER(n + m, n, n - m, m) in terms of IsEllipticNet.rel

The draft used the old EllSequence.net API.  In the current Mathlib that
relator is IsEllipticNet.rel (definitionally the same polynomial), so
s1617_rel_nsm supplies the required expansion lemma directly and the two
chord identities are replayed without any new axiom or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1617SmulAddFromDraftActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual

/-! ### The elliptic-net relator ER(n + m, n, n - m, m) -/

/-- The ψᵤ sequence is an elliptic net, in the current IsEllipticNet.rel API. -/
theorem s1617_rel_ψᵤ (p q r s : ℤ) : IsEllipticNet.rel ψᵤ p q r s = 0 :=
  s1599IsEllipticNet_ψᵤ p q r s

/-- The expansion of the relator ER(n + m, n, n - m, m) for ψᵤ.

This is the replacement for the draft's EllSequence.net_add_sub_iff specialized
at (m, n) = (n, m). -/
theorem s1617_rel_nsm (n m : ℤ) :
    IsEllipticNet.rel ψᵤ (n + m) n (n - m) m = 0 ↔
      ψᵤ (2 * (n + m)) * ψᵤ (n - m) * ψᵤ n * ψᵤ m =
        (ψᵤ (2 * n + m) * ψᵤ (2 * m) * ψᵤ n -
          ψᵤ (n + 2 * m) * ψᵤ (2 * n) * ψᵤ m) * ψᵤ (n + m) := by
  rw [IsEllipticNet.rel]
  conv_rhs => rw [← sub_eq_zero]
  ring_nf

/-! ### The chord X-coordinate -/

/-- Field identity isolated from the draft's smulX_add_aux. -/
private lemma s1617_smulX_add_aux {F : Type*} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

/-- The chord X identity, ported from the draft's smulX_add. -/
theorem s1617_smulX_add (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n + m) = smulX (n - m) -
      (smulY n - Affine.negY pointedCurve.toAffine (smulX n) (smulY n)) *
      (smulY m - Affine.negY pointedCurve.toAffine (smulX m) (smulY m)) /
        (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add m n add_ne sub_ne]
  simp_rw [s1605_smulY_sub_negY m hm, s1605_smulY_sub_negY n hn, smulX_sub_smulX m n hm hn]
  apply s1617_smulX_add_aux <;> apply polyToField_ψ_ne_zero <;> assumption

/-- The exact S1612 chord-X target. -/
theorem s1617_SmulXAdd : S1612SmulXAdd := s1617_smulX_add

/-! ### The chord Y-coordinate -/

/-- Field identity isolated from the draft's smulY_add_sub_negY_aux. -/
private lemma s1617_smulY_add_sub_negY_aux {F : Type*} [Field F]
    {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

/-- The chord Y identity, ported from the draft's smulY_add_sub_negY. -/
theorem s1617_smulY_add_sub_negY (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulY (n + m) - Affine.negY pointedCurve.toAffine (smulX (n + m)) (smulY (n + m)) =
      ((smulY m - Affine.negY pointedCurve.toAffine (smulX m) (smulY m)) *
        (smulX n - smulX (n + m)) -
       (smulY n - Affine.negY pointedCurve.toAffine (smulX n) (smulY n)) *
        (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [s1605_smulY_sub_negY (n + m) add_ne, s1605_smulY_sub_negY m hm,
    s1605_smulY_sub_negY n hn, smulX_sub_smulX n (n + m) hn add_ne,
    smulX_sub_smulX m (n + m) hm add_ne, smulX_sub_smulX m n hm hn,
    add_sub_cancel_left, add_sub_cancel_right]
  rw [s1617_smulY_add_sub_negY_aux]
  · congr
    rw [eq_div_iff]
    · linear_combination (norm := ring_nf)
        ((s1617_rel_nsm n m).mp (s1617_rel_ψᵤ (n + m) n (n - m) m))
    apply_rules [mul_ne_zero, polyToField_ψ_ne_zero]
  all_goals (apply polyToField_ψ_ne_zero; assumption)

/-- The exact S1612 chord-Y target. -/
theorem s1617_SmulYAddSubNegY : S1612SmulYAddSubNegY := s1617_smulY_add_sub_negY

end LeanFormal.IUT.XiFPaper.S1617SmulAddFromDraftActual
end
