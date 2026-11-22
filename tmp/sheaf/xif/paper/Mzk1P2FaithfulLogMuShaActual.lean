import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import Mathlib.Tactic

/-! # A804 correction: p = 2 paper-normalized log-mu is NOT negative

Definition check: `coord/ROUTES-FINAL-GAP.md` line 71 defines `p^r` to be the
*number* of p-power roots of unity, not the count `r` itself.  Hence at
`K = Q_2`, `#mu_{2^infinity}(Q_2) = 2 = 2^1` gives `r = 1`, and
`logMuPaper 2 1 1 1 = (1 + 1 - 1 - 1) * log 2 = 0`, NOT `-log 2`.
The A804 value `-log 2` corresponds to the alternative (non-project)
"count" reading `r = 2`; it is recorded below only as an arithmetic fact.

Under the faithful constraints `e >= 1`, `0 <= r <= n`, `n > 0`, the p=2
coefficient is `2 - 1/e - r/n >= 0`, so `logMuPaper 2 e r n >= 0`: the
p=2 negative-log-mu loophole is closed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P2FaithfulLogMuShaActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

/-- Faithful project value at `Q_2` (`r = 1`): zero, not negative. -/
theorem logMuPaper_2_r1_eq_zero : logMuPaper 2 1 1 1 = 0 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- Unfaithful count-reading `r = 2` gives `-log 2`; kept as a record only. -/
theorem logMuPaper_2_r2_eq_neg_log2 : logMuPaper 2 1 2 1 = -Real.log 2 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- Faithful p=2 nonnegativity under `e >= 1`, `0 <= r <= n`, `n > 0`. -/
theorem logMuPaper_2_nonneg {e n r : Real} (he : 1 <= e) (hn : 0 < n)
    (hr : 0 <= r) (hrn : r <= n) : 0 <= logMuPaper 2 e r n := by
  unfold logMuPaper paperMuCoeff
  norm_num
  have he1 : e⁻¹ <= 1 := inv_le_one_of_one_le₀ he
  have hrn' : r / n <= 1 := div_le_one_of_le₀ hrn hn.le
  have hcoef : 0 <= (2 - e⁻¹ - r / n : Real) := by linarith
  have hlog : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  exact mul_nonneg hcoef hlog

#print axioms logMuPaper_2_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1P2FaithfulLogMuShaActual
