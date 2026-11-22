import tmp.sheaf.xif.paper.Mzk1PaperNormDeficitActual
import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual

/-! # Mzk1P2DeficitActual (stage4 lane; A804 p=2 log-mu check)

A804: the p=2 "loophole" claim: at K = Q_2, e = 1, f = 1, n = 1, the p-power roots of
unity are {+1, -1} (2 elements).  Whether this gives r = 2 or r = 1 depends on the
definition of r.  The project reference `coord/ROUTES-FINAL-GAP.md` §6.1 (line 71) says:

  "vol(log O^) = 1/(q_k * p^r), where q_k = p^f is the residue field size and
   p^r is the NUMBER of p-power roots of unity in the field".

Hence at K = Q_2: #mu_{2^infinity}(Q_2) = 2 = 2^1, so **r = 1** (NOT 2), and
logMuPaper(2, e=1, r=1, n=1) = (1 + 1 - 1 - 1) * log 2 = 0.  The A804 loophole value
-log 2 arises only under the alternative "element count" reading r = #mu = 2, which
contradicts the project definition above (then Q_p(zeta_p) would give r = p, but the
project model uses r = 1 there).  Both arithmetic facts are recorded below so the
decision is explicit; the faithful one under the project definition is r = 1 (mu = 0).

No old file changed.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P2DeficitActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual

/-- The "element-count" reading r = 2 at K = Q_2 gives `logMuPaper = -log 2`. -/
theorem logMuPaper_2_r2_eq_neg_log2 :
    logMuPaper 2 1 2 1 = -Real.log 2 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- The project reading (`p^r = #mu_{p^infinity}`; at Q_2: 2 = 2^1) gives r = 1 and
`logMuPaper = 0`, NOT a negative value. -/
theorem logMuPaper_2_r1_eq_zero :
    logMuPaper 2 1 1 1 = 0 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- The abstract deficit at the A798 witness values (with the element-count r=2
place contributing `-log 2`) is `1 + log 2 > 0`; this is the A804 arithmetic. -/
theorem deficit_pos_of_p2_r2 :
    0 < paperNormDeficit 1 1 (-Real.log 2) 0 := by
  unfold paperNormDeficit
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Under the project definition (r = 1 at Q_2) the same witness has sumLogMu = 0,
so the deficit is `ssCoeff*A - sumTheta`; with the theta identity
`sumTheta = c_lana * A > 0` it is negative, i.e. the verdict holds:
`1 - 0 - sumTheta <= 0`.  This is algebra only (no claim about realizability of A). -/
theorem deficit_nonpos_of_p2_r1 (A sumTheta : Real)
    (hA : A = 1) (hTheta : 1 < sumTheta) :
    paperNormDeficit 1 A 0 sumTheta < 0 := by
  unfold paperNormDeficit
  subst hA
  linarith

/-- Faithful p=2 valuation: `logMuPaper 2 e r n` is nonnegative for the project
convention degrees: e=1, r=1, n=1 gives 0; e>=2 with r>=1 also gives > 0. -/
theorem logMuPaper_2_faithful_nonneg (e n : Real) (he : 1 <= e) (hn : 1 <= n) :
    0 <= logMuPaper 2 e 1 n := by
  unfold logMuPaper paperMuCoeff
  have hif : (if (2 : Real) = 2 then (1 : Real) else 0) = 1 := by norm_num
  rw [hif]
  have h1 : 0 <= (1 : Real) - 1 / e := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ he (lt_of_lt_of_le (by norm_num) he).le
  have h2 : 0 <= (1 : Real) - 1 / n := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ hn (lt_of_lt_of_le (by norm_num) hn).le
  have hlog : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hcoef : (1 + 1 - 1 / e - 1 / n : Real) = (1 - 1 / e) + (1 - 1 / n) := by ring
  rw [hcoef]
  positivity

#print axioms logMuPaper_2_r2_eq_neg_log2
#print axioms logMuPaper_2_r1_eq_zero
#print axioms deficit_pos_of_p2_r2
#check logMuPaper_2_r1_eq_zero
#check deficit_nonpos_of_p2_r1

end LeanFormal.IUT.XiFPaper.Mzk1P2DeficitActual
end
