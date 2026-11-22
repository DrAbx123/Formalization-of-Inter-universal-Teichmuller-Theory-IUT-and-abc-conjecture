import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import tmp.sheaf.xif.paper.Mzk1PaperNormDeficitActual
import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import Mathlib.Tactic

/-! # A805 audit: paper / project definition of `r` in the log-shell volume

## Findings
1. The project audit note `coord/ROUTES-FINAL-GAP.md` §6.1 line 71 writes
   `vol(log O^×) = 1/(q_k * p^r)` with `q_k = p^f` and says `p^r` is the
   *number* of p-power roots of unity.  Hence `r = log_p #mu`, an EXPONENT.
2. The lana Lean files `Iut/Concrete/LocalConstruct/{LocalLogShell,LogShell,
   Integral,Volume,ScaleVolume}.lean` define the log-shell as
   `(2p)^{-1} log(1+m)` and prove scaling laws/inclusions; they do NOT introduce
   an explicit `r` variable, so they are compatible with the exponent reading and
   give no element-count definition.
3. The project Lean files `IntegralLogShellIndexResidueFormula`/`IntegralLogShellHaarIndex`
   have no `r`; the only cardinal is `Nat.card (CommGroup.torsion (Integers K)^×)`
   (all roots of unity), and `logShellResidueCard = p^f`.  Thus the formal project
   also does not define `r` as an element count.

## Verdict
Paper convention and project convention agree: `r` is the exponent with
`#mu_{p^infinity} = p^r`.  Consequently for `K = Q_2`: `#mu = 2 = 2^1`, so
`r = 1`, and `logMuPaper 2 1 1 1 = 0` (not `-log 2`).  The p = 2 negative-log-mu
counterexample route is CLOSED under the faithful convention.

The arithmetic of the alternative (element-count) reading is recorded only for
the audit trail. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RDefinitionAuditActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

/-- Faithful exponent convention at `Q_2`: `r = 1`, so log-mu is zero. -/
theorem p2_faithful_logMu_zero : logMuPaper 2 1 1 1 = 0 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- Element-count misreading `r = 2`: this gives `-log 2` and is recorded as
unfaithful. -/
theorem p2_count_reading_logMu_neg : logMuPaper 2 1 2 1 = -Real.log 2 := by
  unfold logMuPaper paperMuCoeff
  norm_num

structure RDefinitionRow where
  source : String
  definition : String
  status : String
  deriving Repr

def rDefinitionRows : List RDefinitionRow :=
  [ { source := "coord/ROUTES-FINAL-GAP.md §6.1 L71", definition := "p^r = number of p-power roots of unity (r = log_p #mu)", status := "EXPONENT" },
    { source := "lana Iut/Concrete/LocalConstruct/{LocalLogShell,LogShell,Integral,Volume,ScaleVolume}.lean", definition := "log-shell (2p)^-1 log(1+m); scaling laws; no explicit r", status := "COMPATIBLE (no element-count)" },
    { source := "project IntegralLogShellIndexResidueFormula / IntegralLogShellHaarIndex", definition := "no r; only torsion cardinal and logShellResidueCard = p^f", status := "NO-FORMAL-r" },
    { source := "Q_2 faithful value", definition := "#mu_{2^infinity} = 2 = 2^1 => r = 1; logMuPaper = 0", status := "NON-COUNTEREXAMPLE" },
    { source := "Q_2 element-count misreading", definition := "r = 2 => logMuPaper = -log 2", status := "UNFAITHFUL" } ]

theorem rDefinitionRows_length : rDefinitionRows.length = 5 := rfl

#print axioms p2_faithful_logMu_zero
#print axioms p2_count_reading_logMu_neg

/-! ### A808: r semantics (p-power roots of unity exponent), faithful coefficient table,
and the branch-A closure `deficit = -sumLogMuPaper` -/

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual

/-- r semantics: `p^r = #mu_{p^infinity}` (the p-POWER roots of unity), so r is the exponent.
Hence: Q_2 r=1 (#{±1}=2=2^1); Q_5(zeta_5) r=1 (#mu_5=5); Q_11 r=0 (only the 11-power
root 1; the 5-th roots in Q_11 are irrelevant to the p=11 local r). -/
theorem r_semantics_q2 : (2 : ℕ) = 2 ^ 1 := by norm_num
theorem r_semantics_q5 : (5 : ℕ) = 5 ^ 1 := by norm_num
theorem r_semantics_q11 : (1 : ℕ) = 11 ^ 0 := by norm_num

/-- Faithful coefficients from the hull definition `paperMuCoeff p e r n`.
p=2 (e=1,r=1,n=1): `0`;  p=5 (e=4,r=1,n=4): `1/2`;  p=11 (e=1,r=0,n=1): `0`;
all `>= 0'. -/
theorem paperMuCoeff_q2 : paperMuCoeff 2 1 1 1 = 0 := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.paperMuCoeff
  norm_num
theorem paperMuCoeff_q5 : paperMuCoeff 5 4 1 4 = 1 / 2 := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.paperMuCoeff
  norm_num
theorem paperMuCoeff_q11 : paperMuCoeff 11 1 0 1 = 0 := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual.paperMuCoeff
  norm_num

/-- **A cancellation (stage4)**: with `sumTheta = ssCoeff*A` the deficit is `-sumLogMu`. -/
theorem deficit_cancel (ssCoeff A sumLogMu : ℝ) :
    paperNormDeficit ssCoeff A sumLogMu (ssCoeff * A) = -sumLogMu := by
  unfold paperNormDeficit
  ring

/-- **Branch A closure**: if every paper-normalized local term is nonnegative, the deficit is
nonpositive (verdict holds). -/
theorem deficit_nonpos_of_each_nonneg {ι : Type*} [Fintype ι] (ssCoeff A : ℝ)
    (mu : ι → ℝ) (h : ∀ i, 0 ≤ mu i) :
    paperNormDeficit ssCoeff A (∑ i, mu i) (ssCoeff * A) ≤ 0 := by
  rw [deficit_cancel]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => h i))

end LeanFormal.IUT.XiFPaper.Mzk1RDefinitionAuditActual
