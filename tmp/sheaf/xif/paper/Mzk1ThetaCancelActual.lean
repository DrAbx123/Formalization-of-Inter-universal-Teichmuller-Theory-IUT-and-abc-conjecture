import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import tmp.sheaf.xif.paper.Mzk1PaperNormThetaActual
import tmp.sheaf.xif.paper.Mzk1PaperNormDeficitActual
import tmp.sheaf.xif.paper.Mzk1LargeLTheoremActual

/-! # Mzk1ThetaCancelActual (stage4 lane; A805 B10 verification: theta/deficit cancellation)

A805 B10 data verification:  lana `Iut/Concrete/LocalEstimate.lean:117-118` defines the
number of capsules as `nCaps := (D.ℓ - 1)/2 = l*`.  Hence in the paper deficit
`deficit = ssCoeff*A - (sumLogMu + sumTheta)` with `sumTheta = c_lana*A` and
`c_lana = (sFactor(nC)-1)/(2l)` we have, since `sFactor(l*) = l(l+1)/12`:

  `c_lana(l*) = (l(l+1)/12 - 1)/(2l) = (l+1)/24 - 1/(2l) = ssCoeff(l)`   EXACTLY.

Therefore `sumTheta = ssCoeff*A` and the deficit CANCELS the `A` term entirely:

  `deficit = ssCoeff*A - sumLogMu - ssCoeff*A = -sumLogMu`.

Consequences (model level, no old file changed):
  (a) the q-magnitude normalization `A = (1/(2l))·sum_v qlog_v` cancels from the deficit;
  (b) under the project r-convention (each `logMuPaper >= 0`) the deficit is `<= 0`
      (paper 3.12 normalized verdict holds);
  (c) under the element-count r-convention any negative `logMuPaper` place (e.g. p=11,
      e=n=1, r=1 element => -log 11) makes the deficit positive (counterexample shape).

Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaCancelActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual
open LeanFormal.IUT.XiFPaper.Mzk1LargeLTheoremActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

/-- Sum of `(j+1)^2` for `j < n`, in closed form over `Real`. -/
theorem sum_range_sq_one_add (n : Nat) :
    (∑ j ∈ Finset.range n, (((j : Real) + 1) ^ 2 : Real)) =
      (n : Real) * ((n : Real) + 1) * (2 * (n : Real) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Closed form of the lana capsule factor: `sFactor n = (n+1)(2n+1)/6`. -/
theorem sFactor_eq (n : Nat) (hn : 0 < n) :
    sFactor n = ((n : Real) + 1) * (2 * (n : Real) + 1) / 6 := by
  unfold sFactor
  rw [sum_range_sq_one_add]
  have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

/-- **B10 cancellation**: with `nC = l* = k` capsules and `l = 2k+1` (l odd),
`c_lana(l*) = ssCoeff(l)` exactly. -/
theorem clana_eq_ssCoeff (k : Nat) (hk : 2 ≤ k) :
    clana k (2 * (k : Real) + 1) = ssCoeff (2 * (k : Real) + 1) := by
  unfold clana ssCoeff
  have hk0 : 0 < k := by omega
  rw [sFactor_eq k hk0]
  have hkR : (k : Real) ≠ 0 := by exact_mod_cast hk0.ne'
  have hlR : 2 * (k : Real) + 1 ≠ 0 := by positivity
  field_simp [hkR, hlR]
  ring_nf

/-- **Deficit cancellation**: substituting the theta sum with `nC = l* = k` capsules,
`paperDeficit (ssCoeff l) A sumLogMu (clana k l * A) = -sumLogMu`. -/
theorem paperDeficit_cancel (k : Nat) (hk : 2 ≤ k) (A sumLogMu : Real) :
    paperDeficit (ssCoeff (2 * (k : Real) + 1)) A sumLogMu
        (clana k (2 * (k : Real) + 1) * A) = -sumLogMu := by
  unfold paperDeficit
  rw [clana_eq_ssCoeff k hk]
  ring

/-- Same statement with the theta sum in the `thetaSumPaper` form (nonempty capsules). -/
theorem paperDeficit_cancel_thetaSum (k : Nat) (hk : 2 ≤ k) (A sumLogMu : Real) :
    paperDeficit (ssCoeff (2 * (k : Real) + 1)) A sumLogMu
        (thetaSumPaper k (2 * (k : Real) + 1) A) = -sumLogMu := by
  rw [thetaSumPaper_eq_clana_mul k (by omega) (2 * (k : Real) + 1) A]
  exact paperDeficit_cancel k hk A sumLogMu

/-- **Branch-A sign**: if the paper-normalized log-mu sum is nonnegative, the deficit is
nonpositive (the normalized verdict holds), for `nC = l* = k`, `l = 2k+1`. -/
theorem paperDeficit_nonpos_of_sum_nonneg (k : Nat) (hk : 2 ≤ k) (A sumLogMu : Real)
    (h : 0 ≤ sumLogMu) :
    paperDeficit (ssCoeff (2 * (k : Real) + 1)) A sumLogMu
        (clana k (2 * (k : Real) + 1) * A) ≤ 0 := by
  rw [paperDeficit_cancel k hk A sumLogMu]
  linarith

/-- Per-place branch-A nonnegativity for odd unramified places (`e = 1`, no p-power
torsion `r = 0`): the paper coefficient is `0`. -/
theorem paperMuCoeff_odd_unramified (p : Real) (hp2 : p ≠ 2) :
    paperMuCoeff p 1 0 1 = 0 := by
  unfold paperMuCoeff
  rw [if_neg hp2]
  norm_num


/-- Corrected A808 reading: r is the p-power-root EXPONENT.  At p = 11 the only
11-power root of unity in Q_11 is 1, so r = 0 and the coefficient is 0 (the 5th roots
of unity are l-torsion, irrelevant to the local r). -/
theorem logMuPaper_11_eq_zero : logMuPaper 11 1 0 1 = 0 := by
  unfold logMuPaper paperMuCoeff
  norm_num

/-- Corrected A808 candidate places: p=2 (e=1,n=4,r=1), p=5 (e=4,n=4,r=1),
p=11 (e=1,n=1,r=0).  The sum is (3/4)log2 + (1/2)log5 >= 0. -/
theorem candidate_sum_nonneg :
    0 ≤ logMuPaper 2 1 1 4 + logMuPaper 5 4 1 4 + logMuPaper 11 1 0 1 := by
  rw [logMuPaper_11_eq_zero]
  unfold logMuPaper paperMuCoeff
  norm_num
  positivity

/-- With nC = l* = 2, l = 5 and the corrected candidate places, the deficit equals
-( (3/4)log2 + (1/2)log5 ) < 0: the p=2-branch counterexample DISAPPEARS after A808. -/
theorem candidate_deficit_neg (A : Real) :
    paperDeficit (ssCoeff 5) A
        (logMuPaper 2 1 1 4 + logMuPaper 5 4 1 4 + logMuPaper 11 1 0 1)
        (clana 2 5 * A) < 0 := by
  have hc := paperDeficit_cancel 2 (by norm_num) A
    (logMuPaper 2 1 1 4 + logMuPaper 5 4 1 4 + logMuPaper 11 1 0 1)
  norm_num at hc
  rw [hc]
  have hpos : 0 < logMuPaper 2 1 1 4 + logMuPaper 5 4 1 4 + logMuPaper 11 1 0 1 := by
    rw [logMuPaper_11_eq_zero]
    unfold logMuPaper paperMuCoeff
    norm_num
    positivity
  linarith

#print axioms paperDeficit_cancel

#print axioms paperDeficit_cancel_thetaSum
#print axioms paperDeficit_nonpos_of_sum_nonneg
#check clana_eq_ssCoeff
#check sFactor_eq

end LeanFormal.IUT.XiFPaper.Mzk1ThetaCancelActual
end
