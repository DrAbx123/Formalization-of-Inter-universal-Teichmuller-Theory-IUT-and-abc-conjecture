import tmp.sheaf.xif.paper.Mzk1ThetaCancelActual
import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import Mathlib.Tactic

/-! # A808 r-definition audit V2: faithful per-place coefficients and branch closure

CORRECTION: `r` is the EXPONENT of the group of p-power roots of unity in the
local field (`#mu_{p^infinity} = p^r`), not the number of l-th roots and not an
element count.  Hence:
* `p = 2`: `#mu_{2^infinity}(Q_2) = 2 = 2^1`, so `r = 1`; coefficient `0`.
* `p = 3`: `Q_3(zeta_3)`: `e = n = 2`, `r = 1`; coefficient `0`.
* `p = 5`: `Q_5(zeta_5)`: `e = n = 4`, `r = 1`; coefficient `1/2`.
* `p = 11`: `Q_11` unramified, only 11-power root is `1`, so `r = 0`;
  coefficient `1 - 1/1 - 0 = 0` (NOT `-1`; mu_5 has order 5, not 11).

All faithful per-place coefficients are nonnegative.  In addition, with
`nC = l* = k` and `l = 2k+1`, `c_lana = ssCoeff` exactly, so the deficit
cancels the A term: `deficit = -sumLogMuPaper`.  Branch A (`sumLogMuPaper >= 0`)
therefore gives `deficit <= 0` unconditionally in this normalization; the
branch-B negative candidate (p=11 with the misread r=1) does not exist. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RDefinitionAuditV2Actual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual
open LeanFormal.IUT.XiFPaper.Mzk1LargeLTheoremActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaCancelActual

/-- Faithful r-values and coefficients at the candidate places. -/
structure FaithfulPlace where
  p : Real
  e : Real
  n : Real
  r : Real
  role : String

def faithfulPlaces : List FaithfulPlace :=
  [ { p := 2, e := 1, n := 1, r := 1, role := "Q_2: #mu_{2^inf} = 2 = 2^1" },
    { p := 2, e := 1, n := 4, r := 1, role := "unramified degree-4 over Q_2" },
    { p := 3, e := 2, n := 2, r := 1, role := "Q_3(zeta_3)" },
    { p := 5, e := 4, n := 4, r := 1, role := "Q_5(zeta_5)" },
    { p := 11, e := 1, n := 1, r := 0, role := "Q_11 unramified; 11-power roots = {1}" } ]

theorem faithfulPlaces_length : faithfulPlaces.length = 5 := rfl

/-- p=2, Q_2: coefficient zero, not negative. -/
theorem coeff_p2_Q2 : paperMuCoeff 2 1 1 1 = 0 := by
  unfold paperMuCoeff
  norm_num

/-- p=2, unramified degree 4: coefficient 3/4. -/
theorem coeff_p2_deg4 : paperMuCoeff 2 1 1 4 = 3 / 4 := by
  unfold paperMuCoeff
  norm_num

/-- p=3, Q_3(zeta_3): coefficient zero. -/
theorem coeff_p3_zeta : paperMuCoeff 3 2 1 2 = 0 := by
  unfold paperMuCoeff
  norm_num

/-- p=5, Q_5(zeta_5): coefficient 1/2. -/
theorem coeff_p5_zeta : paperMuCoeff 5 4 1 4 = 1 / 2 := by
  unfold paperMuCoeff
  norm_num

/-- p=11, Q_11: coefficient zero (NOT -1). -/
theorem coeff_p11_unramified : paperMuCoeff 11 1 0 1 = 0 := by
  unfold paperMuCoeff
  norm_num

theorem logMuPaper_11_eq_zero : logMuPaper 11 1 0 1 = 0 := by
  unfold logMuPaper
  rw [coeff_p11_unramified]
  ring

/-- All faithful candidate coefficients are nonnegative. -/
theorem faithful_coeffs_nonneg :
    0 <= paperMuCoeff 2 1 1 1 ∧ 0 <= paperMuCoeff 2 1 1 4 ∧
    0 <= paperMuCoeff 3 2 1 2 ∧ 0 <= paperMuCoeff 5 4 1 4 ∧
    0 <= paperMuCoeff 11 1 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [paperMuCoeff]

/-- Branch A: theta cancellation `deficit = -sumLogMu`, and nonpositive on nonnegative
`sumLogMu` (re-export of stage4 green). -/
theorem branchA_deficit_cancel_thetaSum (k : Nat) (hk : 2 <= k) (A sumLogMu : Real) :
    paperDeficit (ssCoeff (2 * (k : Real) + 1)) A sumLogMu
        (thetaSumPaper k (2 * (k : Real) + 1) A) = -sumLogMu :=
  paperDeficit_cancel_thetaSum k hk A sumLogMu

theorem branchA_deficit_nonpos (k : Nat) (hk : 2 <= k) (A sumLogMu : Real)
    (h : 0 <= sumLogMu) :
    paperDeficit (ssCoeff (2 * (k : Real) + 1)) A sumLogMu
        (thetaSumPaper k (2 * (k : Real) + 1) A) <= 0 := by
  rw [branchA_deficit_cancel_thetaSum k hk A sumLogMu]
  linarith

#print axioms faithful_coeffs_nonneg
#print axioms branchA_deficit_nonpos
#print axioms logMuPaper_11_eq_zero

end LeanFormal.IUT.XiFPaper.Mzk1RDefinitionAuditV2Actual
