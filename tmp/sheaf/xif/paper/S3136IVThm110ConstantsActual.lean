import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Stage-4 host: IUT IV Theorem 1.10 constant arithmetic and display shapes

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt,
Theorem 1.10 p.1255-1385.

CONSUMER: mainline's IUT IV statement skeleton. This file formalizes the CLASS A
arithmetic of the Theorem 1.10 constants and records the exact display shapes as
named real formulas (no claim of the inequalities themselves; those are class B).

* d_mod = [F_mod : Q]; e_mod = maximal ramification index;
  d*_mod = 2^12 * 3^3 * 5 * d_mod; e*_mod = 2^12 * 3^3 * 5 * e_mod (p.1264-1272);
  hence e*_mod <= d*_mod whenever e_mod <= d_mod (Remark 1.10.7, (i) p.2292-2298).
* The constant C_Theta of [IUTchIII], Corollary 3.12 (p.1363-1375):
  (l+1)/4 * |log q| * { (1 + 12 d_mod/l)(log d_Ftpd + log f_Ftpd)
  + 10(e*_mod l + eta_prm) - (1/6)(1 - 12/l^2) log q } - 1.
* The final displays (p.1376-1385):
  (1/6) log(q) <= (1 + 20 d_mod/l)(log d_Ftpd + log f_Ftpd) + 20(e*_mod l + eta_prm).

LABEL: class A constant arithmetic + display shapes (data/defs, no claim).
Registry frozen; new file only. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3136IVThm110ConstantsActual

/-- The Theorem 1.10 constant d*_mod = 2^12 * 3^3 * 5 * d_mod. -/
def lgpDStarMod (dmod : ℕ) : ℕ :=
  2 ^ 12 * 3 ^ 3 * 5 * dmod

/-- The Theorem 1.10 constant e*_mod = 2^12 * 3^3 * 5 * e_mod. -/
def lgpEStarMod (emod : ℕ) : ℕ :=
  2 ^ 12 * 3 ^ 3 * 5 * emod

/-- d*_mod = 552960 * d_mod. -/
theorem lgpDStarMod_eq (dmod : ℕ) :
    lgpDStarMod dmod = 552960 * dmod := by
  unfold lgpDStarMod
  norm_num

/-- e*_mod = 552960 * e_mod. -/
theorem lgpEStarMod_eq (emod : ℕ) :
    lgpEStarMod emod = 552960 * emod := by
  unfold lgpEStarMod
  norm_num

/-- e*_mod <= d*_mod whenever e_mod <= d_mod (Remark 1.10.7, (i)). -/
theorem lgpEStarMod_le_lgpDStarMod {emod dmod : ℕ} (h : emod ≤ dmod) :
    lgpEStarMod emod ≤ lgpDStarMod dmod := by
  rw [lgpEStarMod_eq, lgpDStarMod_eq]
  nlinarith

/-- The C_Theta formula shape of Theorem 1.10 (p.1363-1375), as a real function of
the numeric data. -/
noncomputable def lgpCThetaShape (ell : ℕ) (logq dFtpd fFtpd dmod emod eta : ℝ) : ℝ :=
  ((ell : ℝ) + 1) / 4 * |logq| *
    ((1 + 12 * dmod / (ell : ℝ)) * (Real.log dFtpd + Real.log fFtpd)
      + 10 * (emod * (ell : ℝ) + eta)
      - (1 / 6) * (1 - 12 / ((ell : ℝ) ^ 2)) * logq)
  - 1

/-- The final displayed inequality shape of Theorem 1.10 (p.1376-1385). -/
noncomputable def lgpThm110DisplayShape (ell : ℕ) (logq dFtpd fFtpd dmod emod eta : ℝ) : Prop :=
  (1 / 6) * logq ≤
    (1 + 20 * dmod / (ell : ℝ)) * (Real.log dFtpd + Real.log fFtpd)
      + 20 * (emod * (ell : ℝ) + eta)

#check lgpDStarMod_eq
#check lgpEStarMod_le_lgpDStarMod
#check lgpCThetaShape
#check lgpThm110DisplayShape

end LeanFormal.IUT.XiFPaper.S3136IVThm110ConstantsActual