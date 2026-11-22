import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import tmp.sheaf.xif.paper.Mzk1IVThm110LogQActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110SlackReductionActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110LogQActual
/-- The Step (v) slack `hSlack` is not an independent paper input: it follows
from Cor 3.12 rearrangement under `l ≥ 7`, `dmod ≥ 1`, and nonnegativity. -/
theorem thm110_slack_of_hCor312
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T := by
  have h312 : (1 / 6) * T.logQ ≤
      (1 + 12 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) +
        (2 / T.l ^ 2) * T.logQ := by
    have h := hCor312
    simp only [thm110Lhs, thm110Mid, thm110Cor312Gap] at h
    have hfac : (1 / 6 : Real) * (12 / T.l ^ 2) = 2 / T.l ^ 2 := by
      field_simp
      ring
    rw [hfac] at h
    simpa [one_div, mul_assoc, mul_left_comm, mul_comm] using h
  have hl0 : (0 : Real) < T.l := by linarith
  have hbound := logQ_bound_of_hCor312
    (l := T.l) (d := T.dmod) (S := T.logDFpd + T.logFFpd)
    (E := T.eStar * T.l + T.etaPrm) (Q := T.logQ) hl hd hS hE h312
  have hscale : (0 : Real) ≤ 2 / T.l ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbound hscale
  have hslack : (2 / T.l ^ 2) * T.logQ ≤
      (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) := by
    have hrhs : (2 / T.l ^ 2) *
        (4 * T.dmod * T.l * (T.logDFpd + T.logFFpd) +
          5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) =
        (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
          10 * (T.eStar * T.l + T.etaPrm) := by
      field_simp
      ring
    linarith
  unfold thm110Cor312Gap thm110Rhs thm110Mid
  have hfac2 : (1 / 6 : Real) * (12 / T.l ^ 2) * T.logQ =
      (2 / T.l ^ 2) * T.logQ := by
    field_simp
    ring
  rw [hfac2]
  have hdiff : ((1 + 20 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
      20 * (T.eStar * T.l + T.etaPrm)) -
      ((1 + 12 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm)) =
      (8 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
        10 * (T.eStar * T.l + T.etaPrm) := by
    field_simp
    ring
  rw [hdiff]
  exact hslack
#check thm110_slack_of_hCor312
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110SlackReductionActual
end