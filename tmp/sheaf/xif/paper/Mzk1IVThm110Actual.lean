import tmp.sheaf.xif.paper.Mzk1Thm110SlackActual
import tmp.sheaf.xif.paper.Mzk1IVThm110LogQActual
import tmp.sheaf.xif.paper.Mzk1S1DisplayCThetaActualV2
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Tactic
/-! IUT IV Thm 1.10: actual-data instantiation and structural nonnegativities.

This file discharges the four nonnegativity hypotheses from actual data
(`l ≥ 5`, `dmod = [F_mod:Q]`, `dFpd, fFpd ≥ 1`, `eStar*l+etaPrm ≥ 0`), and proves the
F-dictionary step.  The two genuine remaining inputs are recorded explicitly:
* the numeric `logQ` bound;
* `CThetaPaper ≥ -1` (Cor 3.12), or equivalently `hCor312`.
No sorry/extra axiom is introduced. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm110SlackActual
open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
/-- Actual IV data: prime l≥5, dmod=[F_mod:Q], dFpd/fFpd≥1, and the paper η term. -/
structure ActualThm110Data where
  l : PrimeGeFive
  l_ge_seven : 7 ≤ l.value
  dmod : Nat
  dmod_ge_one : 1 ≤ dmod
  dFpd : Real
  fFpd : Real
  dFpd_ge_one : 1 ≤ dFpd
  fFpd_ge_one : 1 ≤ fFpd
  eStar : Real
  etaPrm : Real
  logQ : Real
  logQ_pos : 0 < logQ
  eta_nonneg : 0 ≤ eStar * (l.value : Real) + etaPrm
/-- The actual display terms. -/
def ActualThm110Data.toTerms (A : ActualThm110Data) : Thm110DisplayTerms where
  l := (A.l.value : Real)
  dmod := (A.dmod : Real)
  logDFpd := Real.log A.dFpd
  logFFpd := Real.log A.fFpd
  eStar := A.eStar
  etaPrm := A.etaPrm
  logQ := A.logQ
/-- Structural: `0 < l`. -/
theorem actual_hl (A : ActualThm110Data) : 0 < (A.toTerms).l := by
  simp only [ActualThm110Data.toTerms]
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 7) A.l_ge_seven)
/-- Structural: `0 ≤ dmod`. -/
theorem actual_hd (A : ActualThm110Data) : 0 ≤ (A.toTerms).dmod := by
  unfold ActualThm110Data.toTerms
  positivity
/-- Structural: `0 ≤ log dFpd + log fFpd`. -/
theorem actual_hsum (A : ActualThm110Data) :
    0 ≤ (A.toTerms).logDFpd + (A.toTerms).logFFpd := by
  unfold ActualThm110Data.toTerms
  have h1 : 0 ≤ Real.log A.dFpd := Real.log_nonneg A.dFpd_ge_one
  have h2 : 0 ≤ Real.log A.fFpd := Real.log_nonneg A.fFpd_ge_one
  linarith
/-- Structural: `0 ≤ eStar*l + etaPrm`. -/
theorem actual_he (A : ActualThm110Data) :
    0 ≤ (A.toTerms).eStar * (A.toTerms).l + (A.toTerms).etaPrm := by
  unfold ActualThm110Data.toTerms
  exact A.eta_nonneg
/-- F-dictionary step: `log d_Ftpd + log f_Ftpd ≤ log d_F + log f_F` from actual
dFpd/fFpd≤dF/fF and positivity. -/
theorem f_dictionary {dFpd fFpd dF fF : Real}
    (hdFpd : 0 < dFpd) (hfFpd : 0 < fFpd)
    (hdd : dFpd ≤ dF) (hff : fFpd ≤ fF) :
    Real.log dFpd + Real.log fFpd ≤ Real.log dF + Real.log fF :=
  add_le_add (Real.log_le_log hdFpd hdd) (Real.log_le_log hfFpd hff)
/-- Thm 1.10 display from actual data plus the two genuine remaining inputs. -/
theorem thm110_display_of_actual_data
    (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (hQ : A.toTerms.logQ ≤
      (4 * A.toTerms.dmod * A.toTerms.l) *
        (A.toTerms.logDFpd + A.toTerms.logFFpd) +
      5 * A.toTerms.l ^ 2 *
        (A.toTerms.eStar * A.toTerms.l + A.toTerms.etaPrm)) :
    thm110Lhs A.toTerms ≤ thm110Rhs A.toTerms :=
  thm110_final_display_of_logQ_bound A.toTerms hCor312
    (actual_hl A) (actual_hd A) (actual_hsum A) (actual_he A) hQ
/-- Thm 1.10 display from actual data plus the paper inputs `CThetaPaper ≥ -1` and
the numeric `logQ` bound. -/
theorem thm110_display_of_CThetaPaper
    (A : ActualThm110Data)
    (hC : -1 ≤ CThetaPaper A.l A.logQ (A.dmod : Real) A.dFpd A.fFpd A.eStar A.etaPrm)
    (hQ : A.toTerms.logQ ≤
      (4 * A.toTerms.dmod * A.toTerms.l) *
        (A.toTerms.logDFpd + A.toTerms.logFFpd) +
      5 * A.toTerms.l ^ 2 *
        (A.toTerms.eStar * A.toTerms.l + A.toTerms.etaPrm)) :
    thm110Lhs A.toTerms ≤ thm110Rhs A.toTerms :=
  thm110_final_display_of_CThetaPaper_logQ A.toTerms A.l A.dFpd A.fFpd
    rfl rfl rfl A.logQ_pos hC (actual_hl A) (actual_hd A) (actual_hsum A)
    (actual_he A) hQ
/-- Thm 1.10 display from actual data and hCor312 only: the numeric `logQ` bound is
derived by absorbing the `2/l^2 logQ` term of hCor312 (l>=7, dmod>=1). -/
theorem thm110_display_of_hCor312
    (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms) :
    thm110Lhs A.toTerms ≤ thm110Rhs A.toTerms := by
  have h312 : (1 / 6) * A.toTerms.logQ ≤
      (1 + 12 * A.toTerms.dmod / A.toTerms.l) *
        (A.toTerms.logDFpd + A.toTerms.logFFpd) +
      10 * (A.toTerms.eStar * A.toTerms.l + A.toTerms.etaPrm) +
      (2 / A.toTerms.l ^ 2) * A.toTerms.logQ := by
    have h := hCor312
    simp only [thm110Lhs, thm110Mid, thm110Cor312Gap, ActualThm110Data.toTerms] at h
    have hfac : (1 / 6 : Real) * (12 / (A.l.value : Real) ^ 2) =
        2 / (A.l.value : Real) ^ 2 := by
      field_simp
      norm_num
    rw [hfac] at h
    simpa [ActualThm110Data.toTerms, one_div] using h
  apply thm110_display_of_actual_data A hCor312
  exact LeanFormal.IUT.XiFPaper.Mzk1IVThm110LogQActual.logQ_bound_of_hCor312
    (l := A.toTerms.l) (d := A.toTerms.dmod) (S := A.toTerms.logDFpd + A.toTerms.logFFpd)
    (E := A.toTerms.eStar * A.toTerms.l + A.toTerms.etaPrm) (Q := A.toTerms.logQ)
    (by
      change (7 : Real) ≤ (A.l.value : Real)
      exact_mod_cast A.l_ge_seven)
    (by
      change (1 : Real) ≤ (A.dmod : Real)
      exact_mod_cast A.dmod_ge_one)
    (actual_hsum A) (actual_he A) h312
/-- Exact remaining unconditional inputs, not proved here. -/
def remainingInputs : List String :=
  [ "numeric logQ bound: logQ <= 4*dmod*l*(log dFpd + log fFpd) + 5*l^2*(eStar*l+etaPrm)",
    "Cor 3.12: -1 <= CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm",
    "actual source identification of (q,height,dF,fF,eStar,etaPrm) with ActualThm110Data fields" ]
theorem remainingInputs_length : remainingInputs.length = 3 := rfl
#check thm110_display_of_actual_data
#check thm110_display_of_CThetaPaper
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
end
