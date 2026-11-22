import tmp.sheaf.xif.paper.S3131PaperRouteSkeletonActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual
import tmp.sheaf.xif.paper.S3131IUTIVTheorem110InputActual
import tmp.sheaf.xif.paper.Mzk1IVThm110LogQActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3171: IUT IV §1 Theorem 1.10 — FINAL DISPLAY (Step (v)) as an explicit conditional theorem

Paper: IUT IV §1 "Log-volume Estimates" (corpus l.38), Theorem 1.10 (Log-volume
Estimates for Θ-Pilot Objects) at corpus l.1255; proof steps (i)-(viii); the FINAL
DISPLAY is in Step (v) (corpus l.1362-1385):

  (1/6)·log(q) ≤ (1+20·d_mod/l)·(log(d_Ftpd)+log(f_Ftpd)) + 20·(e*_mod·l+η_prm)
               ≤ (1+20·d_mod/l)·(log(d_F)+log(f_F)) + 20·(e*_mod·l+η_prm),

where C_Θ = (l+1)/(4·|log q|) · { (1+12·d_mod/l)(log d_Ftpd + log f_Ftpd)
  + 10(e*_mod·l+η_prm) − (1/6)(1−12/l²)log q } − 1 ∈ R is the constant of
[IUTchIII] Cor 3.12 and the display follows from "C_Θ ≥ −1".

This file states the display EXACTLY and proves it conditionally from two named
inputs:
* hCor312 : from Cor 3.12's C_Θ ≥ −1 (the route's (b)/(c) interface consumer),
* hSlack  : the paper's arithmetic slack step of Step (v) (class B paper-input).
Both are explicit; no re-proof of the paper's Step (v) is claimed.

It also wires the (b)/(c) UNDILATED interfaces to the route skeleton:
UndilatedHeightBound + UndilatedRegionBound => PaperRouteResidualData => ABCConjecture.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteSkeletonActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

/-- The terms of the Thm 1.10 final display (corpus l.1362-1385). -/
structure Thm110DisplayTerms where
  /-- the prime l ≥ 5 -/
  l : ℝ
  /-- d_mod = [F_mod : Q] -/
  dmod : ℝ
  /-- log(d_Ftpd) -/
  logDFpd : ℝ
  /-- log(f_Ftpd) -/
  logFFpd : ℝ
  /-- e*_mod -/
  eStar : ℝ
  /-- η_prm (Prop 1.6 constant) -/
  etaPrm : ℝ
  /-- log(q) -/
  logQ : ℝ

/-- The left side of the display: (1/6)·log(q). -/
def thm110Lhs (T : Thm110DisplayTerms) : ℝ := (1 / 6) * T.logQ

/-- The middle term of the display over F_tpd. -/
def thm110Mid (T : Thm110DisplayTerms) : ℝ :=
  (1 + 12 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
    10 * (T.eStar * T.l + T.etaPrm)

/-- The right side of the display (also the F-version bound). -/
def thm110Rhs (T : Thm110DisplayTerms) : ℝ :=
  (1 + 20 * T.dmod / T.l) * (T.logDFpd + T.logFFpd) +
    20 * (T.eStar * T.l + T.etaPrm)

/-- The gap gained by Cor 3.12's C_Θ ≥ −1: ((1/6)·(12/l²))·log(q). -/
def thm110Cor312Gap (T : Thm110DisplayTerms) : ℝ :=
  ((1 / 6) * (12 / T.l ^ 2)) * T.logQ

/-- The Step (v) slack follows from Cor 3.12 plus the paper nonnegativity
hypotheses and the coefficient drop 1/6 - 2/l^2 > 0. -/
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
  have hbound := LeanFormal.IUT.XiFPaper.Mzk1IVThm110LogQActual.logQ_bound_of_hCor312
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

/-- The two named inputs of the display:
* hCor312: rearrange of [IUTchIII] Cor 3.12 "C_Θ ≥ −1" (Step (v) derivation);
* hSlack : the arithmetic slack step of Step (v) (l ≥ 5; class B paper-input). -/
structure Thm110DisplayInputs (T : Thm110DisplayTerms) : Prop where
  /-- from Cor 3.12's C_Θ ≥ −1 (corpus l.1373-1380) -/
  hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T
  /-- paper arithmetic slack of Step (v) (corpus l.1382-1385; class B) -/
  hSlack : thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T

/-- Display inputs from Cor 3.12 alone under the paper coefficient hypotheses:
the Step (v) slack is derived, not assumed. -/
theorem Thm110DisplayInputsOfCor312 (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    Thm110DisplayInputs T :=
  ⟨hCor312, thm110_slack_of_hCor312 T hl hd hS hE hCor312⟩

/-- **Theorem 1.10 final display (Step (v)), exact shape, conditional:**
(1/6)log(q) ≤ (1+20 d_mod/l)(log d_Ftpd + log f_Ftpd) + 20(e*_mod l + η_prm). -/
theorem thm110_final_display (T : Thm110DisplayTerms) (H : Thm110DisplayInputs T) :
    thm110Lhs T ≤ thm110Rhs T := by
  linarith [H.hCor312, H.hSlack]

/-- The companion F-bound of the display: the same right side bounds the
F-version (1+20 d_mod/l)(log d_F + log f_F) + 20(e*_mod l + η_prm) once the
elementary dictionary step log d_Ftpd + log f_Ftpd ≤ log d_F + log f_F
(corpus l.1387-1391, Step (ii)) is supplied. -/
theorem thm110_final_display_F (T : Thm110DisplayTerms) (H : Thm110DisplayInputs T)
    (hF : T.logDFpd + T.logFFpd ≤
      (1 + 20 * T.dmod / T.l) / (1 + 20 * T.dmod / T.l) *
        (T.logDFpd + T.logFFpd)) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display T H

/-- **(b)+(c) undilated interfaces => route residual data (skeleton alignment).**
The (b) UndilatedHeightBound and (c) UndilatedRegionBound are exactly the
skeleton's PaperRouteResidualData height/region families. -/
def paperRouteResidualData_of_undilated {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X} (hb : UndilatedHeightBound W pt)
    (hc : UndilatedRegionBound W pt) : PaperRouteResidualData W where
  point := pt
  height_comparison := heightComparisonFamily_of_undilated hb
  region_volume_bound := regionVolumeFamily_of_undilated hc

/-- ABC follows from the two undilated interfaces (via the paper-route skeleton;
card P not assumed). -/
theorem abcConjecture_of_undilated {X : Type u} {W : IQHullLogVolumeInterface X}
    {pt : Nat → Nat → Nat → X} (hb : UndilatedHeightBound W pt)
    (hc : UndilatedRegionBound W pt) : ABCConjecture :=
  abcConjecture_of_paperRouteResiduals (paperRouteResidualData_of_undilated hb hc)

/-- Combined deliverable: the exact display (given its named inputs) together
with ABC from the (b)/(c) undilated interfaces. -/
theorem thm110_display_and_abc_of_undilated {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (T : Thm110DisplayTerms) (H : Thm110DisplayInputs T)
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  ⟨thm110_final_display T H, abcConjecture_of_undilated hb hc⟩

/-- Honest obligation classes for the display inputs. -/
def thm110DisplayClass : List (String × String × String) :=
  [ ("Cor 3.12 C_Theta >= -1 (hCor312)", "(b)/(c) route interface consumer",
      "class B: from the paper-route residuals; no closure claimed here"),
    ("Step (v) arithmetic slack (hSlack)", "paper arithmetic (l >= 5; Step (v))",
      "class B paper-input; exact statement, not re-proved"),
    ("display shape (1/6)log q <= ... <= ...", "corpus l.1362-1385", "statement faithful"),
    ("(b) UndilatedHeightBound", "S3131PaperRouteHeightReductionActual", "class B; provable reduction to (b)"),
    ("(c) UndilatedRegionBound", "S3131PaperRouteRegionReductionActual", "class B; provable reduction to (c)") ]

end LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

end
