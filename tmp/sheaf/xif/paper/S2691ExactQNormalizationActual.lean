import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact q-normalization for IUT IV, Theorem 1.10 (Corollary 3.12 |log q|)

Source (read-only):
* IUT IV, Theorem 1.10, p. 23, and Step (viii) of its proof, pp. 30-31, in
  tmp/external/promachina-iut-lean-latest/docs/papers/mochizuki-iut-iv.pdf .
* Markdown OCR: docs/iut-iv-log-volume-computations-and-set-theoretic-foundations.md,
  lines 1297-1323.  The markdown OCR of the CTheta display is corrupted; see
  the section "OCR mismatch" at the end of this file.  The definitions below follow
  the printed paper, which is also consistent with the estimates used in its proof.

## Normalization

For the prime label l >= 5, the quantity |log(q)| in R_{>0} of
[IUTchIII], Corollary 3.12, is

  |log q| = (1/(2l)) * log(q),   equivalently   log(q) = (2l) * |log q|,

where the paper's log(q) = deg(q^F_ADiv) in R_{>=0} (IUT IV p. 23).  Here
log(q) is an explicit real parameter; no degree object or q-pilot object is
constructed or assumed.

## CTheta (printed, IUT IV Theorem 1.10, p. 23)

  CTheta = ((l+1)/4) * |log q| * (
             (1 + 12*dmod/l) * (log dF_tpd + log fF_tpd)
             + 10 * (eStar_mod*l + etaPrm)
             - (1/6) * (1 - 12/l^2) * log(q)
           ) - 1

and CTheta >= -1, together with log q > 0, l >= 7, dmod >= 1, gives

  (1/6) * log(q) <= (1 + 20*dmod/l) * (log dF_tpd + log fF_tpd)
                     + 20 * (eStar_mod*l + etaPrm).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

open LeanFormal.IUT

/-! ## 1. The normalization |log q| = log(q)/(2l) -/

/-- The factor 1/(2l) relating the paper's log(q) to the |log(q)| of
[IUTchIII], Corollary 3.12. -/
def qNormFactor (l : PrimeGeFive) : Real := (1 : Real) / (2 * (l.value : Real))

/-- The Corollary 3.12 absolute log of q, normalized as in IUT IV Theorem 1.10:
|log q| = (1/(2l)) * log(q).  The input logQ is the paper's log(q). -/
def paperQAbsLog (l : PrimeGeFive) (logQ : Real) : Real := qNormFactor l * logQ

theorem qNormFactor_eq (l : PrimeGeFive) :
    qNormFactor l = (1 : Real) / (2 * (l.value : Real)) := rfl

theorem qNormFactor_pos (l : PrimeGeFive) : 0 < qNormFactor l := by
  unfold qNormFactor
  have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have h2 : (0 : Real) < 2 * (l.value : Real) := by linarith
  exact one_div_pos.mpr h2

/-- Definitional form of the normalization. -/
theorem paperQAbsLog_eq (l : PrimeGeFive) (logQ : Real) :
    paperQAbsLog l logQ = (1 / (2 * (l.value : Real))) * logQ := rfl

/-- The inverse normalization: log(q) = (2l) * |log q|. -/
theorem logQ_eq_two_l_mul_paperQAbsLog (l : PrimeGeFive) (logQ : Real)
    (hl : l.value ≠ 0) :
    logQ = (2 * (l.value : Real)) * paperQAbsLog l logQ := by
  have hlR : (l.value : Real) ≠ 0 := by exact_mod_cast hl
  have h2 : (2 * (l.value : Real)) ≠ 0 := mul_ne_zero two_ne_zero hlR
  unfold paperQAbsLog qNormFactor
  field_simp [h2]

theorem paperQAbsLog_pos (l : PrimeGeFive) {logQ : Real} (h : 0 < logQ) :
    0 < paperQAbsLog l logQ := by
  unfold paperQAbsLog
  exact mul_pos (qNormFactor_pos l) h

/-- With log(q) >= 0, the normalized quantity is literally |log q|/(2l). -/
theorem paperQAbsLog_eq_abs_div (l : PrimeGeFive) {logQ : Real} (h : 0 ≤ logQ) :
    paperQAbsLog l logQ = |logQ| / (2 * (l.value : Real)) := by
  unfold paperQAbsLog qNormFactor
  rw [abs_of_nonneg h]
  ring

/-- With log(q) >= 0, (2l) * paperQAbsLog = |log q|. -/
theorem two_l_mul_paperQAbsLog_eq_abs (l : PrimeGeFive) {logQ : Real}
    (h : 0 ≤ logQ) :
    (2 * (l.value : Real)) * paperQAbsLog l logQ = |logQ| := by
  rw [paperQAbsLog_eq_abs_div l h]
  have hlR : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  have h2 : (2 * (l.value : Real)) ≠ 0 := mul_ne_zero two_ne_zero hlR
  field_simp [h2, hlR]

/-! ## 2. The paper's CTheta (IUT IV, Theorem 1.10, p. 23) -/

/-- The bracketed factor { ... } of the printed CTheta. -/
def cThetaBracket (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) : Real :=
  (1 + 12 * dmod / (l.value : Real)) * (Real.log dFpd + Real.log fFpd) +
    10 * (eStar * (l.value : Real) + etaPrm) -
    (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ

/-- IUT IV, Theorem 1.10: the constant CTheta.  Here dFpd and fFpd are the
positive real numbers whose logarithms are log(dF_tpd) and log(fF_tpd),
logQ = log(q), dmod = d_mod, eStar = e*_mod, etaPrm = eta_prm. -/
def CTheta (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) : Real :=
  ((l.value : Real) + 1) / 4 * paperQAbsLog l logQ *
      cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm -
    1

theorem CTheta_def_eq (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    CTheta l logQ dmod dFpd fFpd eStar etaPrm =
      (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ) *
          cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm - 1 := rfl

theorem cThetaFactor_pos (l : PrimeGeFive) {logQ : Real} (h : 0 < logQ) :
    0 < ((l.value : Real) + 1) / 4 * paperQAbsLog l logQ := by
  have hl : (0 : Real) ≤ (l.value : Real) := by exact_mod_cast Nat.zero_le l.value
  have h1 : (0 : Real) < ((l.value : Real) + 1) / 4 := by linarith
  exact mul_pos h1 (paperQAbsLog_pos l h)

/-- Exact algebraic content of CTheta >= -1 for the printed formula: since
((l+1)/4)|log q| = ((l+1)/(8l)) log(q) > 0, the inequality is equivalent to
(1/6)(1 - 12/l^2) log(q) <= (1 + 12 dmod/l)(log dF_tpd + log fF_tpd)
 + 10(eStar*l + etaPrm). -/
theorem CTheta_ge_neg_one_iff (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm ↔
      (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ ≤
        (1 + 12 * dmod / (l.value : Real)) * (Real.log dFpd + Real.log fFpd) +
          10 * (eStar * (l.value : Real) + etaPrm) := by
  have hfac := cThetaFactor_pos l hlogQ
  have hdef := CTheta_def_eq l logQ dmod dFpd fFpd eStar etaPrm
  constructor
  · intro h
    rw [hdef] at h
    have h0 : 0 ≤ (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ) *
        cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm := by linarith
    have hb : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm := by
      by_contra hneg
      rw [not_le] at hneg
      have hlt : (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ) *
          cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm < 0 :=
        mul_neg_of_pos_of_neg hfac hneg
      linarith
    unfold cThetaBracket at hb
    linarith
  · intro hb
    have hb' : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm := by
      unfold cThetaBracket
      linarith
    rw [hdef]
    have h0 : 0 ≤ (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ) *
        cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm :=
      mul_nonneg (le_of_lt hfac) hb'
    linarith

/-! ## 3. The estimates used at the end of the proof (IUT IV p. 31) -/

/-- 1 - 12/l^2 > 0 for l >= 7. -/
theorem one_sub_twelve_div_sq_pos (l : PrimeGeFive) (hl7 : 7 ≤ l.value) :
    0 < 1 - 12 / ((l.value : Real)) ^ 2 := by
  have hlR7 : (7 : Real) ≤ (l.value : Real) := by exact_mod_cast hl7
  have hlRpos : (0 : Real) < (l.value : Real) := by linarith
  have h12 : (12 : Real) < ((l.value : Real)) ^ 2 := by
    nlinarith [sq_nonneg ((l.value : Real) - 7)]
  have hdiv : 12 / ((l.value : Real)) ^ 2 < 1 := by
    rw [div_lt_one (pow_pos hlRpos 2)]
    exact h12
  linarith

/-- (1 - 12/l^2)^{-1} <= 2 for l >= 7 (printed estimate). -/
theorem inv_one_sub_twelve_div_sq_le_two (l : PrimeGeFive) (hl7 : 7 ≤ l.value) :
    (1 - 12 / ((l.value : Real)) ^ 2)⁻¹ ≤ 2 := by
  have hlR7 : (7 : Real) ≤ (l.value : Real) := by exact_mod_cast hl7
  have hc := one_sub_twelve_div_sq_pos l hl7
  rw [inv_le_iff_one_le_mul₀ hc]
  have h24 : (24 : Real) ≤ ((l.value : Real)) ^ 2 := by
    nlinarith [sq_nonneg ((l.value : Real) - 7)]
  have hpos : (0 : Real) < ((l.value : Real)) ^ 2 := by linarith
  have h24div : 24 / ((l.value : Real)) ^ 2 ≤ 1 := (div_le_one hpos).mpr h24
  have hEq : 2 * (1 - 12 / ((l.value : Real)) ^ 2) =
      2 - 24 / ((l.value : Real)) ^ 2 := by ring
  rw [hEq]
  linarith

/-- Printed estimate (IUT IV p. 31):
(1 - 12/l^2)^{-1} * (1 + 12*dmod/l) <= 1 + 20*dmod/l for l >= 7, dmod >= 1. -/
theorem inv_mul_one_add_twelve_le (l : PrimeGeFive) (dmod : Real)
    (hl7 : 7 ≤ l.value) (hd : 1 ≤ dmod) :
    (1 - 12 / ((l.value : Real)) ^ 2)⁻¹ * (1 + 12 * dmod / (l.value : Real)) ≤
      1 + 20 * dmod / (l.value : Real) := by
  have hlR7 : (7 : Real) ≤ (l.value : Real) := by exact_mod_cast hl7
  have hlRpos : (0 : Real) < (l.value : Real) := by linarith
  have hlRne : (l.value : Real) ≠ 0 := ne_of_gt hlRpos
  have hc := one_sub_twelve_div_sq_pos l hl7
  rw [inv_mul_le_iff₀ hc]
  have hkey : (0 : Real) ≤
      8 * dmod * ((l.value : Real)) ^ 2 - 12 * (l.value : Real) - 240 * dmod := by
    have h1 : (0 : Real) ≤ (dmod - 1) * (8 * ((l.value : Real)) ^ 2 - 240) := by
      apply mul_nonneg (by linarith)
      nlinarith [sq_nonneg ((l.value : Real) - 7)]
    have h2 : (0 : Real) ≤
        8 * ((l.value : Real)) ^ 2 - 12 * (l.value : Real) - 240 := by
      nlinarith [sq_nonneg ((l.value : Real) - 7)]
    nlinarith [h1, h2]
  have hid : (1 - 12 / ((l.value : Real)) ^ 2) * (1 + 20 * dmod / (l.value : Real)) -
      (1 + 12 * dmod / (l.value : Real)) =
      (8 * dmod * ((l.value : Real)) ^ 2 - 12 * (l.value : Real) - 240 * dmod) /
        ((l.value : Real)) ^ 3 := by
    field_simp [hlRne]
    ring
  have h3 : (0 : Real) < ((l.value : Real)) ^ 3 := pow_pos hlRpos 3
  have hquot : (0 : Real) ≤
      (8 * dmod * ((l.value : Real)) ^ 2 - 12 * (l.value : Real) - 240 * dmod) /
        ((l.value : Real)) ^ 3 := div_nonneg hkey (le_of_lt h3)
  linarith

/-! ## 4. The displayed log bound of IUT IV, Theorem 1.10 -/

/-- **Main bound.**  For the printed CTheta, CTheta >= -1 and log(q) > 0
imply (1/6) log(q) <= (1 + 20*dmod/l)(log dF_tpd + log fF_tpd) + 20(eStar*l + etaPrm)
provided l >= 7, dmod >= 1, and the two nonnegativities
0 <= log dF_tpd + log fF_tpd, 0 <= eStar*l + etaPrm.  These hold in the paper
because log(dF_tpd), log(fF_tpd) >= 0, eStar_mod > 0, and etaPrm > 0. -/
theorem CTheta_ge_neg_one_implies_log_bound
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ) (hl7 : 7 ≤ l.value) (hd : 1 ≤ dmod)
    (hX : 0 ≤ Real.log dFpd + Real.log fFpd)
    (hE : 0 ≤ eStar * (l.value : Real) + etaPrm)
    (hC : -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm) :
    (1 / 6) * logQ ≤
      (1 + 20 * dmod / (l.value : Real)) * (Real.log dFpd + Real.log fFpd) +
        20 * (eStar * (l.value : Real) + etaPrm) := by
  let lR : Real := (l.value : Real)
  let X : Real := Real.log dFpd + Real.log fFpd
  let E : Real := eStar * (l.value : Real) + etaPrm
  let c : Real := 1 - 12 / ((l.value : Real)) ^ 2
  have hlR7 : (7 : Real) ≤ lR := by dsimp [lR]; exact_mod_cast hl7
  have hlRpos : (0 : Real) < lR := by linarith
  have hc : 0 < c := by
    dsimp [c]
    exact one_sub_twelve_div_sq_pos l hl7
  have hmain : (1 / 6) * c * logQ ≤ (1 + 12 * dmod / lR) * X + 10 * E := by
    have h := (CTheta_ge_neg_one_iff l logQ dmod dFpd fFpd eStar etaPrm hlogQ).mp hC
    simpa [c, X, E, lR] using h
  have hc_inv : c⁻¹ ≤ 2 := by
    dsimp [c]
    exact inv_one_sub_twelve_div_sq_le_two l hl7
  have hcoef : c⁻¹ * (1 + 12 * dmod / lR) ≤ 1 + 20 * dmod / lR := by
    dsimp [c, lR]
    exact inv_mul_one_add_twelve_le l dmod hl7 hd
  have hstep : (1 / 6) * logQ ≤ c⁻¹ * ((1 + 12 * dmod / lR) * X + 10 * E) := by
    calc
      (1 / 6) * logQ = c⁻¹ * ((1 / 6) * c * logQ) := by
        field_simp [ne_of_gt hc]
      _ ≤ c⁻¹ * ((1 + 12 * dmod / lR) * X + 10 * E) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt (inv_pos.mpr hc))
  have hterm1 : c⁻¹ * ((1 + 12 * dmod / lR) * X) ≤ (1 + 20 * dmod / lR) * X := by
    calc
      c⁻¹ * ((1 + 12 * dmod / lR) * X) = (c⁻¹ * (1 + 12 * dmod / lR)) * X := by ring
      _ ≤ (1 + 20 * dmod / lR) * X := mul_le_mul_of_nonneg_right hcoef hX
  have hterm2 : c⁻¹ * (10 * E) ≤ 20 * E := by
    have h1 : c⁻¹ * E ≤ 2 * E := mul_le_mul_of_nonneg_right hc_inv hE
    calc
      c⁻¹ * (10 * E) = 10 * (c⁻¹ * E) := by ring
      _ ≤ 10 * (2 * E) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 20 * E := by ring
  have hfinal : (1 / 6) * logQ ≤ (1 + 20 * dmod / lR) * X + 20 * E := by
    have hsplit : c⁻¹ * ((1 + 12 * dmod / lR) * X + 10 * E) =
        c⁻¹ * ((1 + 12 * dmod / lR) * X) + c⁻¹ * (10 * E) := by ring
    rw [hsplit] at hstep
    linarith
  simpa [X, E, lR] using hfinal

/-- Source-form of the main bound, with the paper's own sign conditions
log(dF_tpd), log(fF_tpd) >= 0 (written 1 <= dFpd, 1 <= fFpd) and
eStar, etaPrm >= 0. -/
theorem CTheta_ge_neg_one_implies_log_bound_source
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ) (hl7 : 7 ≤ l.value) (hd : 1 ≤ dmod)
    (hdF : 1 ≤ dFpd) (hfF : 1 ≤ fFpd)
    (heStar : 0 ≤ eStar) (hetaPrm : 0 ≤ etaPrm)
    (hC : -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm) :
    (1 / 6) * logQ ≤
      (1 + 20 * dmod / (l.value : Real)) * (Real.log dFpd + Real.log fFpd) +
        20 * (eStar * (l.value : Real) + etaPrm) := by
  refine CTheta_ge_neg_one_implies_log_bound l logQ dmod dFpd fFpd eStar etaPrm
    hlogQ hl7 hd ?_ ?_ hC
  · have h1 : (0 : Real) ≤ Real.log dFpd := Real.log_nonneg hdF
    have h2 : (0 : Real) ≤ Real.log fFpd := Real.log_nonneg hfF
    linarith
  · have hl : (0 : Real) ≤ (l.value : Real) := by exact_mod_cast Nat.zero_le l.value
    nlinarith

/-- Second display of IUT IV, Theorem 1.10: replacing dF_tpd, fF_tpd by
dF, fF (legitimate when the logarithms only increase). -/
theorem CTheta_ge_neg_one_implies_log_bound_dF
    (l : PrimeGeFive) (logQ dmod dFpd fFpd dF fF eStar etaPrm : Real)
    (hlogQ : 0 < logQ) (hl7 : 7 ≤ l.value) (hd : 1 ≤ dmod)
    (hX : 0 ≤ Real.log dFpd + Real.log fFpd)
    (hE : 0 ≤ eStar * (l.value : Real) + etaPrm)
    (hle : Real.log dFpd + Real.log fFpd ≤ Real.log dF + Real.log fF)
    (hC : -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm) :
    (1 / 6) * logQ ≤
      (1 + 20 * dmod / (l.value : Real)) * (Real.log dF + Real.log fF) +
        20 * (eStar * (l.value : Real) + etaPrm) := by
  have h1 := CTheta_ge_neg_one_implies_log_bound l logQ dmod dFpd fFpd eStar etaPrm
    hlogQ hl7 hd hX hE hC
  have hlRpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have hcoef : (0 : Real) ≤ 1 + 20 * dmod / (l.value : Real) := by
    have : (0 : Real) ≤ 20 * dmod / (l.value : Real) :=
      div_nonneg (by linarith) (le_of_lt hlRpos)
    linarith
  have hmono : (1 + 20 * dmod / (l.value : Real)) *
        (Real.log dFpd + Real.log fFpd) ≤
      (1 + 20 * dmod / (l.value : Real)) * (Real.log dF + Real.log fF) :=
    mul_le_mul_of_nonneg_left hle hcoef
  linarith

/-! ## 5. Relation to the singleton normalization of S2679PaperHcompNormalizationActual

In S2679PaperHcompNormalizationActual the singleton q = 1/5 datum has
sourceBadQAbsLog = order_C3 * log 5, and the raw hcomp uses this quantity
directly as the absolute log of q.  In the paper's Corollary 3.12 normalization
the same log(q) = order_C3 * log 5 gives paperQAbsLog = order_C3*log5/(2l),
i.e. the old quantity divided by 2l; at l = 5 it is divided by 10.  The file
S2679PaperHcompNormalizationActual is not modified (and not imported). -/

/-- The prime label 5.  (For actual IUT data, [IUTchI], Definition 3.1, (c),
gives l != 5; the record PrimeGeFive allows 5, and this value is used only
to display the normalization at l = 5.) -/
def l5 : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

theorem qNormFactor_l5 : qNormFactor l5 = (1 : Real) / 10 := by
  unfold qNormFactor l5
  norm_num

theorem paperQAbsLog_l5 (logQ : Real) : paperQAbsLog l5 logQ = logQ / 10 := by
  unfold paperQAbsLog qNormFactor l5
  norm_num
  ring

/-- Conditional relation to the S2679PaperHcompNormalizationActual singleton
value: if the paper's log(q) is the old sourceBadQAbsLog = order_C3 * log 5,
then the Corollary 3.12 normalized quantity is that value divided by 2l. -/
theorem paperQAbsLog_singleton_normalization (l : PrimeGeFive) (orderC3 : Nat) :
    paperQAbsLog l ((orderC3 : Real) * Real.log 5) =
      ((orderC3 : Real) * Real.log 5) / (2 * (l.value : Real)) := by
  unfold paperQAbsLog qNormFactor
  ring

theorem paperQAbsLog_singleton_normalization_l5 (orderC3 : Nat) :
    paperQAbsLog l5 ((orderC3 : Real) * Real.log 5) =
      ((orderC3 : Real) * Real.log 5) / 10 := by
  rw [paperQAbsLog_singleton_normalization]
  unfold l5
  norm_num

/-! ## 6. OCR mismatch: the markdown transcription is not the printed formula

The markdown OCR (lines 1303-1313 of
docs/iut-iv-log-volume-computations-and-set-theoretic-foundations.md) and the
task transcription put +10(...) and -(1/6)(1-12/l^2) log(q) outside the
multiplication by ((l+1)/4)|log q|, and replace the printed coefficients 12 and
20 by 36 and 80.  The printed PDF (p. 23) reads

  CTheta = ((l+1)/4) * |log q| * (
             (1 + 12*dmod/l)(log dF_tpd + log fF_tpd) + 10(e*_mod*l + etaPrm)
             - (1/6)(1 - 12/l^2)log q
           ) - 1

and the proof (p. 31) uses exactly the printed estimates
(1-12/l^2)^{-1} <= 2 and (1-12/l^2)^{-1}(1+12*dmod/l) <= 1+20*dmod/l
for l >= 7, dmod >= 1.  The OCR formula is refutable as a source for the
displayed bound: for it, CTheta >= -1 leaves an extra factor |log q| on the
log dF_tpd + log fF_tpd term.  We record both the exact algebra of the OCR
formula and a concrete counterexample to the transcribed implication. -/

/-- Literal transcription of CTheta from the OCR markdown (and from the task
formulation).  This is **not** the printed formula; see the section docstring. -/
def ocrCTheta (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) : Real :=
  ((l.value : Real) + 1) / 4 * paperQAbsLog l logQ *
      (1 + 36 * dmod / (l.value : Real)) * (Real.log dFpd + Real.log fFpd) +
    10 * (eStar * (l.value : Real) + etaPrm) -
    (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ - 1

/-- Exact algebra of the OCR formula: ocrCTheta >= -1 is equivalent to the
inequality below, which differs from the printed conclusion by the extra factor
paperQAbsLog l logQ = log(q)/(2l) multiplying
(1 + 36*dmod/l)(log dF_tpd + log fF_tpd). -/
theorem ocrCTheta_ge_neg_one_iff (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    -1 ≤ ocrCTheta l logQ dmod dFpd fFpd eStar etaPrm ↔
      (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ ≤
        (((l.value : Real) + 1) / 4 * paperQAbsLog l logQ *
            (1 + 36 * dmod / (l.value : Real))) * (Real.log dFpd + Real.log fFpd) +
          10 * (eStar * (l.value : Real) + etaPrm) := by
  unfold ocrCTheta
  constructor <;> intro h <;> linarith

/-- The prime label 7 used for the concrete disproof. -/
def l7 : PrimeGeFive where
  value := 7
  prime := by norm_num
  ge_five := by norm_num

theorem ocrCTheta_l7_value :
    ocrCTheta l7 100 0 (Real.exp 1) 1 0 0 = 103 / 147 := by
  norm_num [ocrCTheta, paperQAbsLog, qNormFactor, l7, Real.log_exp, Real.log_one]

/-- **OCR mismatch is not cosmetic.**  With l = 7, log q = 100, dmod = 0,
dF_tpd = exp 1, fF_tpd = 1, eStar = etaPrm = 0, the OCR-transcribed
CTheta satisfies CTheta >= -1 (it equals 103/147), but the transcribed
conclusion (1/6)log q <= (1+80 dmod/l)(...) + 20(...) is false (it would read
50/3 <= 1). -/
theorem ocrCTheta_counterexample :
    -1 ≤ ocrCTheta l7 100 0 (Real.exp 1) 1 0 0 ∧
      ¬ ((1 / 6 : Real) * 100 ≤
        (1 + 80 * 0 / (7 : Real)) * (Real.log (Real.exp 1) + Real.log 1) +
          20 * (0 * (7 : Real) + 0)) := by
  constructor
  · rw [ocrCTheta_l7_value]
    norm_num
  · norm_num [Real.log_exp, Real.log_one]

/-! ## Checks and axiom status -/

#check qNormFactor
#check paperQAbsLog
#check CTheta
#check CTheta_ge_neg_one_iff
#check CTheta_ge_neg_one_implies_log_bound
#check paperQAbsLog_l5
#check paperQAbsLog_singleton_normalization_l5
#check ocrCTheta_counterexample

#print axioms CTheta_ge_neg_one_iff
#print axioms CTheta_ge_neg_one_implies_log_bound
#print axioms CTheta_ge_neg_one_implies_log_bound_source
#print axioms CTheta_ge_neg_one_implies_log_bound_dF
#print axioms paperQAbsLog_eq
#print axioms logQ_eq_two_l_mul_paperQAbsLog
#print axioms paperQAbsLog_l5
#print axioms paperQAbsLog_singleton_normalization_l5
#print axioms ocrCTheta_counterexample

end LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
end
