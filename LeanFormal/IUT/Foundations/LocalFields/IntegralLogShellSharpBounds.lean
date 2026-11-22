import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverseSharpRadius

/-!
# Sharp bounds for the unscaled local unit-log lattice

This file isolates the local-field estimates used by IUT IV Proposition 1.2(i).
The carrier is the **unscaled** image `log_p(R_i^×)`, represented by
`unitLogLattice` from `UnscaledUnitLogLattice`.  This is not the scaled
`integralLogShellLattice` of IUT III; statements about the scaled shell are
recorded only as auxiliary corollaries and are shifted by `s = 1` for odd `p`
and `s = 2` for `p = 2`.

The paper's exponents are

* `a_i = (1 / e_i) * ceil (e_i / (p - 2))` for `p > 2`, and `a_i = 2` for
  `p = 2`;
* `b_i = floor (log (p * e_i / (p - 1)) / log p) - 1 / e_i`.

They are defined below as `logShellPaperAExponent` and
`logShellPaperBExponent`.

## What is proved here

All statements use the unscaled carrier `unitLogLattice`, whose carrier is
`Set.range unitLog` (the actual image `log_p(R_i^×)`).

For every prime `p` and every actual ramification exponent
`e = logShellRamificationExponent K p`, the paper's exponents

* `a_i = (1 / e) * ceil (e / (p - 2))` for `p > 2`, and `a_i = 2` for `p = 2`;
* `b_i = floor (log (p * e / (p - 1)) / log p) - 1 / e`

satisfy both inclusions of IUT IV Proposition 1.2(i):

* `padicFractionalLattice a_i <= unitLogLattice`
  (`padicFractionalLattice_paperA_le_unitLogLattice`);
* `unitLogLattice <= padicFractionalLattice (-b_i)`
  (`unitLogLattice_le_padicFractionalLattice_neg_paperB`).

The lower inclusion uses the sharp inverse radius `r < p^(-1/(p-1))` proved
in `LogarithmLocalInverseSharpRadius`.  The upper inclusion uses the
termwise estimate `v_p(n) - n/e <= b_i` and the residue-cardinality
reduction `u^(q-1)` to a principal unit.

Element forms are provided: for a uniformizer `π`,
`logShellPaperAlphaElement π p e` has norm `p^(-a_i)` (normalized order
`a_i`) and satisfies `α_i R_i ⊆ log(R_i^×)`; `logShellPaperBetaElement π p e`
has norm `p^(b_i)` (normalized order `-b_i`) and satisfies
`log(R_i^×) ⊆ β_i R_i`.

The coefficient estimates feeding the log-volume computation are
`logShellPaperAExponent_add_logShellPaperBExponent_eq_zero_of_small`,
`logShellPaperExponent_sum_mul_log_le_three_add_log`,
`logShellPaperAExponent_sub_inv_mul_log_le_two`,
`logShellPaperBExponent_add_inv_mul_log_le_log_two_mul`, and
`log_two_mul_le_one_add_log`.

## Scope

This file proves the local, unscaled statement of Proposition 1.2(i).  It
does not assemble the multi-place tensor `I_tensor` or the global Step(v)
comparison; those are carried by the separate tensor-packet files.  The
finite-congruence integer bound `logShellCongruenceUpperExponent` remains
below as an auxiliary statement: it is not the paper's `b_i` and is not
used as Proposition 1.2(i).
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped Pointwise LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

section PaperExponents

/-- The lower exponent of IUT IV Proposition 1.2(i):
`(1 / e) * ceil (e / (p - 2))` for `p > 2`, and `2` for `p = 2`. -/
def logShellPaperAExponent (p e : ℕ) : ℝ :=
  if p = 2 then 2 else
    (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ)

/-- The upper exponent of IUT IV Proposition 1.2(i):
`floor (log (p * e / (p - 1)) / log p) - 1 / e`. -/
def logShellPaperBExponent (p e : ℕ) : ℝ :=
  (Nat.floor (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
    Real.log (p : ℝ)) : ℝ) - 1 / (e : ℝ)

end PaperExponents

private theorem logShellPaperB_floor_pow_le {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ((p : ℝ) ^ Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) : ℝ) ≤
      (p : ℝ) * e / ((p : ℝ) - 1) := by
  set B := Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) with hB
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have harg1 : (1 : ℝ) ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
    nlinarith
  have hargpos : 0 < (p : ℝ) * e / ((p : ℝ) - 1) := lt_of_lt_of_le zero_lt_one harg1
  have hBle : (B : ℝ) ≤ Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg harg1) hplog.le)
  have hmul : (B : ℝ) * Real.log (p : ℝ) ≤ Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := by
    rw [le_div_iff₀ hplog] at hBle
    linarith
  have hexp := Real.exp_le_exp.mpr hmul
  rw [Real.exp_nat_mul, Real.exp_log (by linarith : (0 : ℝ) < p), Real.exp_log hargpos] at hexp
  exact hexp

private theorem logShellPaperB_floor_pow_lt_succ {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (p : ℝ) * e / ((p : ℝ) - 1) <
      (p : ℝ) ^ (Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) + 1) := by
  set B := Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) with hB
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have harg1 : (1 : ℝ) ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
    nlinarith
  have hargpos : 0 < (p : ℝ) * e / ((p : ℝ) - 1) := lt_of_lt_of_le zero_lt_one harg1
  have hBlt : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) < (B : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hmul : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) < ((B : ℝ) + 1) * Real.log (p : ℝ) := by
    rw [div_lt_iff₀ hplog] at hBlt
    linarith
  have hexp := Real.exp_lt_exp.mpr hmul
  rw [show ((B : ℝ) + 1) = ((B + 1 : ℕ) : ℝ) by norm_cast,
    Real.exp_nat_mul, Real.exp_log (by linarith : (0 : ℝ) < p)] at hexp
  simpa [Real.exp_log hargpos] using hexp

/-- Termwise arithmetic estimate behind the paper's `b_i`: for every positive `n`,
`v_p(n) - n/e` is at most `floor(log_p (p*e/(p-1))) - 1/e`. -/
theorem padicValNat_sub_div_le_logShellPaperBExponent {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    {n : ℕ} (hn : 1 ≤ n) :
    (padicValNat p n : ℝ) - (n : ℝ) / (e : ℝ) ≤ logShellPaperBExponent p e := by
  set B := Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) with hB
  have hBle : ((p : ℝ) ^ B : ℝ) ≤ (p : ℝ) * e / ((p : ℝ) - 1) :=
    logShellPaperB_floor_pow_le hp he
  have hBlt : (p : ℝ) * e / ((p : ℝ) - 1) < (p : ℝ) ^ (B + 1) :=
    logShellPaperB_floor_pow_lt_succ hp he
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let k := padicValNat p n
  have hdvd : p ^ k ∣ n := pow_padicValNat_dvd
  have hpk_le : p ^ k ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hpk_leR : ((p : ℝ) ^ k) ≤ n := by exact_mod_cast hpk_le
  have hred : (k : ℝ) - (n : ℝ) / e ≤ (k : ℝ) - ((p : ℝ) ^ k) / e := by
    have : ((p : ℝ) ^ k) / e ≤ (n : ℝ) / e := div_le_div_of_nonneg_right hpk_leR hepos.le
    linarith
  have hmain : (k : ℝ) - ((p : ℝ) ^ k) / e ≤ (B : ℝ) - 1 / e := by
    by_cases hkB : k ≤ B
    · have hkBnonneg : (k : ℝ) - B ≤ 0 := by
        have hkBR : (k : ℝ) ≤ B := by exact_mod_cast hkB
        linarith
      have hpowe : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ hp1
      have hnonneg : (0 : ℝ) ≤ ((p : ℝ) ^ k - 1) / e :=
        div_nonneg (by linarith) hepos.le
      have : (k : ℝ) - (p : ℝ) ^ k / e ≤ (B : ℝ) - 1 / e := by
        have hEq : (k : ℝ) - (p : ℝ) ^ k / e ≤ (B : ℝ) - 1 / e ↔
            (k : ℝ) - B ≤ ((p : ℝ) ^ k - 1) / e := by
          field_simp [hepos.ne']
          ring_nf
          constructor <;> intro h <;> linarith
        exact hEq.mpr (le_trans hkBnonneg hnonneg)
      exact this
    · have hkB1 : B + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_le hkB)
      have hstep : ∀ j, B + 1 ≤ j →
          ((j + 1 : ℕ) : ℝ) - ((p : ℝ) ^ (j + 1)) / e ≤ (j : ℝ) - ((p : ℝ) ^ j) / e := by
        intro j hj
        have hpj : ((p : ℝ) ^ (B + 1)) ≤ (p : ℝ) ^ j := pow_le_pow_right₀ hp1 hj
        have hpB1gt : (p : ℝ) < ((p : ℝ) ^ (B + 1) * ((p : ℝ) - 1)) / e := by
          have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          have hmul := mul_lt_mul_of_pos_right hBlt (div_pos hpm hepos)
          have heq : (p : ℝ) * e / ((p : ℝ) - 1) * (((p : ℝ) - 1) / e) = (p : ℝ) := by
            field_simp [hepos.ne', hpm.ne']
          rw [heq] at hmul
          simpa [mul_div_assoc] using hmul
        have hbig : (1 : ℝ) ≤ ((p : ℝ) ^ j * ((p : ℝ) - 1)) / e := by
          have hmono : ((p : ℝ) ^ (B + 1) * ((p : ℝ) - 1)) / e ≤
              ((p : ℝ) ^ j * ((p : ℝ) - 1)) / e := by
            apply div_le_div_of_nonneg_right _ hepos.le
            exact mul_le_mul_of_nonneg_right hpj (by linarith)
          linarith
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_cast
        have hrew : ((p : ℝ) ^ j * (p : ℝ) - (p : ℝ) ^ j) / e =
            ((p : ℝ) ^ j * ((p : ℝ) - 1)) / e := by ring
        have hle : (1 : ℝ) ≤ ((p : ℝ) ^ j * (p : ℝ) - (p : ℝ) ^ j) / e := by
          rw [hrew]
          exact hbig
        have hsplit : (j : ℝ) + 1 - (p : ℝ) ^ j * (p : ℝ) / e =
            ((j : ℝ) - (p : ℝ) ^ j / e) +
              (1 - ((p : ℝ) ^ j * (p : ℝ) - (p : ℝ) ^ j) / e) := by
          field_simp [hepos.ne']
          ring
        rw [hcast, pow_succ, hsplit]
        linarith
      have hmono : (k : ℝ) - ((p : ℝ) ^ k) / e ≤
          ((B + 1 : ℕ) : ℝ) - ((p : ℝ) ^ (B + 1)) / e := by
        refine Nat.le_induction (m := B + 1) ?base ?step k hkB1
        · simp
        · intro j hj ih
          have := hstep j hj
          linarith
      have hfinal : ((B + 1 : ℕ) : ℝ) - ((p : ℝ) ^ (B + 1)) / e ≤ (B : ℝ) - 1 / e := by
        have hBcast : ((B + 1 : ℕ) : ℝ) = (B : ℝ) + 1 := by norm_cast
        have hpB1 : (e : ℝ) + 1 ≤ (p : ℝ) ^ (B + 1) := by
          by_cases hcase : (p : ℝ) - 1 ≤ (e : ℝ)
          · have h2 : (e : ℝ) + 1 ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by
              rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
              nlinarith
            linarith [hBlt.le]
          · have hcase' : (e : ℝ) < (p : ℝ) - 1 := not_le.mp hcase
            have hep : e + 1 < p := by
              have : (e : ℝ) + 1 < (p : ℝ) := by linarith
              exact_mod_cast this
            have harg1 : (1 : ℝ) ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by
              rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
              have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
              nlinarith
            have harglt : (p : ℝ) * e / ((p : ℝ) - 1) < (p : ℝ) := by
              rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
              nlinarith
            have hB0 : B = 0 := by
              rw [Nat.floor_eq_zero]
              rw [div_lt_one (Real.log_pos (by linarith : (1 : ℝ) < p))]
              exact Real.log_lt_log (by linarith) harglt
            rw [hB0]
            simpa using (show (e : ℝ) + 1 ≤ (p : ℝ) by exact_mod_cast hep.le)
        rw [hBcast]
        have hdiv : ((e : ℝ) + 1) / e ≤ ((p : ℝ) ^ (B + 1)) / e :=
          div_le_div_of_nonneg_right hpB1 hepos.le
        have he1 : ((e : ℝ) + 1) / e = 1 + 1 / e := by
          field_simp [hepos.ne']
        linarith
      linarith
  dsimp [logShellPaperBExponent]
  rw [← hB]
  change (k : ℝ) - (n : ℝ) / e ≤ (B : ℝ) - 1 / e
  linarith

private theorem logShellPaperAExponent_of_small {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hle : e ≤ p - 2) :
    logShellPaperAExponent p e = 1 / (e : ℝ) := by
  have hpgt : 2 < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hxpos : 0 < (e : ℝ) / ((p : ℝ) - 2) := by
    have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
    have hpgtR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    have hden : 0 < (p : ℝ) - 2 := by linarith
    positivity
  have hxle : (e : ℝ) / ((p : ℝ) - 2) ≤ 1 := by
    have hpgtR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    have hden : 0 < (p : ℝ) - 2 := by linarith
    rw [div_le_one hden]
    have h := (Nat.cast_le (α := ℝ)).mpr hle
    rwa [Nat.cast_sub hp.two_le] at h
  have hceil : Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) = 1 :=
    (Nat.ceil_eq_iff (n := 1) one_ne_zero).mpr ⟨by simpa using hxpos, by simpa using hxle⟩
  simp [logShellPaperAExponent, hp2, hceil]

private theorem logShellPaperBExponent_of_small {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hle : e ≤ p - 2) :
    logShellPaperBExponent p e = -(1 / (e : ℝ)) := by
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    omega
  have hpgt : 2 < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hden : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hargpos : 0 < (p : ℝ) * e / ((p : ℝ) - 1) :=
    div_pos (mul_pos hppos hepos) hden
  have harglt : (p : ℝ) * e / ((p : ℝ) - 1) < (p : ℝ) := by
    rw [div_lt_iff₀ hden]
    have hlt : (e : ℝ) < (p : ℝ) - 1 := by
      have hcast : (e : ℝ) ≤ (p : ℝ) - 2 := by
        have h := (Nat.cast_le (α := ℝ)).mpr hle
        rwa [Nat.cast_sub hp.two_le] at h
      linarith
    nlinarith
  have hquot_lt : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) < 1 := by
    rw [div_lt_one (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < p))]
    exact Real.log_lt_log hargpos harglt
  have hfloor : Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
      Real.log (p : ℝ)) = 0 :=
    Nat.floor_eq_zero.mpr hquot_lt
  simp [logShellPaperBExponent, hfloor, one_div]

/-- In the small-ramification range `e ≤ p - 2`, the paper's exponents satisfy
`a_i + b_i = 0`. -/
theorem logShellPaperAExponent_add_logShellPaperBExponent_eq_zero_of_small
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hle : e ≤ p - 2) :
    logShellPaperAExponent p e + logShellPaperBExponent p e = 0 := by
  rw [logShellPaperAExponent_of_small hp hp2 he hle,
    logShellPaperBExponent_of_small hp he hle]
  ring

private theorem logShellPaperAExponent_le_inv_add {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) :
    logShellPaperAExponent p e ≤ 1 / ((p : ℝ) - 2) + 1 / (e : ℝ) := by
  have hpgt : 2 < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hpgtR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
  have hden : 0 < (p : ℝ) - 2 := by linarith
  have hceil_lt := Nat.ceil_lt_add_one (a := (e : ℝ) / ((p : ℝ) - 2)) (by positivity)
  have hceil_mul : ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) ≤
      (e : ℝ) / ((p : ℝ) - 2) := by linarith
  have hmain : (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) ≤
      1 / ((p : ℝ) - 2) + 1 / (e : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hceil_mul hepos.le
    have heq : (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) =
        ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) / (e : ℝ) + 1 / (e : ℝ) := by
      field_simp [hepos.ne']
      ring
    rw [heq]
    have hdiv' : ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) / (e : ℝ) ≤
        1 / ((p : ℝ) - 2) := by
      calc
        ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) / (e : ℝ) ≤
            ((e : ℝ) / ((p : ℝ) - 2)) / (e : ℝ) := hdiv
        _ = 1 / ((p : ℝ) - 2) := by field_simp [hepos.ne']
    linarith
  simpa [logShellPaperAExponent, hp2] using hmain

private theorem logShellPaperBExponent_le_log_div {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    logShellPaperBExponent p e ≤
      Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) - 1 / (e : ℝ) := by
  have hpgt : 1 < p := hp.one_lt
  have hden : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hpgt
    linarith
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hargpos : 0 < (p : ℝ) * e / ((p : ℝ) - 1) :=
    div_pos (mul_pos hppos hepos) hden
  have hquot_nonneg : 0 ≤ Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by
      rw [le_div_iff₀ hden]
      have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
      nlinarith)) (Real.log_pos (by exact_mod_cast hpgt : (1 : ℝ) < p)).le
  have hfloor : (Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
      Real.log (p : ℝ)) : ℝ) ≤
      Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) :=
    Nat.floor_le hquot_nonneg
  dsimp [logShellPaperBExponent]
  linarith

private theorem log_prime_div_prime_sub_one_le_one {p : ℕ} (hp : p.Prime) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hratio : 0 < (p : ℝ) / ((p : ℝ) - 1) := div_pos (by positivity) hden
  have hlog := Real.log_le_sub_one_of_pos hratio
  have heq : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
    field_simp [hden.ne']
    ring
  rw [heq] at hlog
  have hone : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hden]
    have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  linarith

private theorem log_prime_div_prime_sub_two_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Real.log (p : ℝ) / ((p : ℝ) - 2) ≤ 2 := by
  have hpgt : 2 < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hpgtR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
  have hden : 0 < (p : ℝ) - 2 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by positivity)
  have hle : (p : ℝ) - 1 ≤ 2 * ((p : ℝ) - 2) := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- The paper's first log-volume estimate: `(a_i + b_i) log p ≤ 3 + log e_i`. -/
theorem logShellPaperExponent_sum_mul_log_le_three_add_log
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (logShellPaperAExponent p e + logShellPaperBExponent p e) * Real.log (p : ℝ) ≤
      3 + Real.log (e : ℝ) := by
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hplogpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  by_cases hp2 : p = 2
  · subst p
    have hA : logShellPaperAExponent 2 e = 2 := by simp [logShellPaperAExponent]
    have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)
      norm_num at h
      exact h
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hden : 0 < (2 : ℝ) - 1 := by norm_num
    have harg : (2 : ℝ) * e / ((2 : ℝ) - 1) = (2 : ℝ) * e := by norm_num
    have hquot_nonneg : 0 ≤ Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) /
        Real.log (2 : ℝ) := by
      apply div_nonneg
      · apply Real.log_nonneg
        rw [le_div_iff₀ hden]
        have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
        nlinarith
      · exact hlog2pos.le
    have hfloor : (Nat.floor (Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) /
        Real.log (2 : ℝ)) : ℝ) ≤
        Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) / Real.log (2 : ℝ) :=
      Nat.floor_le hquot_nonneg
    have hfloor' : (Nat.floor (Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) /
        Real.log (2 : ℝ)) : ℝ) ≤ Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ) := by
      simpa [harg] using hfloor
    have hBdecomp : logShellPaperBExponent 2 e + 1 / (e : ℝ) =
        (Nat.floor (Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) /
          Real.log (2 : ℝ)) : ℝ) := by
      dsimp [logShellPaperBExponent]
      ring
    have hBscaled : (logShellPaperBExponent 2 e + 1 / (e : ℝ)) * Real.log (2 : ℝ) ≤
        Real.log ((2 : ℝ) * e) := by
      rw [hBdecomp]
      calc
        (Nat.floor (Real.log ((2 : ℝ) * e / ((2 : ℝ) - 1)) /
            Real.log (2 : ℝ)) : ℝ) * Real.log (2 : ℝ) ≤
            (Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ)) * Real.log (2 : ℝ) :=
          mul_le_mul_of_nonneg_right hfloor' hlog2pos.le
        _ = Real.log ((2 : ℝ) * e) := by field_simp [hlog2pos.ne']
    have hsum_eq : (logShellPaperAExponent 2 e + logShellPaperBExponent 2 e) *
        Real.log (2 : ℝ) =
        (2 + (logShellPaperBExponent 2 e + 1 / (e : ℝ)) - 1 / (e : ℝ)) *
          Real.log (2 : ℝ) := by
      rw [hA]
      ring
    have hBstep : (2 + (logShellPaperBExponent 2 e + 1 / (e : ℝ)) - 1 / (e : ℝ)) *
        Real.log (2 : ℝ) ≤
        (2 + Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ) - 1 / (e : ℝ)) *
          Real.log (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlog2pos.le
      linarith
    have hcalc : (2 + Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ) - 1 / (e : ℝ)) *
        Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) + Real.log (e : ℝ) -
          Real.log (2 : ℝ) / (e : ℝ) := by
      have hlogarg : Real.log ((2 : ℝ) * e) = Real.log (2 : ℝ) + Real.log (e : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hepos.ne']
      field_simp [hlog2pos.ne', hepos.ne']
      rw [hlogarg]
      ring
    have htarget : (2 + Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ) - 1 / (e : ℝ)) *
        Real.log (2 : ℝ) ≤ 3 + Real.log (e : ℝ) := by
      rw [hcalc]
      have hnonneg : 0 ≤ Real.log (2 : ℝ) / (e : ℝ) := div_nonneg hlog2pos.le hepos.le
      have h3 : 3 * Real.log (2 : ℝ) ≤ 3 := by nlinarith
      linarith
    calc
      (logShellPaperAExponent 2 e + logShellPaperBExponent 2 e) * Real.log (2 : ℝ) =
          (2 + (logShellPaperBExponent 2 e + 1 / (e : ℝ)) - 1 / (e : ℝ)) *
            Real.log (2 : ℝ) := hsum_eq
      _ ≤ (2 + Real.log ((2 : ℝ) * e) / Real.log (2 : ℝ) - 1 / (e : ℝ)) *
            Real.log (2 : ℝ) := hBstep
      _ ≤ 3 + Real.log (e : ℝ) := htarget
  · have hpgt : 2 < p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hA := logShellPaperAExponent_le_inv_add hp hp2 he
    have hB := logShellPaperBExponent_le_log_div hp he
    have hsum_le : logShellPaperAExponent p e + logShellPaperBExponent p e ≤
        1 / ((p : ℝ) - 2) + Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) := by
      have hA' : logShellPaperAExponent p e ≤ 1 / ((p : ℝ) - 2) + 1 / (e : ℝ) := hA
      have hB' : logShellPaperBExponent p e ≤
          Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) - 1 / (e : ℝ) := hB
      linarith
    have hmul_le := mul_le_mul_of_nonneg_right hsum_le hplogpos.le
    have hlog_expand : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) =
        Real.log ((p : ℝ) / ((p : ℝ) - 1)) + Real.log (e : ℝ) := by
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        linarith
      have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [show (p : ℝ) * e / ((p : ℝ) - 1) = ((p : ℝ) / ((p : ℝ) - 1)) * e by ring]
      rw [Real.log_mul (div_ne_zero hppos.ne' hden.ne') hepos.ne']
    have hAterm : (1 / ((p : ℝ) - 2) + Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
        Real.log (p : ℝ)) * Real.log (p : ℝ) =
        Real.log (p : ℝ) / ((p : ℝ) - 2) + Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := by
      field_simp [hplogpos.ne']
    rw [hAterm] at hmul_le
    rw [hlog_expand] at hmul_le
    have h1 := log_prime_div_prime_sub_two_le_two hp hp2
    have h2 := log_prime_div_prime_sub_one_le_one hp
    linarith

/-- The paper's sharp lower-exponent estimate `a_i - 1/e_i ≤ 4/p`. -/
theorem logShellPaperAExponent_sub_inv_le_four_div_prime
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    logShellPaperAExponent p e - 1 / (e : ℝ) ≤ 4 / (p : ℝ) := by
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  by_cases hp2 : p = 2
  · subst p
    have hA : logShellPaperAExponent 2 e = 2 := by simp [logShellPaperAExponent]
    have hinv_nonneg : 0 ≤ 1 / (e : ℝ) := div_nonneg zero_le_one hepos.le
    rw [hA]
    norm_num
  · have hpgt : 2 < p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hpgtR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    have hden : 0 < (p : ℝ) - 2 := by linarith
    have hceil_lt := Nat.ceil_lt_add_one (a := (e : ℝ) / ((p : ℝ) - 2)) (by positivity)
    have hceil_mul : ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) ≤
        (e : ℝ) / ((p : ℝ) - 2) := by linarith
    have hmain : (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1 / (e : ℝ) ≤
        1 / ((p : ℝ) - 2) := by
      have hcalc : (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1 / (e : ℝ) =
          ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) / (e : ℝ) := by
        field_simp [hepos.ne']
      rw [hcalc]
      calc
        ((Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) - 1) / (e : ℝ) ≤
            ((e : ℝ) / ((p : ℝ) - 2)) / (e : ℝ) :=
          div_le_div_of_nonneg_right hceil_mul hepos.le
        _ = 1 / ((p : ℝ) - 2) := by field_simp [hepos.ne']
    have hfour : 1 / ((p : ℝ) - 2) ≤ 4 / (p : ℝ) := by
      rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < p)]
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      nlinarith
    have hAeq : logShellPaperAExponent p e =
        (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) := by
      simp [logShellPaperAExponent, hp2]
    rw [hAeq]
    linarith

/-- The product form of the sharp lower-exponent estimate:
`(a_i - 1/e_i) * log p <= (4/p) * log p`. -/
theorem logShellPaperAExponent_sub_inv_mul_log_le_four_div_mul_log
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (logShellPaperAExponent p e - 1 / (e : ℝ)) * Real.log (p : ℝ) ≤
      (4 / (p : ℝ)) * Real.log (p : ℝ) := by
  exact mul_le_mul_of_nonneg_right
    (logShellPaperAExponent_sub_inv_le_four_div_prime hp he)
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))

/-- The paper's `b_i + 1/e_i` log estimate. -/
theorem logShellPaperBExponent_add_inv_mul_log_le_one_add_log
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (logShellPaperBExponent p e + 1 / (e : ℝ)) * Real.log (p : ℝ) ≤
      1 + Real.log (e : ℝ) := by
  have hepos : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one he)
  have hplogpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hargpos : 0 < (p : ℝ) * e / ((p : ℝ) - 1) :=
    div_pos (mul_pos hppos hepos) hden
  have hquot_nonneg : 0 ≤ Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) := by
    apply div_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ hden]
      have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
      nlinarith
    · exact hplogpos.le
  have hfloor : (Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
      Real.log (p : ℝ)) : ℝ) ≤
      Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ) :=
    Nat.floor_le hquot_nonneg
  have hBdecomp : logShellPaperBExponent p e + 1 / (e : ℝ) =
      (Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
        Real.log (p : ℝ)) : ℝ) := by
    dsimp [logShellPaperBExponent]
    ring
  rw [hBdecomp]
  have hmul := mul_le_mul_of_nonneg_right hfloor hplogpos.le
  have hlog_expand : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) =
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) + Real.log (e : ℝ) := by
    rw [show (p : ℝ) * e / ((p : ℝ) - 1) = ((p : ℝ) / ((p : ℝ) - 1)) * e by ring]
    rw [Real.log_mul (div_ne_zero hppos.ne' hden.ne') hepos.ne']
  have hratio := log_prime_div_prime_sub_one_le_one hp
  have hright : (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log (p : ℝ)) *
      Real.log (p : ℝ) = Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := by
    field_simp [hplogpos.ne']
  rw [hright] at hmul
  calc
    (Nat.floor (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) /
        Real.log (p : ℝ)) : ℝ) * Real.log (p : ℝ) ≤
        Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := hmul
    _ = Real.log ((p : ℝ) / ((p : ℝ) - 1)) + Real.log (e : ℝ) := hlog_expand
    _ ≤ 1 + Real.log (e : ℝ) := by linarith

/-- The paper's sharpened lower-exponent estimate
`(a_i - 1/e_i) * log p <= 2`.  It combines `a_i - 1/e_i <= 4/p` with
`(4/p) * log p <= 2`; the latter follows from `log p <= log 2 + p/2 - 1`. -/
theorem logShellPaperAExponent_sub_inv_mul_log_le_two
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (logShellPaperAExponent p e - 1 / (e : ℝ)) * Real.log (p : ℝ) ≤ 2 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogsplit : Real.log (p : ℝ) = Real.log 2 + Real.log ((p : ℝ) / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : (p : ℝ) / 2 ≠ 0)]
    congr 1
    field_simp
  have hloghalf : Real.log ((p : ℝ) / 2) ≤ (p : ℝ) / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (p : ℝ) / 2)
  have hlogp : Real.log (p : ℝ) ≤ Real.log 2 + ((p : ℝ) / 2 - 1) := by
    linarith
  have hfour : (4 / (p : ℝ)) * Real.log (p : ℝ) ≤ 2 := by
    calc (4 / (p : ℝ)) * Real.log (p : ℝ)
        ≤ (4 / (p : ℝ)) * (Real.log 2 + ((p : ℝ) / 2 - 1)) :=
          mul_le_mul_of_nonneg_left hlogp (by positivity)
      _ = 2 + 4 * (Real.log 2 - 1) / (p : ℝ) := by
          field_simp [hppos.ne']
          ring
      _ ≤ 2 := by
          have hneg : Real.log 2 - 1 ≤ 0 := by linarith
          have hnonpos : 4 * (Real.log 2 - 1) / (p : ℝ) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg) hppos.le
          linarith
  have h1 := logShellPaperAExponent_sub_inv_le_four_div_prime hp he
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.log_nonneg hp1)
  exact h2.trans hfour

private theorem log_prime_div_prime_sub_one_le_log_two {p : ℕ} (hp : p.Prime) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) ≤ Real.log 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hratio_pos : 0 < (p : ℝ) / ((p : ℝ) - 1) := div_pos (by positivity) hden
  apply Real.log_le_log hratio_pos
  rw [div_le_iff₀ hden]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  nlinarith

/-- The paper's upper-exponent estimate in the sharper `log (2 e_i)` form:
`(b_i + 1/e_i) * log p <= log (2 e_i)`. -/
theorem logShellPaperBExponent_add_inv_mul_log_le_log_two_mul
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (logShellPaperBExponent p e + 1 / (e : ℝ)) * Real.log (p : ℝ) ≤
      Real.log (2 * (e : ℝ)) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt he)
  have hplogpos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < (p : ℝ))
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hargpos : 0 < (p : ℝ) * (e : ℝ) / ((p : ℝ) - 1) :=
    div_pos (mul_pos hppos hepos) hden
  have hquot_nonneg : 0 ≤ Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
      Real.log (p : ℝ) := by
    apply div_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ hden]
      have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
      nlinarith
    · exact hplogpos.le
  have hfloor : (Nat.floor (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
      Real.log (p : ℝ)) : ℝ) ≤
      Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) / Real.log (p : ℝ) :=
    Nat.floor_le hquot_nonneg
  have hBdecomp : logShellPaperBExponent p e + 1 / (e : ℝ) =
      (Nat.floor (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
        Real.log (p : ℝ)) : ℝ) := by
    dsimp [logShellPaperBExponent]
    ring
  rw [hBdecomp]
  have hmul := mul_le_mul_of_nonneg_right hfloor hplogpos.le
  have hlog_expand : Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) =
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) + Real.log (e : ℝ) := by
    rw [show (p : ℝ) * (e : ℝ) / ((p : ℝ) - 1) =
      ((p : ℝ) / ((p : ℝ) - 1)) * (e : ℝ) by ring]
    rw [Real.log_mul (div_ne_zero hppos.ne' hden.ne') hepos.ne']
  have hright : (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) / Real.log (p : ℝ)) *
      Real.log (p : ℝ) = Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) := by
    field_simp [hplogpos.ne']
  rw [hright] at hmul
  calc (Nat.floor (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
        Real.log (p : ℝ)) : ℝ) * Real.log (p : ℝ)
      ≤ Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) := hmul
    _ = Real.log ((p : ℝ) / ((p : ℝ) - 1)) + Real.log (e : ℝ) := hlog_expand
    _ ≤ Real.log 2 + Real.log (e : ℝ) := by
        linarith [log_prime_div_prime_sub_one_le_log_two hp]
    _ = Real.log (2 * (e : ℝ)) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hepos.ne']

/-- The elementary comparison closing the paper's second log-volume chain. -/
theorem log_two_mul_le_one_add_log {e : ℕ} (he : 1 ≤ e) :
    Real.log (2 * (e : ℝ)) ≤ 1 + Real.log (e : ℝ) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt he)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hepos.ne']
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  linarith

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

/-- The order of the finite `p*`-congruence quotient of the actual integral
unit group.  It is an auxiliary finite exponent, not the paper's `b_i`. -/
def logShellCongruenceQuotientCard : ℕ :=
  Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p))

omit [CompleteSpace K] localNormedAlgebra in
theorem logShellCongruenceQuotientCard_pos :
    0 < logShellCongruenceQuotientCard (K := K) (p := p) := by
  letI := finite_logShellCongruenceQuotient (K := K) (p := p)
  exact Nat.card_pos

/-- The explicit integer upper exponent obtained from the finite congruence
quotient.  It is a proved bound, but it is not the paper's rational `b_i`. -/
def logShellCongruenceUpperExponent : ℕ :=
  padicValNat p (logShellCongruenceQuotientCard (K := K) (p := p))

omit [CharZero K] [CompleteSpace K] [ProperSpace K] [Fact p.Prime]
  localNormedAlgebra in
theorem pow_logShellCongruenceQuotientCard_mem (u : (Integers K)ˣ) :
    u ^ logShellCongruenceQuotientCard (K := K) (p := p) ∈
      logShellCongruenceUnits (K := K) (p := p) := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_card_eq_one'

omit [CharZero K] [CompleteSpace K] [ProperSpace K] [Fact p.Prime]
  localNormedAlgebra in
theorem pow_mul_logShellScale_mem (u : (Integers K)ˣ) :
    u ^ (logShellCongruenceQuotientCard (K := K) (p := p) * logShellScale p) ∈
      logShellCongruenceUnits (K := K) (p := p) := by
  rw [pow_mul]
  exact (logShellCongruenceUnits (K := K) (p := p)).pow_mem
    (pow_logShellCongruenceQuotientCard_mem (K := K) (p := p) u) (logShellScale p)

/-- Multiplying the logarithm of any integral unit by the congruence-quotient
cardinality lands in the integer ring.  This is the concrete finite-exponent
step behind the auxiliary coarse upper bound. -/
theorem card_mul_unitLog_mem_integers (u : (Integers K)ˣ) :
    (logShellCongruenceQuotientCard (K := K) (p := p) : K) * unitLog u ∈
      Integers K := by
  let N := logShellCongruenceQuotientCard (K := K) (p := p)
  let s := logShellScale p
  have hmem := scaledUnitLog_mem_integers_of_mem_congruence (K := K) (p := p)
    (u ^ (N * s)) (pow_mul_logShellScale_mem (K := K) (p := p) u)
  have hs : (s : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
  have hcast : ((N * s : ℕ) : K) = (N : K) * (s : K) := by
    exact Nat.cast_mul N s
  have heq : (s : K)⁻¹ * unitLog (K := K) (u ^ (N * s)) =
      (N : K) * unitLog (K := K) u := by
    rw [unitLog_pow (K := K) (p := p), hcast]
    field_simp [hs]
  rw [← heq]
  exact hmem

omit [CompleteSpace K] in
/-- The integer-ring quotient `p^b / N` is integral, where `b` is the
`p`-adic order of `N`. -/
theorem pow_padicValNat_div_card_mem_integers :
    (p : K) ^ logShellCongruenceUpperExponent (K := K) (p := p) /
        (logShellCongruenceQuotientCard (K := K) (p := p) : K) ∈ Integers K := by
  let N := logShellCongruenceQuotientCard (K := K) (p := p)
  let b := logShellCongruenceUpperExponent (K := K) (p := p)
  let m := ordCompl[p] N
  have hNpos : 0 < N := logShellCongruenceQuotientCard_pos (K := K) (p := p)
  have hNne : N ≠ 0 := hNpos.ne'
  have hb : b = padicValNat p N := rfl
  have hord : ordProj[p] N = p ^ b := by
    rw [hb, Nat.factorization_def N Fact.out]
  have hdecompNat : N = p ^ b * m := by
    calc
      N = ordProj[p] N * m := (Nat.ordProj_mul_ordCompl_eq_self N p).symm
      _ = p ^ b * m := by rw [hord]
  have hmpos : 0 < m := Nat.ordCompl_pos p hNne
  have hmne : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl Fact.out hNne
  have hmnorm_q : ‖(m : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr hcop
  have hmnorm : ‖(m : K)‖ = 1 := by
    calc
      ‖(m : K)‖ = ‖algebraMap ℚ_[p] K (m : ℚ_[p])‖ := by
        simp only [map_natCast]
      _ = ‖(m : ℚ_[p])‖ := norm_algebraMap' K (m : ℚ_[p])
      _ = 1 := hmnorm_q
  have hmcast : (N : K) = (p : K) ^ b * (m : K) := by
    rw [hdecompNat, Nat.cast_mul, Nat.cast_pow]
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpbne : (p : K) ^ b ≠ 0 := pow_ne_zero b hpne
  have hquot : (p : K) ^ b / (N : K) = (m : K)⁻¹ := by
    rw [hmcast]
    field_simp [hpbne, hmne]
  rw [hquot]
  apply (mem_integers_iff _).mpr
  rw [norm_inv, hmnorm, inv_one]

/-- Auxiliary coarse upper bound: every logarithm of an actual integral unit
lies in `p^{-b} O_K`, with `b = v_p (#(O_K^× / (1 + p* O_K)))`.
This is not the paper's `b_i`. -/
theorem unitLog_range_subset_pow_neg_smul_logShellCongruenceUpperExponent :
    Set.range (unitLog (K := K)) ⊆
      ((p : K) ^ (-(logShellCongruenceUpperExponent (K := K) (p := p) : ℤ)) : K) •
        (Integers K : Set K) := by
  rintro _ ⟨u, rfl⟩
  let N := logShellCongruenceQuotientCard (K := K) (p := p)
  let b := logShellCongruenceUpperExponent (K := K) (p := p)
  let y : Integers K :=
    ⟨(N : K) * unitLog (K := K) u,
      card_mul_unitLog_mem_integers (K := K) (p := p) u⟩
  let z : Integers K :=
    ⟨(p : K) ^ b / (N : K), pow_padicValNat_div_card_mem_integers (K := K) (p := p)⟩
  refine ⟨(y * z : Integers K), (y * z).property, ?_⟩
  have hNne : (N : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (logShellCongruenceQuotientCard_pos (K := K) (p := p)).ne'
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  change ((p : K) ^ (-(b : ℤ)) : K) * (((y : K) * (z : K))) =
    unitLog (K := K) u
  dsimp [y, z]
  rw [zpow_neg, zpow_natCast]
  field_simp [hpne, hNne]

/-- Existential form of the auxiliary general upper bound. -/
theorem exists_unitLog_range_subset_pow_inv_smul :
    ∃ b : ℕ, Set.range (unitLog (K := K)) ⊆
      ((p : K) ^ (-(b : ℤ)) : K) • (Integers K : Set K) :=
  ⟨logShellCongruenceUpperExponent (K := K) (p := p),
    unitLog_range_subset_pow_neg_smul_logShellCongruenceUpperExponent (K := K) (p := p)⟩

/-- Under the explicit integer-ring uniformizer hypothesis, membership in the
prime ideal is equivalent to the elementary norm bound defining the closed
congruence radius. -/
theorem mem_span_prime_iff_norm_le_norm_prime_of_irreducible
    (hpi : Irreducible (p : Integers K)) (z : Integers K) :
    z ∈ Ideal.span {(p : Integers K)} ↔ ‖(z : K)‖ ≤ ‖(p : K)‖ := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  have hnormp : ‖(p : K)‖ < 1 := norm_prime_lt_one (K := K) (p := p)
  constructor
  · intro hz
    rw [Ideal.mem_span_singleton] at hz
    rcases hz with ⟨a, ha⟩
    calc
      ‖(z : K)‖ = ‖((p : Integers K) : K) * (a : K)‖ := by
        rw [ha, Subring.coe_mul]
      _ = ‖(p : K)‖ * ‖(a : K)‖ := norm_mul _ _
      _ ≤ ‖(p : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left ((mem_integers_iff (K := K) _).mp a.property)
          (norm_nonneg (p : K))
      _ = ‖(p : K)‖ := mul_one _
  · intro hz
    have hznotunit : ¬ IsUnit z := by
      intro hzunit
      rcases hzunit with ⟨v, hv⟩
      have hvnorm : ‖(z : K)‖ = 1 := by
        rw [← hv]
        exact norm_unit_eq_one (K := K) v
      linarith
    have hzmax : z ∈ IsLocalRing.maximalIdeal (Integers K) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hznotunit
    rw [← hpi.maximalIdeal_eq]
    exact hzmax

/-- Under the explicit integer-ring uniformizer hypothesis, the closed
`p`-congruence subgroup of actual integral units is the principal-unit group. -/
theorem logShellCongruenceUnits_eq_principalUnits_of_irreducible
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    logShellCongruenceUnits (K := K) (p := p) = principalUnits (K := K) := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  ext u
  constructor
  · intro hu
    apply (mem_principalUnits_iff (K := K) u).mpr
    change ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖ at hu
    rw [show logShellScale p = p by simp [logShellScale, hp2]] at hu
    exact hu.trans_lt (norm_prime_lt_one (K := K) (p := p))
  · intro hu
    change ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖
    rw [show logShellScale p = p by simp [logShellScale, hp2]]
    have hznorm0 : ‖((u.val : K) - 1)‖ < 1 :=
      (mem_principalUnits_iff (K := K) u).mp hu
    let z : Integers K := u.val - 1
    have hznorm : ‖(z : K)‖ < 1 := by
      simpa [z] using hznorm0
    change ‖(z : K)‖ ≤ ‖(p : K)‖
    by_cases hz0 : z = 0
    · rw [hz0]
      simp
    · have hznotunit : ¬ IsUnit z := by
        intro hzunit
        rcases hzunit with ⟨v, hv⟩
        have hvnorm : ‖(z : K)‖ = 1 := by
          rw [← hv]
          exact norm_unit_eq_one (K := K) v
        linarith
      have hzmax : z ∈ IsLocalRing.maximalIdeal (Integers K) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hznotunit
      have hzspan : z ∈ Ideal.span {(p : Integers K)} := by
        rw [← hpi.maximalIdeal_eq]
        exact hzmax
      rw [Ideal.mem_span_singleton] at hzspan
      rcases hzspan with ⟨a, ha⟩
      calc
        ‖(z : K)‖ = ‖((p : Integers K) : K) * (a : K)‖ := by
          rw [ha, Subring.coe_mul]
        _ = ‖(p : K)‖ * ‖(a : K)‖ := norm_mul _ _
        _ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left ((mem_integers_iff (K := K) _).mp a.property)
            (norm_nonneg (p : K))
        _ = ‖(p : K)‖ := mul_one _

/-- The canonical reduction map from actual integral units to the units of
the residue field. -/
def integralUnitToLogShellResidueUnits :
    (Integers K)ˣ →* (logShellResidueField (K := K))ˣ :=
  Units.map (IsLocalRing.residue (Integers K)).toMonoidHom

omit [CharZero K] [CompleteSpace K] [ProperSpace K] [Fact p.Prime]
  localNormedAlgebra in
theorem integralUnitToLogShellResidueUnits_surjective :
    Function.Surjective (integralUnitToLogShellResidueUnits (K := K)) := by
  simpa [integralUnitToLogShellResidueUnits] using
    (IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue (Integers K))
      (IsLocalRing.residue_surjective (R := Integers K))
      (inferInstance : IsLocalHom (IsLocalRing.residue (Integers K))))

theorem integralUnitToLogShellResidueUnits_ker_eq
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    (integralUnitToLogShellResidueUnits (K := K)).ker =
      logShellCongruenceUnits (K := K) (p := p) := by
  ext u
  rw [MonoidHom.mem_ker]
  constructor
  · intro hres
    change ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖
    rw [show logShellScale p = p by simp [logShellScale, hp2]]
    have hresval : IsLocalRing.residue (Integers K) (u.val : Integers K) = 1 := by
      have hval := congrArg (fun v : (logShellResidueField (K := K))ˣ =>
        (v : logShellResidueField (K := K))) hres
      simpa [integralUnitToLogShellResidueUnits] using hval
    have hzres : IsLocalRing.residue (Integers K) (u.val - 1) = 0 := by
      rw [map_sub, hresval, map_one, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at hzres
    have hzspan : u.val - 1 ∈ Ideal.span {(p : Integers K)} := by
      letI : IsDiscreteValuationRing (Integers K) :=
        isDiscreteValuationRingIntegers (K := K) (p := p)
      rw [← hpi.maximalIdeal_eq]
      exact hzres
    exact (mem_span_prime_iff_norm_le_norm_prime_of_irreducible
      (K := K) (p := p) hpi (u.val - 1)).mp hzspan
  · intro hu
    change ‖(u.val : K) - 1‖ ≤ ‖(logShellScale p : K)‖ at hu
    rw [show logShellScale p = p by simp [logShellScale, hp2]] at hu
    apply Units.ext
    change IsLocalRing.residue (Integers K) (u.val : Integers K) = 1
    have hzspan : u.val - 1 ∈ Ideal.span {(p : Integers K)} :=
      (mem_span_prime_iff_norm_le_norm_prime_of_irreducible
        (K := K) (p := p) hpi (u.val - 1)).mpr hu
    have hzmax : u.val - 1 ∈ IsLocalRing.maximalIdeal (Integers K) := by
      letI : IsDiscreteValuationRing (Integers K) :=
        isDiscreteValuationRingIntegers (K := K) (p := p)
      rw [hpi.maximalIdeal_eq]
      exact hzspan
    have hzres : IsLocalRing.residue (Integers K) (u.val - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff (u.val - 1)).mpr hzmax
    rw [map_sub, map_one, sub_eq_zero] at hzres
    simpa [integralUnitToLogShellResidueUnits] using hzres

/-- The residue field of the actual integer ring has characteristic `p`. -/
theorem logShellResidueField_charP :
    CharP (logShellResidueField (K := K)) p := by
  have hpnorm : ‖(p : K)‖ < 1 := norm_prime_lt_one (K := K) (p := p)
  have hnotunit : ¬ IsUnit (p : Integers K) := by
    intro hu
    rcases hu with ⟨u, hu⟩
    have hnorm : ‖((u : Integers K) : K)‖ = 1 := norm_unit_eq_one (K := K) u
    have hcoe : ((u : Integers K) : K) = (p : K) := by
      simpa using congrArg (fun x : Integers K => (x : K)) hu
    rw [hcoe] at hnorm
    linarith
  have hmem : (p : Integers K) ∈ IsLocalRing.maximalIdeal (Integers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnotunit
  have hzero : IsLocalRing.residue (Integers K) (p : Integers K) = 0 :=
    (IsLocalRing.residue_eq_zero_iff (p : Integers K)).mpr hmem
  have hcast : ((p : ℕ) : logShellResidueField (K := K)) = 0 := by
    change IsLocalRing.residue (Integers K) (p : Integers K) = 0
    exact hzero
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hcast

theorem logShellResidueCard_eq_prime_pow :
    ∃ f : ℕ, 1 ≤ f ∧ logShellResidueCard (K := K) = p ^ f := by
  letI : CharP (logShellResidueField (K := K)) p :=
    logShellResidueField_charP (K := K) (p := p)
  letI : Finite (logShellResidueField (K := K)) :=
    finite_logShellResidueField (K := K) (p := p)
  letI : Fintype (logShellResidueField (K := K)) := Fintype.ofFinite _
  obtain ⟨n, hp, hq⟩ := FiniteField.card (logShellResidueField (K := K)) p
  refine ⟨(n : ℕ), Nat.succ_le_of_lt n.pos, ?_⟩
  rw [logShellResidueCard, Nat.card_eq_fintype_card, hq]

theorem coprime_p_logShellResidueCard_sub_one :
    Nat.Coprime p (logShellResidueCard (K := K) - 1) := by
  obtain ⟨f, hf, hq⟩ := logShellResidueCard_eq_prime_pow (K := K) (p := p)
  rw [hq]
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_antisymm
  · have hdvd_p : Nat.gcd p (p ^ f - 1) ∣ p := Nat.gcd_dvd_left _ _
    have hdvd_m : Nat.gcd p (p ^ f - 1) ∣ p ^ f - 1 := Nat.gcd_dvd_right _ _
    have hdvd_pow : Nat.gcd p (p ^ f - 1) ∣ p ^ f :=
      dvd_trans hdvd_p (dvd_pow_self p (by omega : f ≠ 0))
    have h := Nat.dvd_sub hdvd_pow hdvd_m
    have hpow : 1 ≤ p ^ f := Nat.one_le_pow f p (Fact.out : p.Prime).pos
    have hsub : p ^ f - (p ^ f - 1) = 1 := by omega
    rwa [hsub] at h
  · exact Nat.one_dvd _

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K] in
theorem norm_natCast_eq_prime_zpow_neg_padicValNat (m : ℕ) (hm : 0 < m) :
    ‖(m : K)‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
  have hmne : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
  have hq : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hmne, Padic.valuation_natCast]
  calc
    ‖(m : K)‖ = ‖algebraMap ℚ_[p] K (m : ℚ_[p])‖ := by simp only [map_natCast]
    _ = ‖(m : ℚ_[p])‖ := norm_algebraMap' K (m : ℚ_[p])
    _ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := hq

theorem norm_uniformizer_eq_prime_rpow_inv_ramificationExponent
    (π : Integers K) (hπ : Irreducible π) :
    ‖(π : K)‖ =
      (p : ℝ) ^ (-(1 / (logShellRamificationExponent (K := K) (p := p) : ℝ))) := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  let e := logShellRamificationExponent (K := K) (p := p)
  have hepos : 0 < e := logShellRamificationExponent_pos (K := K) (p := p)
  have hp0 : (p : Integers K) ≠ 0 := prime_ne_zero_integers (K := K) (p := p)
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  have hpval : IsDiscreteValuationRing.addVal (Integers K) (p : Integers K) = (e : ℕ∞) := by
    simpa [e, ramifiedPrimeAddVal] using
      (addVal_prime_eq_ramificationExponent (K := K) (p := p))
  have hn : n = e := by
    have hval := congrArg
      (fun z : Integers K => IsDiscreteValuationRing.addVal (Integers K) z) hu
    rw [hpval, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, hπ.addVal_pow] at hval
    exact (Nat.cast_injective hval).symm
  have hnormp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    calc
      ‖(p : K)‖ = ‖(p : ℚ_[p])‖ := by
        simpa only [map_natCast] using norm_algebraMap' K (p : ℚ_[p])
      _ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcoe : (p : K) = ((u : Integers K) : K) * (π : K) ^ n := by
    have h := congrArg (fun z : Integers K => (z : K)) hu
    simpa [Subring.coe_mul, Subring.coe_pow] using h
  have hnormpow : ‖(π : K)‖ ^ e = (p : ℝ)⁻¹ := by
    calc
      ‖(π : K)‖ ^ e = ‖(π : K) ^ n‖ := by rw [hn, norm_pow]
      _ = ‖((u : Integers K) : K) * (π : K) ^ n‖ := by
        rw [norm_mul, norm_unit_eq_one (K := K) u, one_mul]
      _ = ‖(p : K)‖ := by rw [← hcoe]
      _ = (p : ℝ)⁻¹ := hnormp
  calc
    ‖(π : K)‖ = (‖(π : K)‖ ^ e) ^ ((e : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (norm_nonneg _) hepos.ne').symm
    _ = ((p : ℝ)⁻¹) ^ ((e : ℝ)⁻¹) := by rw [hnormpow]
    _ = (p : ℝ) ^ (-(1 / (e : ℝ))) := by
      rw [one_div]
      exact (Real.rpow_neg_eq_inv_rpow (p : ℝ) ((e : ℝ)⁻¹)).symm

theorem norm_le_prime_rpow_inv_ramificationExponent_of_mem_maximalIdeal
    {z : Integers K} (hz : z ∈ IsLocalRing.maximalIdeal (Integers K)) :
    ‖(z : K)‖ ≤
      (p : ℝ) ^ (-(1 / (logShellRamificationExponent (K := K) (p := p) : ℝ))) := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  have hzspan : z ∈ Ideal.span ({π} : Set (Integers K)) := by
    rwa [hπ.maximalIdeal_eq] at hz
  rw [Ideal.mem_span_singleton] at hzspan
  rcases hzspan with ⟨a, rfl⟩
  rw [Subring.coe_mul, norm_mul,
    norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (K := K) (p := p) π hπ]
  calc
    (p : ℝ) ^ (-(1 / (logShellRamificationExponent (K := K) (p := p) : ℝ))) *
        ‖(a : K)‖ ≤
      (p : ℝ) ^ (-(1 / (logShellRamificationExponent (K := K) (p := p) : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left ((mem_integers_iff (K := K) _).mp a.property) (by positivity)
    _ = _ := mul_one _

omit [CharZero K] [CompleteSpace K] [ProperSpace K] [Fact p.Prime]
  localNormedAlgebra in
theorem mem_principalUnits_of_residue_eq_one (u : (Integers K)ˣ)
    (h : IsLocalRing.residue (Integers K) (u.val : Integers K) = 1) :
    u ∈ principalUnits (K := K) := by
  rw [mem_principalUnits_iff]
  let z : Integers K := u.val - 1
  have hzres : IsLocalRing.residue (Integers K) z = 0 := by
    simp [z, h]
  have hzmax : z ∈ IsLocalRing.maximalIdeal (Integers K) :=
    (IsLocalRing.residue_eq_zero_iff z).mp hzres
  have hznorm_lt : ‖(z : K)‖ < 1 := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hznorm_le : ‖(z : K)‖ ≤ 1 := (mem_integers_iff (K := K) z).mp z.property
      by_contra hnot
      have hznorm_eq : ‖(z : K)‖ = 1 := le_antisymm hznorm_le (le_of_not_gt hnot)
      let v := unitOfNormOne (K := K) ⟨z, hznorm_eq⟩
      have hv : IsUnit z := (Units.isUnit v : IsUnit (v : Integers K))
      rw [IsLocalRing.mem_maximalIdeal] at hzmax
      exact hzmax hv
  simpa [z] using hznorm_lt

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K] in
/-- Termwise form of the paper's `b_i` estimate.  If `z` lies in the maximal
ideal, so `‖z‖ <= p^(-1/e)`, then the `n`-th term of the negative logarithm
series has norm at most `p^(b_i)`.  The proof uses
`v_p(n+1) - (n+1)/e <= b_i` and `‖(n+1 : K)‖⁻¹ = p^(v_p(n+1))`. -/
private theorem negativeLogTerm_norm_le_paperBUpper {e : ℕ} (he : 1 ≤ e) {z : K}
    (hz : ‖z‖ ≤ (p : ℝ) ^ (-(1 / (e : ℝ)))) (n : ℕ) :
    ‖negativeLogTerm z n‖ ≤ (p : ℝ) ^ (logShellPaperBExponent p e) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hterm : ‖negativeLogTerm z n‖ =
      ‖z‖ ^ (n + 1) * ‖(((n + 1 : ℕ)) : K)‖⁻¹ := by
    rw [negativeLogTerm, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
      div_eq_mul_inv]
    norm_num
  have hden : ‖(((n + 1 : ℕ)) : K)‖⁻¹ =
      (p : ℝ) ^ ((padicValNat p (n + 1) : ℤ) : ℝ) := by
    rw [norm_natCast_eq_prime_zpow_neg_padicValNat (K := K) (p := p) (n + 1) (Nat.succ_pos n)]
    rw [← Real.rpow_intCast]
    simp
  have hpow : ‖z‖ ^ (n + 1) ≤ ((p : ℝ) ^ (-(1 / (e : ℝ)))) ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg z) hz (n + 1)
  have hmul : ‖negativeLogTerm z n‖ ≤
      ((p : ℝ) ^ (-(1 / (e : ℝ)))) ^ (n + 1) *
        (p : ℝ) ^ ((padicValNat p (n + 1) : ℤ) : ℝ) := by
    rw [hterm, hden]
    exact mul_le_mul hpow le_rfl (by positivity) (pow_nonneg (by positivity) _)
  refine hmul.trans ?_
  have hrewrite : ((p : ℝ) ^ (-(1 / (e : ℝ)))) ^ (n + 1) *
      (p : ℝ) ^ ((padicValNat p (n + 1) : ℤ) : ℝ) =
      (p : ℝ) ^
        (-(1 / (e : ℝ)) * ((n + 1 : ℕ) : ℝ) +
          ((padicValNat p (n + 1) : ℤ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < (p : ℝ))]
  rw [hrewrite]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  have hb := padicValNat_sub_div_le_logShellPaperBExponent (p := p) (e := e)
    (Fact.out : p.Prime) he (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have heq : -(1 / (e : ℝ)) * ((n + 1 : ℕ) : ℝ) +
      ((padicValNat p (n + 1) : ℤ) : ℝ) =
      (padicValNat p (n + 1) : ℝ) - ((n + 1 : ℕ) : ℝ) / (e : ℝ) := by
    rw [Int.cast_natCast]
    ring
  rw [heq]
  exact hb

omit [CharZero K] [CompleteSpace K] [ProperSpace K] in
/-- The analytic `log1p` obeys the paper's `b_i` bound on the closed ball of
radius `p^(-1/e)`.  The negative logarithm series converges there, and the
nonarchimedean ultrametric bound passes the termwise estimate to the sum. -/
private theorem log1p_norm_le_paperBUpper {e : ℕ} (he : 1 ≤ e) {z : K}
    (hz : ‖z‖ ≤ (p : ℝ) ^ (-(1 / (e : ℝ)))) :
    ‖log1p z‖ ≤ (p : ℝ) ^ (logShellPaperBExponent p e) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hepos : (0 : ℝ) < (e : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt he)
  have hneg : -(1 / (e : ℝ)) < 0 := by
    have : 0 < 1 / (e : ℝ) := div_pos one_pos hepos
    linarith
  have hz1 : ‖z‖ < 1 := by
    refine hz.trans_lt ?_
    calc (p : ℝ) ^ (-(1 / (e : ℝ))) < (p : ℝ) ^ (0:ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hp1 hneg
      _ = 1 := Real.rpow_zero _
  have hseries : ‖negativeLogSeries z‖ ≤ (p : ℝ) ^ (logShellPaperBExponent p e) := by
    simpa [negativeLogSeries] using
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
        (f := negativeLogTerm z)
        (C := (p : ℝ) ^ (logShellPaperBExponent p e))
        (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (p:ℝ)) _)
        (fun n => negativeLogTerm_norm_le_paperBUpper (K := K) (p := p) he hz n)
  simpa [log1p] using hseries

/-- The exponent `q - 1`, where `q` is the residue cardinality, is prime to
`p`; hence its image in `K` is a `p`-adic unit of norm one. -/
theorem norm_natCast_logShellResidueCard_sub_one :
    ‖(((logShellResidueCard (K := K) - 1) : ℕ) : K)‖ = 1 := by
  let N := logShellResidueCard (K := K) - 1
  have hq1 : 1 < logShellResidueCard (K := K) :=
    one_lt_logShellResidueCard (K := K) (p := p)
  have hNpos : 0 < N := Nat.sub_pos_of_lt hq1
  have hcop : Nat.Coprime p N :=
    coprime_p_logShellResidueCard_sub_one (K := K) (p := p)
  have hnotdvd : ¬ p ∣ N := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
  have hvalN : padicValNat p N = 0 := padicValNat.eq_zero_of_not_dvd hnotdvd
  rw [norm_natCast_eq_prime_zpow_neg_padicValNat (K := K) (p := p) N hNpos, hvalN]
  simp

/-- Paper IV Proposition 1.2(i), general upper inclusion on the unscaled
carrier: `unitLogLattice <= padicFractionalLattice (-b_i)`, where
`b_i = floor(log_p (p e/(p-1))) - 1/e` and `e` is the actual ramification
exponent of `p` in `K`.  The proof raises a unit to the residue cardinality
minus one, reducing to a principal unit, and applies the termwise `b_i`
estimate to `log1p`. -/
theorem unitLogLattice_le_padicFractionalLattice_neg_paperB :
    unitLogLattice (K := K) (p := p) ≤
      padicFractionalLattice (p := p) (K := K)
        (-(logShellPaperBExponent p (logShellRamificationExponent (K := K) (p := p)))) := by
  intro x hx
  rw [mem_unitLogLattice_iff] at hx
  obtain ⟨u, rfl⟩ := hx
  let e := logShellRamificationExponent (K := K) (p := p)
  have he : 1 ≤ e :=
    Nat.succ_le_of_lt (logShellRamificationExponent_pos (K := K) (p := p))
  let q := logShellResidueCard (K := K)
  let N := q - 1
  have hq1 : 1 < q := one_lt_logShellResidueCard (K := K) (p := p)
  have hNpos : 0 < N := Nat.sub_pos_of_lt hq1
  have hNne : N ≠ 0 := hNpos.ne'
  have hcop : Nat.Coprime p N :=
    coprime_p_logShellResidueCard_sub_one (K := K) (p := p)
  have hnotdvd : ¬ p ∣ N := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
  have hvalN : padicValNat p N = 0 := padicValNat.eq_zero_of_not_dvd hnotdvd
  have hNnorm : ‖(N : K)‖ = 1 := by
    rw [norm_natCast_eq_prime_zpow_neg_padicValNat (K := K) (p := p) N hNpos, hvalN]
    simp
  have hw : (integralUnitToLogShellResidueUnits (K := K) u) ^ N = 1 := by
    have h := pow_card_eq_one' (G := (logShellResidueField (K := K))ˣ)
      (x := integralUnitToLogShellResidueUnits (K := K) u)
    rwa [Nat.card_units, ← logShellResidueCard] at h
  have hresN : IsLocalRing.residue (Integers K) (((u ^ N).val : Integers K)) = 1 := by
    have hmap : integralUnitToLogShellResidueUnits (K := K) (u ^ N) = 1 := by
      rw [map_pow]
      exact hw
    have hval := congrArg (fun v : (logShellResidueField (K := K))ˣ =>
      (v : logShellResidueField (K := K))) hmap
    simpa [integralUnitToLogShellResidueUnits] using hval
  have hmem : u ^ N ∈ principalUnits (K := K) :=
    mem_principalUnits_of_residue_eq_one (K := K) (u ^ N) hresN
  let y : Integers K := (u ^ N).val - 1
  have hyres : IsLocalRing.residue (Integers K) y = 0 := by
    change IsLocalRing.residue (Integers K) (((u ^ N).val : Integers K) - 1) = 0
    rw [map_sub, hresN, map_one, sub_self]
  have hymax : y ∈ IsLocalRing.maximalIdeal (Integers K) :=
    (IsLocalRing.residue_eq_zero_iff y).mp hyres
  have hylt : ‖(y : K)‖ ≤ (p : ℝ) ^ (-(1 / (e : ℝ))) :=
    norm_le_prime_rpow_inv_ramificationExponent_of_mem_maximalIdeal (K := K) (p := p) hymax
  have hlog : ‖unitLog u‖ ≤ (p : ℝ) ^ logShellPaperBExponent p e := by
    rw [unitLog_eq_withExponent (p := p) u hNne hmem]
    change ‖log1p ((((u ^ N).val : K) - 1)) / (N : K)‖ ≤ _
    rw [norm_div, hNnorm, div_one]
    exact log1p_norm_le_paperBUpper (K := K) (p := p) he hylt
  rw [mem_padicFractionalLattice_iff]
  simpa using hlog

omit [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]
  [ProperSpace K] [Fact p.Prime] localNormedAlgebra in
/-- The paper's lower exponent always lies strictly above the sharp inverse
radius `1/(p-1)`: for `p > 2`,
`(1/e) * ceil(e/(p-2)) >= 1/(p-2) > 1/(p-1)`, and for `p = 2` it is `2`. -/
theorem one_div_pred_lt_logShellPaperAExponent {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    1 / ((p : ℝ) - 1) < logShellPaperAExponent p e := by
  by_cases hp2 : p = 2
  · subst p
    have hA : logShellPaperAExponent 2 e = 2 := by simp [logShellPaperAExponent]
    rw [hA]
    norm_num
  · have hpgt : 2 < p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hepos : (0 : ℝ) < e := by exact_mod_cast (Nat.zero_lt_of_lt he)
    have hp2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    have hden2 : 0 < (p : ℝ) - 2 := by linarith
    have hden1 : 0 < (p : ℝ) - 1 := by linarith
    rw [logShellPaperAExponent, if_neg hp2]
    have hceil : (e : ℝ) / ((p : ℝ) - 2) ≤
        (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) := Nat.le_ceil _
    have hmul : 1 / ((p : ℝ) - 2) ≤
        (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) := by
      calc 1 / ((p : ℝ) - 2) = (1 / (e : ℝ)) * ((e : ℝ) / ((p : ℝ) - 2)) := by
            field_simp [hepos.ne']
        _ ≤ (1 / (e : ℝ)) * (Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)) : ℝ) :=
            mul_le_mul_of_nonneg_left hceil (by positivity)
    have hlt : 1 / ((p : ℝ) - 1) < 1 / ((p : ℝ) - 2) := by
      apply one_div_lt_one_div_of_lt hden2
      linarith
    linarith

/-- Paper IV Proposition 1.2(i), general lower inclusion on the unscaled
carrier: `padicFractionalLattice a_i <= unitLogLattice`, where
`a_i = (1/e) * ceil(e/(p-2))` for `p > 2` and `a_i = 2` for `p = 2`, with
`e` the actual ramification exponent of `p` in `K`. -/
theorem padicFractionalLattice_paperA_le_unitLogLattice :
    padicFractionalLattice (p := p) (K := K)
        (logShellPaperAExponent p (logShellRamificationExponent (K := K) (p := p))) ≤
      unitLogLattice (K := K) (p := p) := by
  apply padicFractionalLattice_le_unitLogLattice_of_one_div_lt (K := K) (p := p)
  exact one_div_pred_lt_logShellPaperAExponent (p := p)
    (e := logShellRamificationExponent (K := K) (p := p)) (Fact.out : p.Prime)
    (Nat.succ_le_of_lt (logShellRamificationExponent_pos (K := K) (p := p)))

/-- The paper's lower ramification element `α_i = π^(e a_i)`, where `π` is a
uniformizer of `K`.  Its normalized order is `a_i`; equivalently
`‖α_i‖ = p^(-a_i)`. -/
def logShellPaperAlphaElement (π : K) (p e : ℕ) : K :=
  π ^ (if p = 2 then 2 * e else Nat.ceil ((e : ℝ) / ((p : ℝ) - 2)))

/-- The element `α_i` has normalized order `a_i`. -/
theorem norm_logShellPaperAlphaElement (π : Integers K) (hπ : Irreducible π) :
    ‖logShellPaperAlphaElement (π : K) p
        (logShellRamificationExponent (K := K) (p := p))‖ =
      (p : ℝ) ^ (-(logShellPaperAExponent p
        (logShellRamificationExponent (K := K) (p := p)))) := by
  have hepos : (0 : ℝ) <
      (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
    exact_mod_cast logShellRamificationExponent_pos (K := K) (p := p)
  have hfn := norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (K := K) (p := p) π hπ
  have hbase : (0 : ℝ) ≤ (p : ℝ) := by positivity
  unfold logShellPaperAlphaElement
  rw [norm_pow, hfn]
  by_cases hp2 : p = 2
  · simp only [if_pos hp2]
    rw [logShellPaperAExponent]
    simp only [if_pos hp2]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    rw [Nat.cast_mul]
    field_simp [hepos.ne']
    norm_num
  · simp only [if_neg hp2]
    rw [logShellPaperAExponent]
    simp only [if_neg hp2]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    ring

/-- The element form of the lower inclusion: `α_i R_i ⊆ log(R_i^×)`. -/
theorem logShellPaperAlphaElement_smul_integers_subset_unitLogLattice
    (π : Integers K) (hπ : Irreducible π) :
    logShellPaperAlphaElement (π : K) p
        (logShellRamificationExponent (K := K) (p := p)) • (Integers K : Set K) ⊆
      (unitLogLattice (K := K) (p := p) : Set K) := by
  intro x hx
  rcases hx with ⟨r, hr, rfl⟩
  have hrn : ‖r‖ ≤ 1 := (mem_integers_iff (K := K) r).mp hr
  have hnorm : ‖logShellPaperAlphaElement (π : K) p
        (logShellRamificationExponent (K := K) (p := p)) • r‖ ≤
      (p : ℝ) ^ (-(logShellPaperAExponent p
        (logShellRamificationExponent (K := K) (p := p)))) := by
    rw [smul_eq_mul, norm_mul, norm_logShellPaperAlphaElement π hπ]
    calc (p : ℝ) ^ (-(logShellPaperAExponent p
          (logShellRamificationExponent (K := K) (p := p)))) * ‖r‖
        ≤ (p : ℝ) ^ (-(logShellPaperAExponent p
          (logShellRamificationExponent (K := K) (p := p)))) * 1 :=
          mul_le_mul_of_nonneg_left hrn (by positivity)
      _ = _ := mul_one _
  exact padicFractionalLattice_paperA_le_unitLogLattice (K := K) (p := p) hnorm

/-- The paper's upper ramification element `β_i = π^(1 - e B)` with
`B = floor(log_p (p e/(p-1)))`; its normalized order is `-b_i`.
Equivalently `‖β_i‖ = p^(b_i)`. -/
noncomputable def logShellPaperBetaElement (π : K) (p e : ℕ) : K :=
  ((π : K) ^ (Nat.floor (Real.log ((p : ℝ) * (e : ℝ) / ((p : ℝ) - 1)) /
    Real.log (p : ℝ)) * e))⁻¹ * (π : K)

/-- The element `β_i` has normalized order `-b_i`. -/
theorem norm_logShellPaperBetaElement (π : Integers K) (hπ : Irreducible π) :
    ‖logShellPaperBetaElement (π : K) p
        (logShellRamificationExponent (K := K) (p := p))‖ =
      (p : ℝ) ^ (logShellPaperBExponent p
        (logShellRamificationExponent (K := K) (p := p))) := by
  set B := Nat.floor (Real.log ((p : ℝ) *
    (logShellRamificationExponent (K := K) (p := p) : ℝ) / ((p : ℝ) - 1)) /
    Real.log (p : ℝ)) with hB
  have hepos : (0 : ℝ) <
      (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
    exact_mod_cast logShellRamificationExponent_pos (K := K) (p := p)
  have hfn := norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (K := K) (p := p) π hπ
  have hbase : (0 : ℝ) ≤ (p : ℝ) := by positivity
  unfold logShellPaperBetaElement
  dsimp [logShellPaperBExponent]
  rw [← hB]
  rw [norm_mul, norm_inv, norm_pow, hfn]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
  rw [← Real.rpow_neg hbase]
  rw [← Real.rpow_add (by exact_mod_cast (Fact.out : p.Prime).pos : (0 : ℝ) < (p : ℝ))]
  congr 1
  rw [Nat.cast_mul]
  field_simp [hepos.ne']
  ring

/-- The element form of the upper inclusion: `log(R_i^×) ⊆ β_i R_i`. -/
theorem unitLogLattice_subset_logShellPaperBetaElement_smul_integers
    (π : Integers K) (hπ : Irreducible π) :
    (unitLogLattice (K := K) (p := p) : Set K) ⊆
      logShellPaperBetaElement (π : K) p
        (logShellRamificationExponent (K := K) (p := p)) • (Integers K : Set K) := by
  intro x hx
  have hupper : x ∈ padicFractionalLattice (p := p) (K := K)
      (-(logShellPaperBExponent p (logShellRamificationExponent (K := K) (p := p)))) :=
    unitLogLattice_le_padicFractionalLattice_neg_paperB (K := K) (p := p) hx
  rw [mem_padicFractionalLattice_iff] at hupper
  let β := logShellPaperBetaElement (π : K) p
    (logShellRamificationExponent (K := K) (p := p))
  have hβnorm : ‖β‖ = (p : ℝ) ^ (logShellPaperBExponent p
      (logShellRamificationExponent (K := K) (p := p))) :=
    norm_logShellPaperBetaElement π hπ
  have hppos : (0 : ℝ) < (p : ℝ) :=
    by exact_mod_cast (Fact.out : p.Prime).pos
  have hβpos : 0 < ‖β‖ := by
    rw [hβnorm]
    exact Real.rpow_pos_of_pos hppos _
  have hβne : β ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hβpos
    exact lt_irrefl 0 hβpos
  have hxle : ‖x‖ ≤ ‖β‖ := by
    rw [hβnorm]
    simpa using hupper
  refine ⟨x / β, ?_, ?_⟩
  · exact (mem_integers_iff (K := K) (x / β)).mpr (by
      rw [norm_div, div_le_one hβpos]
      exact hxle)
  · change β * (x / β) = x
    field_simp [hβne]

/-- The sharp upper inclusion for odd `p` and `e = 1`: the logarithm of every
actual integral unit lies in `p * O_K`. -/
theorem unitLog_mem_prime_smul_integers_of_odd_unramified
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) (u : (Integers K)ˣ) :
    unitLog u ∈ (p : K) • (Integers K : Set K) := by
  let q := logShellResidueCard (K := K)
  let N := q - 1
  have hq1 : 1 < q := one_lt_logShellResidueCard (K := K) (p := p)
  have hNpos : 0 < N := Nat.sub_pos_of_lt hq1
  have hNne : N ≠ 0 := hNpos.ne'
  have hNneK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hNne
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcard : Nat.card ((logShellResidueField (K := K))ˣ) = N := by
    dsimp [N, q]
    rw [Nat.card_units]
    rfl
  have hpow : integralUnitToLogShellResidueUnits (K := K) (u ^ N) = 1 := by
    have h := pow_card_eq_one' (G := (logShellResidueField (K := K))ˣ)
      (x := integralUnitToLogShellResidueUnits (K := K) u)
    rw [hcard] at h
    simpa only [map_pow] using h
  have hker : u ^ N ∈ (integralUnitToLogShellResidueUnits (K := K)).ker :=
    MonoidHom.mem_ker.mpr hpow
  have hmem : u ^ N ∈ logShellCongruenceUnits (K := K) (p := p) := by
    rwa [integralUnitToLogShellResidueUnits_ker_eq (K := K) (p := p) hp2 hpi] at hker
  have hlog := scaledUnitLog_mem_integers_of_mem_congruence (K := K) (p := p) (u ^ N) hmem
  rw [show logShellScale p = p by simp [logShellScale, hp2]] at hlog
  rw [unitLog_pow (K := K) (p := p)] at hlog
  have hcop : Nat.Coprime p N := by
    dsimp [N, q]
    exact coprime_p_logShellResidueCard_sub_one (K := K) (p := p)
  have hnormN : ‖(N : K)‖ = 1 := by
    calc
      ‖(N : K)‖ = ‖algebraMap ℚ_[p] K (N : ℚ_[p])‖ := by
        simp only [map_natCast]
      _ = ‖(N : ℚ_[p])‖ := norm_algebraMap' K (N : ℚ_[p])
      _ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  have hNinv_mem : ((N : K)⁻¹) ∈ Integers K := by
    apply (mem_integers_iff _).mpr
    rw [norm_inv, hnormN, inv_one]
  have hscaled : (p : K)⁻¹ * unitLog u ∈ Integers K := by
    have hmul : ((N : K)⁻¹) * ((p : K)⁻¹ * ((N : K) * unitLog u)) ∈ Integers K :=
      (Integers K).mul_mem hNinv_mem hlog
    have hEq : ((N : K)⁻¹) * ((p : K)⁻¹ * ((N : K) * unitLog u)) =
        (p : K)⁻¹ * unitLog u := by
      field_simp [hNneK]
    rwa [hEq] at hmul
  refine ⟨(p : K)⁻¹ * unitLog u, hscaled, ?_⟩
  change (p : K) * ((p : K)⁻¹ * unitLog u) = unitLog u
  field_simp [hpne]

/-- The lower inclusion for odd `p` and `e = 1`: `p * O_K` is contained in
the actual logarithm image. -/
theorem prime_smul_integers_subset_unitLog_range
    (hp2 : p ≠ 2) (x : Integers K) :
    (p : K) * (x : K) ∈ Set.range (unitLog (K := K)) := by
  obtain ⟨u, _, hu⟩ := exists_unitLog_eq_scale_mul (K := K) (p := p) x
  refine ⟨u, ?_⟩
  rw [hu, show logShellScale p = p by simp [logShellScale, hp2]]

/-- The sharp `e = 1` equality for odd `p` on the unscaled image. -/
theorem unitLog_range_eq_prime_smul_integers_of_odd_unramified
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    Set.range (unitLog (K := K)) = (p : K) • (Integers K : Set K) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact unitLog_mem_prime_smul_integers_of_odd_unramified (K := K) (p := p) hp2 hpi u
  · rintro _ ⟨x, hx, rfl⟩
    exact prime_smul_integers_subset_unitLog_range (K := K) (p := p) hp2 ⟨x, hx⟩

omit [CompleteSpace K] [ProperSpace K] in
/-- Integer shifts of the integer lattice are the p-adic fractional lattices. -/
theorem prime_pow_smul_integers_eq_padicFractionalLattice (s : ℕ) :
    ((p : K) ^ s) • (Integers K : Set K) =
      (padicFractionalLattice (p := p) (K := K) (s : ℝ) : Set K) := by
  apply Set.ext
  intro x
  rw [show (s : ℝ) = 0 + ((s : ℤ) : ℝ) by norm_num]
  change x ∈ ((p : K) ^ s) • (Integers K : Set K) ↔
    x ∈ padicFractionalLattice (p := p) (K := K) (0 + ((s : ℤ) : ℝ))
  rw [mem_padicFractionalLattice_add_int_iff (p := p) (K := K)
    (a := 0) (k := (s : ℤ))]
  simp only [padicFractionalLattice_zero]
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    rw [zpow_natCast]
    simpa [smul_eq_mul] using hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    rw [zpow_natCast] at hxy
    simpa [smul_eq_mul] using hxy

/-- Unconditional lower inclusion from the actual local inverse theorem:
the paper's scaled lattice `p^s * O_K` is contained in the unscaled unit-log
lattice.  For `e = 1` this is the paper's lower bound `a_i = 1` (odd `p`) or
`a_i = 2` (`p = 2`). -/
theorem padicFractionalLattice_scaleExponent_le_unitLogLattice :
    padicFractionalLattice (p := p) (K := K)
        (logShellScaleExponentFactor (p := p) : ℝ) ≤
      unitLogLattice (K := K) (p := p) := by
  intro x hx
  rw [mem_unitLogLattice_iff]
  change x ∈ (padicFractionalLattice (p := p) (K := K)
    (logShellScaleExponentFactor (p := p) : ℝ) : Set K) at hx
  rw [← prime_pow_smul_integers_eq_padicFractionalLattice (p := p) (K := K)
    (s := logShellScaleExponentFactor (p := p))] at hx
  rcases hx with ⟨y, hy, rfl⟩
  obtain ⟨u, _, hu⟩ := exists_unitLog_eq_scale_mul (K := K) (p := p) ⟨y, hy⟩
  refine ⟨u, ?_⟩
  rw [hu, logShellScale_eq_prime_pow_factor (p := p)]
  simp [smul_eq_mul]

/-- The `e = 1`, odd `p` sharp equality in lattice form. -/
theorem unitLogLattice_eq_padicFractionalLattice_one_of_odd_unramified
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    unitLogLattice (K := K) (p := p) =
      padicFractionalLattice (p := p) (K := K) (1 : ℝ) := by
  apply Submodule.ext
  intro x
  rw [mem_unitLogLattice_iff]
  rw [unitLog_range_eq_prime_smul_integers_of_odd_unramified (K := K) (p := p) hp2 hpi]
  rw [show ((p : K) • (Integers K : Set K)) =
      (padicFractionalLattice (p := p) (K := K) (1 : ℝ) : Set K) by
    simpa using (prime_pow_smul_integers_eq_padicFractionalLattice (p := p) (K := K) (s := 1))]
  rfl

/-- Paper Prop 1.2(i), lower inclusion, `p > 2`, `e = 1`. -/
theorem padicFractionalLattice_one_le_unitLogLattice_of_odd_unramified
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    padicFractionalLattice (p := p) (K := K) (1 : ℝ) ≤
      unitLogLattice (K := K) (p := p) := by
  rw [unitLogLattice_eq_padicFractionalLattice_one_of_odd_unramified (K := K) (p := p) hp2 hpi]

/-- Paper Prop 1.2(i), upper inclusion, `p > 2`, `e = 1`
(`b_i = -1`). -/
theorem unitLogLattice_le_padicFractionalLattice_neg_one_of_odd_unramified
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    unitLogLattice (K := K) (p := p) ≤
      padicFractionalLattice (p := p) (K := K) (-1 : ℝ) := by
  rw [unitLogLattice_eq_padicFractionalLattice_one_of_odd_unramified (K := K) (p := p) hp2 hpi]
  exact padicFractionalLattice_antitone (p := p) (K := K) (by norm_num : (-1 : ℝ) ≤ 1)

/-- For `p = 2`, the paper's lower exponent is `a_i = 2`, independent of
the ramification exponent. -/
theorem padicFractionalLattice_two_le_unitLogLattice_of_two (hp : p = 2) :
    padicFractionalLattice (p := p) (K := K) (2 : ℝ) ≤
      unitLogLattice (K := K) (p := p) := by
  subst p
  exact
    (padicFractionalLattice_scaleExponent_le_unitLogLattice (K := K) (p := 2))

/-- The same `p = 2` lower bound stated with the paper's `a_i`. -/
theorem padicFractionalLattice_paperA_two_le_unitLogLattice
    (hp : p = 2) (e : ℕ) :
    padicFractionalLattice (p := p) (K := K) (logShellPaperAExponent p e) ≤
      unitLogLattice (K := K) (p := p) := by
  subst p
  simpa [logShellPaperAExponent] using
    (padicFractionalLattice_two_le_unitLogLattice_of_two (K := K) (p := 2) rfl)

end

end LeanFormal.IUT.LocalFieldLogarithm
