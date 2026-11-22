/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A915 / route C stage C0: Ind2 term and archDefect — precise statements and provable parts -/

/- CONTEXT (lana `Iut/WallEquiv/Gap.lean`, root tree, read-only; oleans not built here):
* `ind2Term` enters `gapHullAt`: the hull enlargement by the (Ind2)-union of the images of
  `q^{j^2} * tensor log-shell`.  File header (Gap.lean:30-36): the Ind2 automorphisms at a
  prime are `tensorAut` (Z_p-lattice automorphisms of the factor log-shells) and 'need not
  commute with the theta values'; `ind2Term_nonneg`; `ind2Term_eq_zero` away from bad residue
  characteristics; whether the Ind2 terms at bad primes are 0 or > 0 is OPEN.
  The paper formula for the Ind2 term (fractional part of the theta exponent) is
  `frac(j^2 * v_p(q) / (2l)) * log p`; we record it as a model with explicit fractional-part
  data and prove the elementary properties.  The exact derivation from `tensorAut` is NOT
  available without the lana cube/commutation lemmas (precise gap below).
* `archDefect` (Gap.lean:459) is defined as `componentVol leastHull(logShell) -
  componentVol logShell`; only `archDefect_nonneg` (Gap.lean:463) is proved in lana.  The
  EXACT value `log((2^{N-1})!)/2^N` for a packet of N complex factors is stated in the file
  header (Gap.lean:66) as 'not formalized here'.  We formalize the formula as data and prove
  its nonnegativity; the identification with `archDefect` is the precise remaining gap. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C0Ind2ArchActual

/-- Model of the Ind2 term: fractional part of the theta exponent times `log p`. -/
structure Ind2Data where
  fracPart : ℝ
  frac_nonneg : 0 ≤ fracPart
  frac_lt_one : fracPart < 1
  logp : ℝ
  logp_pos : 0 < logp

def ind2Term (D : Ind2Data) : ℝ := D.fracPart * D.logp

theorem ind2Term_nonneg (D : Ind2Data) : 0 ≤ ind2Term D := by
  unfold ind2Term
  exact mul_nonneg D.frac_nonneg D.logp_pos.le

theorem ind2Term_lt_logp (D : Ind2Data) : ind2Term D < D.logp := by
  unfold ind2Term
  have h : D.fracPart * D.logp < 1 * D.logp := by
    exact mul_lt_mul_of_pos_right D.frac_lt_one D.logp_pos
  simpa using h

theorem ind2Term_eq_zero_iff (D : Ind2Data) : ind2Term D = 0 ↔ D.fracPart = 0 := by
  unfold ind2Term
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt D.logp_pos)
  · intro h
    rw [h, zero_mul]

theorem ind2Term_pos_iff (D : Ind2Data) : 0 < ind2Term D ↔ 0 < D.fracPart := by
  unfold ind2Term
  constructor
  · intro h
    by_contra hc
    have hz : D.fracPart = 0 := le_antisymm (not_lt.mp hc) D.frac_nonneg
    rw [hz, zero_mul] at h
    exact lt_irrefl 0 h
  · intro h
    exact mul_pos h D.logp_pos

/-- Archimedean defect model: formula `log((2^{N-1})!)/2^N` (Gap.lean:66). -/
structure ArchDefectData where
  N : ℕ
  value : ℝ
  formula : value = Real.log ((Nat.factorial (2 ^ (N - 1)) : ℝ)) / (2 ^ N : ℝ)

theorem archDefect_model_nonneg (A : ArchDefectData) : 0 ≤ A.value := by
  rw [A.formula]
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos _).ne'
  · positivity

/-- The exact-value identification gap recorded as a predicate (not assumed, not proved). -/
def ArchDefectValueGap (archDefectValue : ℝ) (formulaValue : ℝ) : Prop :=
  archDefectValue = formulaValue

def c0Rows : List (String × String × String) :=
  [ ("ind2Term formula", "frac(j^2 v_p(q)/(2l)) log p (paper form)", "MODEL (data)") ,
    ("ind2Term_nonneg", "0 <= fracPart * logp", "PROVED") ,
    ("ind2Term_lt_logp", "ind2Term < log p", "PROVED") ,
    ("ind2Term_eq_zero_iff / pos", "zero iff fracPart=0; positive iff fracPart>0", "PROVED") ,
    ("derivation from tensorAut/commutation", "Gap.lean:30-36 cube lemmas", "GAP (lana oleans)") ,
    ("archDefect exact value", "log((2^{N-1})!)/2^N (Gap.lean:66 header)", "MODEL (data); NOT formalized in lana") ,
    ("archDefect_model_nonneg", "formula value >= 0", "PROVED") ,
    ("archDefect = formula", "identification", "GAP (precise: need lana cube/orthogonality)") ]

theorem c0Rows_length : c0Rows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C0Ind2ArchActual
