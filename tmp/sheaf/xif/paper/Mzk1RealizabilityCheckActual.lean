import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # A800 realizability check: `e = 1` and `r = n` cannot coexist

Data: `e` = local ramification index (`v_K(p)`), `n` = local degree
`[K_v : Q_p]`, `r` = normalized count of nontrivial p-power roots of unity.

Green references from `LeanFormal/IUT/Foundations/LocalFields/`:
* `logShellRamificationExponent_pos : 0 < e`
  (`IntegralLogShellRamificationInertia.lean`);
* local degree `n = Module.finrank ℚ_[p] K`; the degree identity `n = e * f`
  is the standard `Ideal.sum_ramification_inertia_eq_finrank` used in
  `IUTIV/Estimates/ArithmeticDivisorDegree.lean`;
* `logShellResidueCard = p ^ f` in
  `IntegralLogShellIndexResidueFormula.lean`.

The missing formalized arithmetic is the local-field fact: `e = 1` (unramified)
implies that every p-power root of unity in `K_v` is trivial, hence `r = 0`
(otherwise `Q_p(zeta_p)` would be a ramified subextension, forcing `p - 1 | e`).
We record that fact as the named input `UnramifiedNoPPowerRoot` and prove the
resulting exclusion shape. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RealizabilityCheckActual

/-- Local C3/Theta-data invariants at one place. -/
structure LocalC3PlaceData where
  e : Nat
  n : Nat
  r : Nat
  e_pos : 0 < e
  n_pos : 0 < n

/-- Named local-field input: unramified (`e = 1`) forces `r = 0`. -/
def UnramifiedNoPPowerRoot (D : LocalC3PlaceData) : Prop :=
  D.e = 1 → D.r = 0

theorem unramified_r_zero (D : LocalC3PlaceData)
    (hunram : UnramifiedNoPPowerRoot D) (he : D.e = 1) : D.r = 0 :=
  hunram he

/-- Exclusion shape: `e = 1` and `r = n` cannot both hold. -/
theorem not_e1_and_r_eq_n (D : LocalC3PlaceData)
    (hunram : UnramifiedNoPPowerRoot D) (he : D.e = 1) (hrn : D.r = D.n) : False := by
  have hr : D.r = 0 := unramified_r_zero D hunram he
  have hn : D.n = 0 := by omega
  exact Nat.lt_irrefl 0 (hn ▸ D.n_pos)

/-- Consequently `e = 1` excludes the ratio `r/n = 1`. -/
theorem not_e1_and_ratio_one (D : LocalC3PlaceData)
    (hunram : UnramifiedNoPPowerRoot D) (he : D.e = 1)
    (hratio : (D.r : Real) / (D.n : Real) = 1) : False := by
  have hn0 : (D.n : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp D.n_pos)
  have hrn : (D.r : Real) = D.n := by
    field_simp at hratio
    exact_mod_cast hratio
  exact not_e1_and_r_eq_n D hunram he (by exact_mod_cast hrn)

#print axioms not_e1_and_ratio_one

end LeanFormal.IUT.XiFPaper.Mzk1RealizabilityCheckActual
