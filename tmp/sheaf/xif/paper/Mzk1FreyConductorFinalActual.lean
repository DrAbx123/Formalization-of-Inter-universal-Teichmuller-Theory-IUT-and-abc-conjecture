/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A861 hull: Frey conductor p ∤ 6 — ZMod-free c4 proof

Frey invariants Delta = 16 a^2 b^2 c^2, c4 = 16(a^2+ab+b^2).
For p | a and p ∤ b, p ∤ (a^2+ab+b^2): reduce to p | b^2, contradicting
p ∤ b (Nat divisibility, no ZMod).  The p-adic valuations of Delta and c4
remain explicit fields (valuation bridge to WeierstrassCurve invariants is not
formalized); p = 2,3 is external Ogg-Saito data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FreyConductorFinalActual

def freyDeltaNat (a b c : ℕ) : ℕ := 16 * a ^ 2 * b ^ 2 * c ^ 2

def freyC4Nat (a b : ℕ) : ℕ := 16 * (a ^ 2 + a * b + b ^ 2)

theorem freyDeltaNat_eq (a b c : ℕ) :
    freyDeltaNat a b c = 16 * (a * b * c) ^ 2 := by
  unfold freyDeltaNat
  ring

/-- p ∤ a^2+ab+b^2 when p | a and p ∤ b. -/
theorem c4_poly_not_dvd (p a b : ℕ) (hp : p.Prime) (ha : p ∣ a) (hb : ¬ p ∣ b) :
    ¬ p ∣ (a ^ 2 + a * b + b ^ 2) := by
  intro h
  have h1 : p ∣ a ^ 2 := by
    have := dvd_mul_of_dvd_left ha a
    simpa [pow_two] using this
  have h2 : p ∣ a * b := dvd_trans ha (dvd_mul_right a b)
  have hsum : p ∣ a ^ 2 + a * b := dvd_add h1 h2
  have hb2 : p ∣ b ^ 2 := by
    have h' : p ∣ (a ^ 2 + a * b) + b ^ 2 := by simpa [Nat.add_assoc] using h
    have hsub := Nat.dvd_sub h' hsum
    simpa using hsub
  exact hb ((hp.dvd_of_dvd_pow hb2 : p ∣ b))

/-- Multiplicative-reduction local data (Delta/c4 valuations are explicit fields;
the arithmetic reduction to padicValNat is not formalized). -/
structure LocalMultiplicativeData (p delta c4 : ℕ) where
  deltaValuation : padicValNat p delta = 2
  c4Valuation : padicValNat p c4 = 0
  multiplicative : Prop
  multiplicative_holds : multiplicative

/-- conductor exponent 1 from multiplicative reduction (Tate input). -/
def ConductorExponentOne (p N : ℕ) : Prop := padicValNat p N = 1

/-- p=2,3 Ogg-Saito exponents (external). -/
structure OggSaitoData where
  v2N : ℕ
  v3N : ℕ
  data : Prop
  data_holds : data

def rows : List (String × String × String) :=
  [ ("Delta", "16(abc)^2", "PROVED (freyDeltaNat_eq)"),
    ("c4", "16(a^2+ab+b^2)", "DEF"),
    ("c4 divisibility", "p|a, p not b => p not (a^2+ab+b^2)", "PROVED (c4_poly_not_dvd)"),
    ("Delta valuation", "ord_p(Delta)=2", "FIELD (LocalMultiplicativeData.deltaValuation); arithmetic bridge GAP"),
    ("c4 valuation", "ord_p(c4)=0", "FIELD (LocalMultiplicativeData.c4Valuation); arithmetic bridge GAP"),
    ("multiplicative", "ord_p Delta>0 and ord_p c4=0", "FIELD (multiplicative Prop)"),
    ("conductor exponent", "v_p(N)=1", "DEF (ConductorExponentOne); Tate input"),
    ("p=2,3", "Ogg-Saito exponents", "EXTERNAL (OggSaitoData)") ]

theorem rows_length : rows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorFinalActual.freyDeltaNat_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorFinalActual.c4_poly_not_dvd

end LeanFormal.IUT.XiFPaper.Mzk1FreyConductorFinalActual

end
