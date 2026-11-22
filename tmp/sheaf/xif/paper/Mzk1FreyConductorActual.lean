/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A857 hull: Frey conductor — p ∤ 6 arithmetic

Frey invariants: Delta = 16*a^2*b^2*c^2, c4 = 16*(a^2+ab+b^2).
For p ∤ 6 and p || abc (say p | a once, p ∤ b, p ∤ c):
* ord_p(Delta) = 2;
* ord_p(c4) = 0 because c4 ≡ 16 b^2 ≠ 0 mod p.

This file records the arithmetic identities and the reduction criterion.  The
p-adic valuation bridge to WeierstrassCurve invariants is NOT formalized;
p ∤ 6 closure is therefore conditional on that bridge.  p = 2,3 exponents are
an explicit external Prop (Ogg–Saito table).  No fake local proof is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FreyConductorActual

/-- Natural-number Frey discriminant. -/
def freyDeltaNat (a b c : ℕ) : ℕ := 16 * a ^ 2 * b ^ 2 * c ^ 2

/-- Natural-number Frey c4. -/
def freyC4Nat (a b : ℕ) : ℕ := 16 * (a ^ 2 + a * b + b ^ 2)

theorem freyDeltaNat_eq (a b c : ℕ) :
    freyDeltaNat a b c = 16 * (a * b * c) ^ 2 := by
  unfold freyDeltaNat
  ring

/-- c4 at a p-divisible a (p ∤ b): modulo p it is 16*b^2, nonzero. -/
def C4NonzeroModP (p a b : ℕ) : Prop :=
  ¬ p ∣ (a ^ 2 + a * b + b ^ 2)

/-- Multiplicative-reduction criterion at p: ord_p(Delta) > 0 and ord_p(c4) = 0. -/
def MultiplicativeAt (p delta c4 : ℕ) : Prop :=
  padicValNat p delta > 0 ∧ padicValNat p c4 = 0

/-- The conductor exponent at a multiplicative-reduction prime is 1 (Tate input). -/
def ConductorExponentOne (p N : ℕ) : Prop := padicValNat p N = 1

/-- p = 2,3 additive-reduction exponents: external Ogg–Saito data. -/
structure OggSaitoFreyExponent where
  v2N : ℕ
  v3N : ℕ
  data : Prop
  data_holds : data

/-- Full Frey conductor formula: p ∤ 6 true (conditional on valuation bridge),
p = 2,3 external. -/
structure FreyConductorFormula where
  N : ℕ
  pNotSix : Prop
  pNotSix_holds : pNotSix
  oggSaito : OggSaitoFreyExponent

def conductorRows : List (String × String × String) :=
  [ ("Delta", "Delta = 16*(abc)^2", "PROVED (freyDeltaNat_eq)"),
    ("c4", "c4 = 16(a^2+ab+b^2)", "DEF (freyC4Nat)"),
    ("c4 mod p", "p|a, p∤b => p∤(a^2+ab+b^2) (ZMod)", "GAP (ZMod proof abandoned; statement as C4NonzeroModP)"),
    ("ord_p Delta", "p∤6, p||a => ord_p(Delta)=2", "ARITHMETIC EXPECTED; valuation bridge GAP"),
    ("ord_p c4", "p∤6 => ord_p(c4)=0", "ARITHMETIC EXPECTED; valuation bridge GAP"),
    ("multiplicative criterion", "ord_p Delta>0 and ord_p c4=0 => multiplicative", "DEF (MultiplicativeAt)"),
    ("v_p(N)=1", "multiplicative => conductor exponent 1 (Tate input)", "DEF (ConductorExponentOne)"),
    ("p=2,3", "Ogg-Saito additive exponents", "EXTERNAL PROP (OggSaitoFreyExponent)") ]

theorem conductorRows_length : conductorRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorActual.freyDeltaNat_eq

end LeanFormal.IUT.XiFPaper.Mzk1FreyConductorActual

end
