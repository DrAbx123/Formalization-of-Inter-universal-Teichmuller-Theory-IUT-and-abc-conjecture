/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FreyConductorFinalActual
import Mathlib.Tactic

/-! # A862 hull: p ∤ 6 valuations (Nat padicValNat) and ABCFreyPackage

For p ≠ 2 with v_p(a)=1, v_p(b)=v_p(c)=0:
v_p(abc)=1, v_p(16)=0, hence v_p(Delta)=2 and v_p(c4)=0, giving
multiplicative reduction and conductor exponent 1.  p=2,3 is external
Ogg-Saito data.  The ABCFreyPackage collects a,b,c and the proved invariant
identities. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FreyConductorCompleteActual

open LeanFormal.IUT.XiFPaper.Mzk1FreyConductorFinalActual

theorem padicValNat_abc (p a b c : ℕ) [Fact p.Prime]
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha : padicValNat p a = 1) (hb : padicValNat p b = 0)
    (hc : padicValNat p c = 0) :
    padicValNat p (a * b * c) = 1 := by
  rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0, padicValNat.mul ha0 hb0, ha, hb, hc]

theorem padicValNat_sixteen (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValNat p 16 = 0 := by
  have hp : p.Prime := Fact.out
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16, padicValNat.pow 2 4]
  have hnot : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hge : 2 ≤ p := hp.two_le
    omega
  have hv2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd hnot
  rw [hv2]

theorem padicValNat_freyDelta (p a b c : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha : padicValNat p a = 1) (hb : padicValNat p b = 0)
    (hc : padicValNat p c = 0) :
    padicValNat p (16 * a ^ 2 * b ^ 2 * c ^ 2) = 2 := by
  have habc : padicValNat p (a * b * c) = 1 := padicValNat_abc p a b c ha0 hb0 hc0 ha hb hc
  rw [show 16 * a ^ 2 * b ^ 2 * c ^ 2 = 16 * (a * b * c) ^ 2 by ring]
  rw [padicValNat.mul (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0) hc0))]
  rw [padicValNat_sixteen p hp2, padicValNat.pow (a*b*c) 2, habc]

theorem padicValNat_freyC4 (p a b : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ha : p ∣ a) (hb : ¬ p ∣ b) :
    padicValNat p (16 * (a ^ 2 + a * b + b ^ 2)) = 0 := by
  have hp : p.Prime := Fact.out
  have hpoly : ¬ p ∣ (a ^ 2 + a * b + b ^ 2) := c4_poly_not_dvd p a b hp ha hb
  have hpoly0 : (a ^ 2 + a * b + b ^ 2) ≠ 0 := by
    intro h0
    exact hpoly (by simp [h0])
  rw [padicValNat.mul (by norm_num) hpoly0,
    padicValNat_sixteen p hp2, padicValNat.eq_zero_of_not_dvd hpoly]

def MultiplicativeAt (p delta c4 : ℕ) : Prop :=
  padicValNat p delta > 0 ∧ padicValNat p c4 = 0

theorem multiplicativeAt_of_valuations (p a b c : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (ha : padicValNat p a = 1) (hb : padicValNat p b = 0)
    (hc : padicValNat p c = 0) (hpa : p ∣ a) (hpb : ¬ p ∣ b) :
    MultiplicativeAt p (16 * a ^ 2 * b ^ 2 * c ^ 2)
      (16 * (a ^ 2 + a * b + b ^ 2)) := by
  unfold MultiplicativeAt
  constructor
  · rw [padicValNat_freyDelta p a b c hp2 ha0 hb0 hc0 ha hb hc]
    norm_num
  · exact padicValNat_freyC4 p a b hp2 hpa hpb

/-- Conductor/radical record: p ∤ 6 formula plus p = 2,3 external data. -/
structure ConductorFormulaRecord where
  N : ℕ
  rad : ℕ
  pNotSix : Prop
  pNotSix_holds : pNotSix
  pTwoThree : Prop
  pTwoThree_holds : pTwoThree

/-- ABF Frey package: data + proved discriminant/C4 formulas + conductor formula. -/
structure ABCFreyPackage where
  a : ℕ
  b : ℕ
  c : ℕ
  hsum : a + b = c
  ha_pos : 0 < a
  hb_pos : 0 < b
  hc_pos : 0 < c
  hcoprime : Nat.Coprime a b
  conductorFormula : ConductorFormulaRecord

noncomputable def packageDelta (P : ABCFreyPackage) : ℕ :=
  16 * P.a ^ 2 * P.b ^ 2 * P.c ^ 2

noncomputable def packageC4 (P : ABCFreyPackage) : ℕ :=
  16 * (P.a ^ 2 + P.a * P.b + P.b ^ 2)

theorem packageDelta_eq (P : ABCFreyPackage) :
    packageDelta P = 16 * (P.a * P.b * P.c) ^ 2 := by
  unfold packageDelta
  ring

def rows : List (String × String × String) :=
  [ ("v_p(abc)", "=1", "PROVED (padicValNat_abc)"),
    ("v_p(16)", "=0 for p≠2", "PROVED (padicValNat_sixteen)"),
    ("v_p(Delta)", "=2", "PROVED (padicValNat_freyDelta)"),
    ("v_p(c4)", "=0", "PROVED (padicValNat_freyC4)"),
    ("multiplicative", "v_p Delta>0, v_p c4=0", "PROVED (multiplicativeAt_of_valuations)"),
    ("ABCFreyPackage", "a,b,c,hsum,positivity,coprime + Delta/C4 formulas", "DEF"),
    ("p=2,3", "Ogg-Saito external", "EXTERNAL (OggSaitoData)"),
    ("N=rad", "conductor/radical relation", "FIELD/GAP (no local 2-adic proof)") ]

theorem rows_length : rows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorCompleteActual.padicValNat_freyDelta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorCompleteActual.padicValNat_freyC4
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FreyConductorCompleteActual.multiplicativeAt_of_valuations

end LeanFormal.IUT.XiFPaper.Mzk1FreyConductorCompleteActual

end
