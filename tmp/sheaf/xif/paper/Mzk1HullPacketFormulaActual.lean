/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A814 hull: arithmetic formulas for `hullPacket` and the procession average

Extracted from lana `Iut/WallEquiv/VcI.lean` (read-only source):
* `hullPacket_finite` (:806):
  `hullPacket i (.finite p) = Σ_c w_c · (Σ_j ρ_{cj} · log p)`;
* `hullPacket_tame` (:844):
  `= Σ_c w_c · (Σ_j (1 − 1/e_{cj}) · log p)` at tame primes;
* `logVol_hull_vcI_eq` (:741):
  `logVol(hull(VC(I))) = (Σ_i Σ^f_vQ hullPacket i vQ) / nC`.

Here we replicate the arithmetic (no lana import) and record posable upper
bounds used by the volume upper direction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullPacketFormulaActual

open scoped BigOperators

/-- `hullPacket_finite` arithmetic: `Σ_c w_c · Σ_j ρ_{cj} · log p`. -/
def hullPacketFinite {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (rho : C → J → ℝ) (logp : ℝ) : ℝ :=
  ∑ c, w c * (∑ j, rho c j * logp)

/-- `hullPacket_tame` arithmetic: `Σ_c w_c · Σ_j (1 − 1/e_{cj}) · log p`. -/
def hullPacketTame {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (e : C → J → ℝ) (logp : ℝ) : ℝ :=
  ∑ c, w c * (∑ j, (1 - 1 / e c j) * logp)

theorem hullPacketFinite_eq {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (rho : C → J → ℝ) (logp : ℝ) :
    hullPacketFinite w rho logp = ∑ c, w c * (∑ j, rho c j * logp) := rfl

theorem hullPacketTame_eq {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (e : C → J → ℝ) (logp : ℝ) :
    hullPacketTame w e logp = ∑ c, w c * (∑ j, (1 - 1 / e c j) * logp) := rfl

/-- Positivity of the finite formula under nonnegative data. -/
theorem hullPacketFinite_nonneg {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (rho : C → J → ℝ) (logp : ℝ)
    (hw : ∀ c, 0 ≤ w c) (hrho : ∀ c j, 0 ≤ rho c j) (hlogp : 0 ≤ logp) :
    0 ≤ hullPacketFinite w rho logp := by
  unfold hullPacketFinite
  exact Finset.sum_nonneg fun c _ =>
    mul_nonneg (hw c) (Finset.sum_nonneg fun j _ => mul_nonneg (hrho c j) hlogp)

/-- Tame upper: every label contributes at most `log p`, so
`hullPacketTame <= Σ_c w_c · (#J) · log p` for `e >= 1`. -/
theorem hullPacketTame_le {C J : Type*} [Fintype C] [Fintype J]
    (w : C → ℝ) (e : C → J → ℝ) (logp : ℝ)
    (hw : ∀ c, 0 ≤ w c) (he : ∀ c j, 1 ≤ e c j) (hlogp : 0 ≤ logp) :
    hullPacketTame w e logp ≤ ∑ c, w c * ((Fintype.card J : ℝ) * logp) := by
  unfold hullPacketTame
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (hw c)
  have hterm : ∀ j, (1 - 1 / e c j) * logp ≤ logp := by
    intro j
    have hcoef : 1 - 1 / e c j ≤ 1 := by
      have hpos : 0 < e c j := lt_of_lt_of_le zero_lt_one (he c j)
      have h : 0 ≤ 1 / e c j := by positivity
      linarith
    simpa using mul_le_mul_of_nonneg_right hcoef hlogp
  calc (∑ j, (1 - 1 / e c j) * logp) ≤ ∑ j, logp := Finset.sum_le_sum fun j _ => hterm j
    _ = (Fintype.card J : ℝ) * logp := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `logVol_hull_vcI_eq` arithmetic: `(Σ_i Σ^f_vQ hullPacket i vQ) / nC`. -/
def logVolHullVcI {I V : Type*} [Fintype I] [Fintype V]
    (hullPacket : I → V → ℝ) (nC : ℝ) : ℝ :=
  (∑ i, ∑ v, hullPacket i v) / nC

theorem logVolHullVcI_eq {I V : Type*} [Fintype I] [Fintype V]
    (hullPacket : I → V → ℝ) (nC : ℝ) :
    logVolHullVcI hullPacket nC = (∑ i, ∑ v, hullPacket i v) / nC := rfl

/-- Global upper from a per-packet bound: if every (i,vQ) packet is at most `B`,
`logVolHullVcI <= (card I * card V * B)/nC`. -/
theorem logVolHullVcI_le_of_packet_le {I V : Type*} [Fintype I] [Fintype V]
    (hullPacket : I → V → ℝ) (nC B : ℝ) (hnC : 0 < nC)
    (h : ∀ i v, hullPacket i v ≤ B) :
    logVolHullVcI hullPacket nC ≤ ((Fintype.card I : ℝ) * (Fintype.card V : ℝ) * B) / nC := by
  unfold logVolHullVcI
  have hsum : (∑ i, ∑ v, hullPacket i v) ≤
      ∑ i : I, ∑ v : V, B := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro v _
    exact h i v
  have hsum2 : (∑ i : I, ∑ v : V, B) = (Fintype.card I : ℝ) * (Fintype.card V : ℝ) * B := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  rw [hsum2] at hsum
  exact div_le_div_of_nonneg_right hsum hnC.le

def hullPacketRows : List (String × String × String) :=
  [ ("hullPacket_finite", "Σ_c w_c Σ_j ρ_{cj} log p", "LANA GREEN (VcI.lean:806); arithmetic DEF here"),
    ("hullPacket_tame", "Σ_c w_c Σ_j (1-1/e_{cj}) log p", "LANA GREEN (VcI.lean:844); arithmetic DEF here"),
    ("logVol_hull_vcI", "(Σ_i Σ^f hullPacket)/nC", "LANA GREEN (VcI.lean:741); arithmetic DEF here"),
    ("positivity", "nonnegative weights/radii => hullPacketFinite >= 0", "PROVED (hullPacketFinite_nonneg)"),
    ("tame upper", "e>=1 => hullPacketTame <= Σ_c w_c (#J log p)", "PROVED (hullPacketTame_le)"),
    ("global upper", "per-packet <= B => logVol <= (card I card V B)/nC", "PROVED (logVolHullVcI_le_of_packet_le)"),
    ("volume use", "tame hull packet bounds feed the volume upper direction V <= (1/4)l logdf + C0", "PARTIAL (needs paper data identification)") ]

theorem hullPacketRows_length : hullPacketRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullPacketFormulaActual.hullPacketTame_le
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullPacketFormulaActual.logVolHullVcI_le_of_packet_le

end LeanFormal.IUT.XiFPaper.Mzk1HullPacketFormulaActual

end