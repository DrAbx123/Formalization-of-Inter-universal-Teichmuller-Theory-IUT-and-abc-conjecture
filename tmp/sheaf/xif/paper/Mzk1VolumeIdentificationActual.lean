/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullPacketFormulaActual
import tmp.sheaf.xif.paper.Mzk1StepVVolumeUpperActual
import Mathlib.Tactic

/-! # A821 hull: volume identification `V = stepVExpr`

Tame case: the hull volume is the procession average of the tame hull packets
  `Σ_i (1/nC) Σ_c w_c Σ_j (1 − 1/e_{cj}) log p`,
which is exactly the tame `hullPacket` formula replicated in
`Mzk1HullPacketFormulaActual`.  General case: `V` must be identified with
`stepVExpr = (−floor(λ−Σdiff−ΣA)+ΣB)·log p`; the Section-1 bookkeeping
(`S = log s^Q`, `T = l*_mod log s≤`, `λ`, `Σdiff`) is not yet green, so the
general identification remains an explicit hypothesis. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationActual

open LeanFormal.IUT.XiFPaper.Mzk1HullPacketFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open scoped BigOperators

/-- Procession average over `n` capsules. -/
def processionAverage (n : ℕ) (f : Fin n → ℝ) : ℝ :=
  (∑ i, f i) / (n : ℝ)

theorem processionAverage_eq (n : ℕ) (f : Fin n → ℝ) :
    processionAverage n f = (∑ i, f i) / (n : ℝ) := rfl

/-- Tame hull volume: procession average of the tame hull packets (per capsule). -/
def tameHullVolume {C J : Type*} [Fintype C] [Fintype J] (n : ℕ)
    (w : Fin n → C → ℝ) (e : Fin n → C → J → ℝ) (logp : ℝ) : ℝ :=
  processionAverage n (fun i => hullPacketTame (w i) (e i) logp)

/-- **Tame identification**: the tame hull volume is the procession average of the
tame `hullPacket` formula (definitional unfolding). -/
theorem tameHullVolume_eq (n : ℕ) (hn : 0 < n)
    {C J : Type*} [Fintype C] [Fintype J]
    (w : Fin n → C → ℝ) (e : Fin n → C → J → ℝ) (logp : ℝ) :
    tameHullVolume n w e logp =
      (∑ i : Fin n, hullPacketTame (w i) (e i) logp) / (n : ℝ) := rfl

/-- Tame upper: each capsule's tame hull packet is at most `Σ_c w_c (#J logp)`. -/
theorem tameHullVolume_le (n : ℕ) (hn : 0 < n)
    {C J : Type*} [Fintype C] [Fintype J]
    (w : Fin n → C → ℝ) (e : Fin n → C → J → ℝ) (logp : ℝ)
    (hw : ∀ i c, 0 ≤ w i c) (he : ∀ i c j, 1 ≤ e i c j) (hlogp : 0 ≤ logp) :
    tameHullVolume n w e logp ≤ 
      (∑ i : Fin n, ∑ c, w i c * ((Fintype.card J : ℝ) * logp)) / (n : ℝ) := by
  unfold tameHullVolume processionAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  exact hullPacketTame_le (w i) (e i) logp (hw i) (he i) hlogp

/-- General identification predicate: the actual hull volume equals the Step-V
log-volume expression.  This is the open object identification; it is NOT
asserted as a theorem. -/
def VolumeIdentification (V stepV : ℝ) : Prop := V = stepV

theorem volumeIdentification_iff (V stepV : ℝ) :
    VolumeIdentification V stepV ↔ V = stepV := Iff.rfl

/-- Conditional general identification: if the hull volume equals the Step-V
expression and the Step-V bound holds, the paper box follows (interface only). -/
theorem volume_upper_of_general_identification
    (V floorTerm sumB lambda sumDiff logp exceptional l logd logf C0 : ℝ)
    (hident : VolumeIdentification V (stepVExpr floorTerm sumB logp))
    (hstep : stepVExpr floorTerm sumB logp ≤ stepVRHS lambda sumDiff logp exceptional)
    (hbox : stepVRHS lambda sumDiff logp exceptional ≤ paperBox l logd logf C0) :
    V ≤ paperBox l logd logf C0 := by
  unfold VolumeIdentification at hident
  rw [hident]
  linarith

def volumeIdentRows : List (String × String × String) :=
  [ ("tame V", "procession average of tame hullPacket = Σ_i (1/n)Σ_c w_c Σ_j (1-1/e)logp", "PROVED (tameHullVolume_eq)"),
    ("tame upper", "tame V <= (Σ_i Σ_c w_c (#J logp))/n", "PROVED (tameHullVolume_le)"),
    ("general V=stepVExpr", "V = (-floor(λ-Σdiff-ΣA)+ΣB)logp", "GAP (object identification)"),
    ("Section1 S", "S = log s^Q (needed to identify lambda/diff with D=log d^K)", "GAP (no green)"),
    ("Section1 T", "T = l*_mod log s<= ; recovery via StepVProcessionAverage.exceptionalSum_le_r4", "GAP (green cited but not object-identified)"),
    ("lambda/sumDiff", "identify lambda and Σdiff with paper D terms", "GAP"),
    ("conditional interface", "VolumeIdentification + stepV bound + box => V <= paperBox", "PROVED (volume_upper_of_general_identification)") ]

theorem volumeIdentRows_length : volumeIdentRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationActual.tameHullVolume_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationActual.tameHullVolume_le
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationActual.volume_upper_of_general_identification

end LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationActual

end