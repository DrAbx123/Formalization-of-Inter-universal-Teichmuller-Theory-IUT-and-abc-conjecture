/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionAverageActual
import Mathlib.Tactic

/-! # A851 hull: self-contained L5 (no lana import)

`DExact` is the paper-normalized per-place weighted hull datum:
`DExact = Σ_v weight_v·h_v·logp_v` (plus a separate arch/infinity addend).
`VHull` is the procession average of the capsule contributions, where capsule
`i` (labels `j = 1..nC`) contributes `(j+1)·DExact`, i.e. `(i+2)·DExact`.

Proved from the L4 average (`Mzk1ProcessionAverageActual.avgJPlusOne_eq_l`):

  `VHull = ((l+5)/4)·DExact`  at `l = 2·nC+1`.

This replaces A849's conditional version and does not import any unbuilt lana
olean; provenance: lana `IdentifiedCopies.logVol_lgp` / `logVol_lgp_integral`
(source only). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1L5SelfContainedActual

open LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual
open scoped BigOperators

/-- Paper `D_exact`: weighted hull datum over places. -/
def DExact {ι : Type*} [Fintype ι] (weight h logp : ι → ℝ) : ℝ :=
  ∑ v, weight v * h v * logp v

theorem DExact_eq {ι : Type*} [Fintype ι] (weight h logp : ι → ℝ) :
    DExact weight h logp = ∑ v, weight v * h v * logp v := rfl

/-- Procession average of capsule terms. -/
def VHull (nC : ℕ) (term : Fin nC → ℝ) : ℝ :=
  (1 / (nC : ℝ)) * ∑ i, term i

theorem VHull_eq (nC : ℕ) (term : Fin nC → ℝ) :
    VHull nC term = (1 / (nC : ℝ)) * ∑ i, term i := rfl

/-- **Capsule factor hypothesis**: capsule `i` contributes `(j+1)·D = (i+2)·D`. -/
def CapsuleFactor (nC : ℕ) (term : Fin nC → ℝ) (D : ℝ) : Prop :=
  ∀ i, term i = ((i : ℝ) + 2) * D

/-- Sum of capsule factors: `Σ_i (i+2) = nC*(nC+3)/2`. -/
theorem sum_fin_add_two (nC : ℕ) :
    (∑ i : Fin nC, ((i : ℝ) + 2)) = (nC : ℝ) * ((nC : ℝ) + 3) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ) + 2)) nC]
  exact sum_range_add_two nC

/-- **L5 self-contained**: under the capsule-factor hypothesis,
`VHull = ((l+5)/4)·D` at `l = 2·nC+1`. -/
theorem VHull_eq_paper (nC : ℕ) (hn : 0 < nC) (term : Fin nC → ℝ) (D l : ℝ)
    (hl : l = 2 * (nC : ℝ) + 1) (hf : CapsuleFactor nC term D) :
    VHull nC term = ((l + 5) / 4) * D := by
  unfold VHull
  have hsum : (∑ i : Fin nC, term i) = (∑ i : Fin nC, ((i : ℝ) + 2)) * D := by
    rw [Finset.sum_congr rfl fun i _ => hf i, Finset.sum_mul]
  rw [hsum, sum_fin_add_two]
  have hnR : (nC : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  rw [hl]
  ring

/-- With the arch/infinity addend: if capsule terms use `D+arch`, the same
identity holds. -/
theorem VHull_eq_paper_arch (nC : ℕ) (hn : 0 < nC) (term : Fin nC → ℝ)
    (D arch l : ℝ) (hl : l = 2 * (nC : ℝ) + 1)
    (hf : CapsuleFactor nC term (D + arch)) :
    VHull nC term = ((l + 5) / 4) * (D + arch) := by
  exact VHull_eq_paper nC hn term (D + arch) l hl hf

/-- Instantiated with `DExact`: `VHull = ((l+5)/4)·DExact` under the capsule
factor hypothesis. -/
theorem VHull_eq_DExact {ι : Type*} [Fintype ι] (nC : ℕ) (hn : 0 < nC)
    (term : Fin nC → ℝ) (weight h logp : ι → ℝ) (l : ℝ)
    (hl : l = 2 * (nC : ℝ) + 1)
    (hf : CapsuleFactor nC term (DExact weight h logp)) :
    VHull nC term = ((l + 5) / 4) * DExact weight h logp := by
  exact VHull_eq_paper nC hn term (DExact weight h logp) l hl hf

def l5Rows : List (String × String × String) :=
  [ ("DExact", "Σ_v weight_v h_v logp_v (+ arch addend)", "DEF (DExact)"),
    ("VHull", "(1/nC)Σ_i capsule_i; capsule_i=(i+2)D", "DEF (VHull / CapsuleFactor)"),
    ("capsule sum", "Σ_{i<nC}(i+2)=nC(nC+3)/2", "PROVED (sum_fin_add_two, green sum_range_add_two)"),
    ("L5", "VHull=((l+5)/4)D at l=2nC+1", "PROVED (VHull_eq_paper"),
    ("arch version", "same with D+arch", "PROVED (VHull_eq_paper_arch)"),
    ("DExact instance", "VHull=((l+5)/4)DExact", "PROVED (VHull_eq_DExact"),
    ("weight hypothesis", "capsule factor: term_i=(i+2)·D (weights product/sum-1 normalized)", "EXPLICIT HYPOTHESIS (CapsuleFactor)"),
    ("provenance", "lana IdentifiedCopies logVol_lgp/logVol_lgp_integral (source only; no import)", "CITED") ]

theorem l5Rows_length : l5Rows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1L5SelfContainedActual.VHull_eq_paper
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L5SelfContainedActual.VHull_eq_paper_arch
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L5SelfContainedActual.VHull_eq_DExact

end LeanFormal.IUT.XiFPaper.Mzk1L5SelfContainedActual

end