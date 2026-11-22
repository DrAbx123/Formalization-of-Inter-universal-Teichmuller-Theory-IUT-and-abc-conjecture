/- R5 non-circular assembly: per-M ingredients (monogenic minpoly data + derivative bound).
construct SeparationInput d (d*(d+2)). No field has type SeparationInput.

The ingredient derivative bound is stated at the Serre bound
`differentBound p d = d*(v_p(d)+1)`; the separation conclusion is drawn at the
conservative bound `d*(d+2) >= d*(v_p(d)+1)`, where the constant `p^{-B}` is smaller,
so the conservative separation statement is the weaker one. -/
import tmp.sheaf.xif.paper.Mzk1G1MonogenicMinpolyBridgeActual
import tmp.sheaf.xif.paper.Mzk1G1DifferentBoundConservativeActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationConstantActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationBoundActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalResidueRootGenerationActual
import Mathlib.Tactic
noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1SeparationInputActual

open LeanFormal.IUT.XiFPaper.Mzk1G1DifferentBoundConservativeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationConstantActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual

variable {p : Nat} [Fact p.Prime]

/-- Per-M ingredients for the R5 construction.  All fields are genuine inputs; none is
the target `SeparationInput`.  The derivative lower bound is the Serre bound
`p^{-(d*(v_p(d)+1))}`. -/
structure SeparationInputIngredients (p : Nat) [Fact p.Prime] (d : Nat) : Prop where
  data : ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)),
      FiniteDimensional ℚ_[p] M → Module.finrank ℚ_[p] M ≤ d →
      ∃ (n : Nat) (hn : n ≤ d) (f : Polynomial ℤ_[p]) (x : PadicAlgCl p),
        f.Monic ∧ f.natDegree = n ∧ 0 < n ∧ IsIntegral ℚ_[p] x ∧ ‖x‖ ≤ 1 ∧
        Module.finrank ℚ_[p] M = n ∧
        (f.map (algebraMap ℤ_[p] ℚ_[p])).aeval x = 0 ∧
        M = IntermediateField.adjoin ℚ_[p] ({x} : Set (PadicAlgCl p)) ∧
        (f.map (algebraMap ℤ_[p] (PadicAlgCl p))).Splits ∧
        x ∈ (f.map (algebraMap ℤ_[p] (PadicAlgCl p))).roots ∧
        (∀ y : PadicAlgCl p, IsConjRoot ℚ_[p] x y →
          y ∈ (f.map (algebraMap ℤ_[p] (PadicAlgCl p))).roots) ∧
        ‖(f.map (algebraMap ℤ_[p] (PadicAlgCl p))).derivative.eval x‖ ≥
          (p : ℝ) ^ (-(differentBound p d : ℤ)) ∧
        (∀ y ∈ (f.map (algebraMap ℤ_[p] (PadicAlgCl p))).roots, ‖x - y‖ ≤ 1)

/-- R5 non-circular assembly: ingredients give SeparationInput at B = d*(d+2). -/
theorem separationInput_of_differentBound (d : Nat)
    (H : SeparationInputIngredients p d) :
    SeparationInput (p := p) d (differentBoundConservative d) := by
  intro M hMfin hMle
  obtain ⟨n, hn, f, x, hfmonic, hfdeg, hnpos, hxint, hxnorm, hMrank, hxroot, hM,
    hsplit, hxmem, hconj, hderiv, hrootnorm⟩ := H.data M hMfin hMle
  refine ⟨n, hn, f, x, hfmonic, hfdeg, hnpos, hxint, hxnorm, hMrank, hxroot, hM, ?_⟩
  intro y hyconj hyne
  haveI : DecidableEq (PadicAlgCl p) := Classical.decEq _
  have hB : differentBound p d ≤ differentBoundConservative d := by
    unfold differentBound differentBoundConservative
    have hle : padicValNat p d + 1 ≤ d + 2 := by
      have h := padicValNat_le_self (p := p) (d := d)
      omega
    exact Nat.mul_le_mul_left d hle
  have hz : (p : ℝ) ^ (-(differentBoundConservative d : ℤ)) ≤
      (p : ℝ) ^ (-(differentBound p d : ℤ)) := by
    refine zpow_le_zpow_right₀ ?_ ?_
    · exact_mod_cast (Fact.out : p.Prime).one_le
    · have h' : (differentBound p d : ℤ) ≤ (differentBoundConservative d : ℤ) := by
        exact_mod_cast hB
      exact neg_le_neg h'
  exact le_trans hz
    (separation_of_derivative_norm_ge (p := p) (d := d)
      (f := f.map (algebraMap ℤ_[p] (PadicAlgCl p)))
      (hfmonic.map (algebraMap ℤ_[p] (PadicAlgCl p))) hsplit
      hxmem (hconj y hyconj) hyne hrootnorm hderiv)

#print axioms separationInput_of_differentBound
end LeanFormal.IUT.XiFPaper.Mzk1G1SeparationInputActual
