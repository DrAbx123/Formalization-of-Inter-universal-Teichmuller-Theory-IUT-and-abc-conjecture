/- R5 non-circular assembly: per-M ingredients (monogenic minpoly data + derivative bound; retry 4)
construct SeparationInput d (d*(d+2)). No field has type SeparationInput. -/
import tmp.sheaf.xif.paper.Mzk1G1MonogenicMinpolyBridgeActual
import tmp.sheaf.xif.paper.Mzk1G1DifferentBoundConservativeActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationBoundActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalResidueRootGenerationActual
import Mathlib.Tactic
noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1SeparationInputFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1DifferentBoundConservativeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual

variable {p : Nat} [Fact p.Prime]

/-- Per-M ingredients for the R5 construction.  All fields are genuine inputs; none is
the target SeparationInput. -/
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
          (p : ℝ) ^ (-(differentBoundConservative d : ℤ)) ∧
        (∀ y ∈ (f.map (algebraMap ℤ_[p] (PadicAlgCl p))).roots, ‖x - y‖ ≤ 1)

/-- R5 non-circular assembly: ingredients give SeparationInput at B = d*(d+2). -/
theorem separationInput_of_differentBound (d : Nat)
    (he_d : ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)),
      FiniteDimensional ℚ_[p] M → Module.finrank ℚ_[p] M ≤ d →
        logShellRamificationExponent (K := M) (p := p) ≤ Module.finrank ℚ_[p] M)
    (hbase : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0)
    (H : SeparationInputIngredients p d) :
    SeparationInput (p := p) d (differentBoundConservative d) := by
  classical
  intro M hMfin hMle
  obtain ⟨n, hn, f, x, hfmonic, hfdeg, hnpos, hxint, hxnorm, hMrank, hxroot, hM,
    hsplit, hxmem, hconj, hderiv, hrootnorm⟩ := H.data M hMfin hMle
  refine ⟨n, hn, f, x, hfmonic, hfdeg, hnpos, hxint, hxnorm, hMrank, hxroot, hM, ?_⟩
  intro y hyconj hyne
  exact le_norm_sub_of_le_norm_eval_derivative
    (f := f.map (algebraMap ℤ_[p] (PadicAlgCl p))) (hfmonic.map _) hsplit
    hxmem (hconj y hyconj) hyne hrootnorm
    (eps := (p : ℝ) ^ (-(differentBoundConservative d : ℤ))) hderiv

#print axioms separationInput_of_differentBound
end LeanFormal.IUT.XiFPaper.Mzk1G1SeparationInputFinalActual
