/- Route 7.2: assembly from SeparationInput to ResidueRootGeneration. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalAnalyticInputActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalCongruenceActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalResiduePolysActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalHgenInterfaceActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalAnalyticInputActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalCongruenceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResiduePolysActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual

variable {p : Nat} [Fact p.Prime]

/-- Analytic separation input of route 7.2 step 4. -/
def SeparationInput (d B : Nat) : Prop :=
  ∀ M : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] M →
    Module.finrank ℚ_[p] M ≤ d →
    ∃ (n : Nat) (hn : n ≤ d) (f : Polynomial ℤ_[p]) (x : PadicAlgCl p),
      f.Monic ∧ f.natDegree = n ∧ 0 < n ∧ IsIntegral ℚ_[p] x ∧ ‖x‖ ≤ 1 ∧
      Module.finrank ℚ_[p] M = n ∧
      (f.map (algebraMap ℤ_[p] ℚ_[p])).aeval x = 0 ∧
      M = IntermediateField.adjoin ℚ_[p] ({x} : Set (PadicAlgCl p)) ∧
      ∀ y : PadicAlgCl p, IsConjRoot ℚ_[p] x y → y ≠ x →
        (p : ℝ) ^ (-(B : ℤ)) ≤ ‖x - y‖

/-- Assembly from SeparationInput to ResidueRootGeneration. -/
theorem residueRootGeneration_of_separationInput (d B N : Nat) (hN : 0 < N)
    (hsmall : ∀ n : Nat, 0 < n → n ≤ d →
      ((n + 1 : Nat) * (p : ℝ) ^ (1 - (N : ℤ))) ^ ((n : ℝ)⁻¹) <
        (p : ℝ) ^ (-(B : ℤ)))
    (hsep : SeparationInput (p := p) d B) :
    ResidueRootGeneration (p := p) d N := by
  intro M hMfin hMle
  obtain ⟨n, hn, f, x, hfmonic, hfdeg, hnpos, hxint, hxnorm, hMrank, hxroot, hM, hsepconj⟩ :=
    hsep M hMfin hMle
  let c : Fin n → ZMod (p ^ N) := fun i => PadicInt.toZModPow N (f.coeff i)
  let g : Polynomial ℚ_[p] := (residueMonicPoly p N n c).map (algebraMap ℤ_[p] ℚ_[p])
  have hgmonic : g.Monic := (residueMonicPoly_monic p N n c).map (algebraMap ℤ_[p] ℚ_[p])
  have hgdeg : g.natDegree = n := by
    rw [show g = (residueMonicPoly p N n c).map (algebraMap ℤ_[p] ℚ_[p]) from rfl]
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (by simp [(residueMonicPoly_monic p N n c).leadingCoeff])]
    exact residueMonicPoly_natDegree p N n c
  have hfQdeg : (f.map (algebraMap ℤ_[p] ℚ_[p])).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (by simp [hfmonic.leadingCoeff]), hfdeg]
  have heps : (0 : ℝ) < (p : ℝ) ^ (1 - (N : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hcoeff : ∀ i : Nat, ‖g.coeff i - (f.map (algebraMap ℤ_[p] ℚ_[p])).coeff i‖ <
      (p : ℝ) ^ (1 - (N : ℤ)) := by
    intro i
    have h := residueMonicPoly_coeff_close (p := p) N n hN f hfmonic hfdeg i
    simpa [g, Polynomial.coeff_map] using h
  obtain ⟨beta, hbeta_root, hbeta_close⟩ :=
    exists_root_near_of_coeff_close (p := p) (n := n) hnpos
      (hfmonic.map (algebraMap ℤ_[p] ℚ_[p])) hgmonic hgdeg hfQdeg heps hcoeff
      (by simpa using hxroot)
  have hbetal : ‖x - beta‖ < (p : ℝ) ^ (-(B : ℤ)) := by
    have hmax : max ‖x‖ 1 = 1 := max_eq_right hxnorm
    rw [hmax, mul_one] at hbeta_close
    exact lt_of_lt_of_le hbeta_close (le_of_lt (hsmall n hnpos hn))
  have hsep' : ∀ y, IsConjRoot ℚ_[p] x y → x ≠ y → ‖x - beta‖ < ‖x - y‖ := by
    intro y hy hyne
    exact lt_of_lt_of_le hbetal (hsepconj y hy hyne.symm)
  have hxmem : x ∈ IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p)) := by
    have hxsep : IsSeparable ℚ_[p] x := IsSeparable.of_integral (F := ℚ_[p]) (K := PadicAlgCl p) x
    have hyint : IsIntegral ℚ_[p] beta := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic beta)
    exact padic_krasner_mem hxsep hyint hsep'
  have hle : M ≤ IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p)) := by
    rw [hM]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxmem)
  have hbetalg : IsAlgebraic ℚ_[p] beta := Algebra.IsAlgebraic.isAlgebraic beta
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p))) :=
    IntermediateField.adjoin.finiteDimensional (IsAlgebraic.isIntegral hbetalg)
  have hrank_le : Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p))) ≤ n := by
    have hmindvd : minpoly ℚ_[p] beta ∣ g := by
      apply minpoly.dvd ℚ_[p]
      rw [Polynomial.IsRoot.def] at hbeta_root
      rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def] at hbeta_root
      exact hbeta_root
    have hdeg_min : (minpoly ℚ_[p] beta).natDegree ≤ n := by
      calc (minpoly ℚ_[p] beta).natDegree ≤ g.natDegree :=
            Polynomial.natDegree_le_of_dvd hmindvd hgmonic.ne_zero
        _ = n := hgdeg
    rw [IntermediateField.adjoin.finrank (IsAlgebraic.isIntegral hbetalg)]
    exact hdeg_min
  have hrank_eq : Module.finrank ℚ_[p] M =
      Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p))) := by
    apply le_antisymm
    · exact IntermediateField.finrank_le_of_le_right hle
    · rw [hMrank]
      exact hrank_le
  have hMbeta : M = IntermediateField.adjoin ℚ_[p] ({beta} : Set (PadicAlgCl p)) :=
    IntermediateField.eq_of_le_of_finrank_eq hle hrank_eq
  refine ⟨n, hn, c, beta, ?_, hMbeta⟩
  · rw [Polynomial.IsRoot.def] at hbeta_root
    rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def] at hbeta_root
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    simpa [g] using hbeta_root

#print axioms residueRootGeneration_of_separationInput
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual
