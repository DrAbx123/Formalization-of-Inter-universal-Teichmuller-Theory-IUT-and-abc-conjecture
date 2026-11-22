import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeMain

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field

theorem S1687P_ne_zero' : S1687P ≠ 0 := by
  intro h
  have hdeg : S1687P.natDegree = 3 := by unfold S1687P; compute_degree!
  rw [h, Polynomial.natDegree_zero] at hdeg
  norm_num at hdeg

theorem S1687P_splits_F : (S1687P.map (algebraMap ℚ F)).Splits := by
  let Ω := AlgebraicClosure F
  have hH : (S1687H.map (algebraMap ℚ F)).Splits := S1687H_splits_in_F'
  have hHne : (S1687H.map (algebraMap ℚ F)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective]
    exact S1687H_ne_zero
  have hPneΩ : (S1687P.map (algebraMap ℚ Ω)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ Ω).injective]
    exact S1687P_ne_zero'
  have hmapP : ((S1687P.map (algebraMap ℚ F)).map (algebraMap F Ω)) =
      S1687P.map (algebraMap ℚ Ω) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ F Ω]
  have hmapH : ((S1687H.map (algebraMap ℚ F)).map (algebraMap F Ω)) =
      S1687H.map (algebraMap ℚ Ω) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ F Ω]
  have hroots : ∀ x ∈ ((S1687P.map (algebraMap ℚ F)).map (algebraMap F Ω)).roots,
      x ∈ (algebraMap F Ω).range := by
    intro x hx
    have hx'' : x ∈ (S1687P.map (algebraMap ℚ Ω)).roots := by
      rwa [hmapP] at hx
    have hxroot : aeval x S1687P = 0 := by
      have h : (S1687P.map (algebraMap ℚ Ω)).IsRoot x := (Polynomial.mem_roots hPneΩ).mp hx''
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using h
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2)
    have hyH : aeval y S1687H = 0 := by
      rw [S1687H_eval_eq, hy]
      exact hxroot
    have hyroot : ((S1687H.map (algebraMap ℚ F)).map (algebraMap F Ω)).IsRoot y := by
      rw [hmapH]
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hyH
    have hy_range : y ∈ (algebraMap F Ω).range :=
      Polynomial.Splits.mem_range_of_isRoot hH hHne hyroot
    obtain ⟨z, hz⟩ := hy_range
    refine ⟨z ^ 2, ?_⟩
    rw [map_pow, hz, hy]
  apply Polynomial.Splits.of_splits_map (i := algebraMap F Ω)
  · exact IsAlgClosed.splits _
  · intro x hx
    have hx' : x ∈ (S1687P.map (algebraMap ℚ Ω)).roots := by
      rwa [hmapP] at hx
    exact hroots x (by rwa [hmapP])

end ProbeMain
