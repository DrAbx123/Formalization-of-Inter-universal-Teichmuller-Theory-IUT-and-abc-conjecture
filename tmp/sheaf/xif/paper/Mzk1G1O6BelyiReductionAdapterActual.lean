/- O6 / M2: adapter exposing the ported Belyi degree-reduction theorem inside our tree
(`m2AnalyticTarget_of_branch` h-existence input). REUSE (recon 2026-11-17):
`tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction.`
`TauCeti.exists_polynomial_aeval_mem_range` (perfect field F, values and critical values
into the base field) — imported, not ported. DEDUP: no adapter existed in our tree. -/
import tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6BelyiReductionAdapterActual

/-- At `F = ℚ`, `K = ℂ`: the ported Belyi degree reduction gives a polynomial `q` with
nonzero derivative that carries a finite set of algebraic complex numbers into `ℚ`,
and whose critical values also lie in `ℚ`. -/
theorem exists_belyiReduction_mem_range (S : Finset ℂ)
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : Polynomial ℚ, q.derivative ≠ 0 ∧
      (∀ s ∈ S, Polynomial.aeval s q ∈ Set.range (algebraMap ℚ ℂ)) ∧
      (∀ z : ℂ, Polynomial.aeval z q.derivative = 0 →
        Polynomial.aeval z q ∈ Set.range (algebraMap ℚ ℂ)) := by
  obtain ⟨q, hq, hSq, hcrit⟩ := TauCeti.exists_polynomial_aeval_mem_range (F := ℚ)
    (K := ℂ) (S := S) hS
  refine ⟨q, hq, ?_, ?_⟩
  · intro s hs
    exact hSq s hs
  · intro z hz
    exact hcrit ℂ z hz

/-- The same data in the form needed by the `M2AnalyticTarget` witness assembly: the
values on the finite set and the critical values are rational numbers. -/
theorem exists_belyiReduction_ratValues (S : Finset ℂ)
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : Polynomial ℚ, q.derivative ≠ 0 ∧
      (∃ r : S → ℚ, ∀ s : S, Polynomial.aeval (s : ℂ) q = algebraMap ℚ ℂ (r s)) ∧
      (∀ z : ℂ, Polynomial.aeval z q.derivative = 0 → ∃ c : ℚ,
        Polynomial.aeval z q = algebraMap ℚ ℂ c) := by
  obtain ⟨q, hq, hSq, hcrit⟩ := exists_belyiReduction_mem_range S hS
  refine ⟨q, hq, ?_, ?_⟩
  · refine ⟨fun s => (hSq s.1 s.2).choose, fun s => ?_⟩
    exact (hSq s.1 s.2).choose_spec.symm
  · intro z hz
    obtain ⟨c, hc⟩ := hcrit z hz
    exact ⟨c, hc.symm⟩

#print axioms exists_belyiReduction_mem_range
#print axioms exists_belyiReduction_ratValues
end LeanFormal.IUT.XiFPaper.Mzk1G1O6BelyiReductionAdapterActual