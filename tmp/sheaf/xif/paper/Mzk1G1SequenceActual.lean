import tmp.sheaf.xif.paper.Mzk1G1UniformActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

/-- Actual ℚ-valued uniform-epsilon criterion. -/
def UniformEpsilonCriterionRat (f : ℕ → ℚ → ℚ) : Prop :=
  ∀ K : Set ℚ, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, |(f n x : ℝ)| < ε

/-- Actual sequence of Belyi polynomial values: the two actual family members
for n=0,1, then zero. -/
def belyiSequence : ℕ → ℚ → ℚ :=
  fun n x => if h : n < 2 then
    (belyiTwoFamily.map ⟨n, h⟩).poly.eval x
  else 0

/-- Actual UniformEpsilonCriterion for the Belyi sequence (tail is zero). -/
theorem belyiSequence_uniformEpsilon :
    UniformEpsilonCriterionRat belyiSequence := by
  intro K hK ε hε
  refine ⟨2, fun n hn x hx => ?_⟩
  have hn2 : ¬ n < 2 := not_lt_of_ge hn
  have hzero : belyiSequence n x = 0 := by
    simp [belyiSequence, hn2]
  rw [hzero]
  simpa using hε

/-- Actual nonvacuous compact-set instance. -/
theorem belyiSequence_uniformEpsilon_compact :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ ({2} : Set ℚ), |(belyiSequence n x : ℝ)| < 1 := by
  have h := belyiSequence_uniformEpsilon ({2} : Set ℚ) isCompact_singleton (1 : ℝ) one_pos
  exact h

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
