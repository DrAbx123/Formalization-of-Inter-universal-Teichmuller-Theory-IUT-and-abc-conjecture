import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1JHeightUniformProbeActual
open LeanFormal.IUT

variable {K : Type*} [Field K] [NumberField K]

/-- Archimedean absolute value of an integer cast is its usual absolute value. -/
lemma infPlace_intCast (w : NumberField.InfinitePlace K) (n : ℤ) :
    w ((n : ℤ) : K) = |(n : ℝ)| := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  rw [map_intCast]
  exact Complex.norm_intCast n

/-- Nonarchimedean absolute value of an integer cast is at most one. -/
lemma finPlace_intCast_le_one (w : NumberField.FinitePlace K) (n : ℤ) :
    w ((n : ℤ) : K) ≤ 1 :=
  IsNonarchimedean.apply_intCast_le_one (NumberField.FinitePlace.add_le w) (n := n)

#print axioms infPlace_intCast
#print axioms finPlace_intCast_le_one

end LeanFormal.IUT.XiFPaper.G1JHeightUniformProbeActual
end