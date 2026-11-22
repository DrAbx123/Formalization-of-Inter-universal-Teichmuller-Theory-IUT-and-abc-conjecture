import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import tmp.sheaf.xif.paper.S2696VbadActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual

namespace Probe2699

local instance probeGaussian : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance probe2161 : Fact (Nat.Prime 2161) := ⟨by norm_num⟩

def p5mem (l : PrimeGeFive) : concreteGaussianFivePlace ∈ S2696Vbad l := by
  rw [S2696Vbad]; exact Or.inl rfl
def p2161mem (l : PrimeGeFive) : S2696GaussianPlace2161 ∈ S2696Vbad l := by
  rw [S2696Vbad]; exact Or.inr rfl

example (l : PrimeGeFive)
    (f : (p : NumberField.FinitePlace GaussianField) →
      p ∈ S2696Vbad l → Real) :
    S2696BadQAbsLog l f =
      f concreteGaussianFivePlace (p5mem l) +
      f S2696GaussianPlace2161 (p2161mem l) := by
  classical
  unfold S2696BadQAbsLog
  simp only
  rw [show (Finset.univ : Finset {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad l}) =
      {⟨concreteGaussianFivePlace, p5mem l⟩,
       ⟨S2696GaussianPlace2161, p2161mem l⟩} from ?_]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
    · simp only [Finset.mem_singleton]
      intro h
      have hres := congrArg (fun p : NumberField.FinitePlace GaussianField =>
        NumberFieldFinitePlace.residueCharacteristic p) (congrArg Subtype.val h)
      rw [concreteGaussianFivePlace_residueCharacteristic,
        S2696GaussianPlace2161_residueCharacteristic] at hres
      norm_num at hres
  · ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    constructor
    · intro _
      rcases x.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · intro _; trivial

end Probe2699
end
