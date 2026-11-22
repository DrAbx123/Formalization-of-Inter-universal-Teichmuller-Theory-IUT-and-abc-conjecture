import tmp.sheaf.xif.paper.Mzk1Lemma24UnionActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24ConjInvarianceActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual

local instance decEqQbar : DecidableEq Qbar := Classical.decEq Qbar

/-- Conjugation invariance of the minimal polynomial: if x is a conjugate of alpha
(i.e. x is a root of the minimal polynomial of alpha), then x has the same minimal
polynomial as alpha (paper [Mzk1] lines 166-169, used for the reduced-degree
bookkeeping in the induction). -/
theorem s3135_minpoly_eq_of_mem_conjugateSet {α x : Qbar} (hx : x ∈ conjugateSet α) :
    minpoly ℚ x = minpoly ℚ α := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic (k := ℚ)
  have hIntα : IsIntegral ℚ α :=
    IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic α)
  have hroot : Polynomial.aeval x (minpoly ℚ α) = 0 := hx
  exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hIntα) hroot
    (minpoly.monic hIntα)).symm

/-- The reduced degree is constant on conjugates. -/
theorem s3135_reducedDegreeOfPoint_eq_on_conj {α x : Qbar} (hx : x ∈ conjugateSet α) :
    reducedDegreeOfPoint x = reducedDegreeOfPoint α := by
  unfold reducedDegreeOfPoint
  rw [s3135_minpoly_eq_of_mem_conjugateSet hx]

/-- The image of the conjugate closure under the reduced-degree map is the same finite
set of numbers as the image of S. -/
theorem s3135_image_pointClosure_eq (S : Finset Qbar) :
    (pointClosure S).image reducedDegreeOfPoint = S.image reducedDegreeOfPoint := by
  apply Finset.Subset.antisymm
  · intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    rw [pointClosure, Finset.mem_biUnion] at hx
    obtain ⟨α, hα, hxα⟩ := hx
    rw [Set.Finite.mem_toFinset] at hxα
    exact Finset.mem_image.mpr
      ⟨α, hα, (s3135_reducedDegreeOfPoint_eq_on_conj hxα).symm⟩
  · exact Finset.image_subset_image (s3135_subset_pointClosure S)

