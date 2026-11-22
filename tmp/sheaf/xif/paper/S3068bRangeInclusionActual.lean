import tmp.sheaf.xif.paper.S3067PointRealizationActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S3067PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3068bRangeInclusionActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev K := S2844D6F6BaseChangeActual.K
abbrev X := S2844D6F6BaseChangeActual.S2844X

/-- Range inclusion form: the chart-Z component of a square-zero automorphism
with infinity fixed is contained in the chart-Z range. -/
theorem S3068b_range_inclusion
    (β : X ⟶ X)
    (hβ2 : β ≫ β = 𝟙 X)
    (hfix : S3062InfinityPoint ≫ Over.Hom.left β = S3062InfinityPoint)
    (hnon : S3062InfinityNotInChartZ) :
    Set.range (fun x : S2801E37AffineScheme K =>
      E37ProjChartZMap K (S2820E37TransitionIso K) x ≫ Over.Hom.left β) ⊆
      Set.range (E37ProjChartZMap K (S2820E37TransitionIso K)) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hβleft : Over.Hom.left β ≫ Over.Hom.left β =
      𝟙 (S2820E37ProjectiveScheme K) := by
    have h := congrArg (fun f : X ⟶ X => Over.Hom.left f) hβ2
    simpa [Category.assoc] using h
  have hne : E37ProjChartZMap K (S2820E37TransitionIso K) x ≫ Over.Hom.left β ≠
      S3062InfinityPoint := by
    intro hyinf
    have hcomp := congrArg (fun f => f ≫ Over.Hom.left β) hyinf
    rw [Category.assoc, hβleft, Category.comp_id, hfix] at hcomp
    exact hnon ⟨x, hcomp⟩
  by_cases hyinf : E37ProjChartZMap K (S2820E37TransitionIso K) x ≫ Over.Hom.left β =
      S3062InfinityPoint
  · exact absurd hyinf hne
  · exact S3067_pointRealization _ hyinf

#check S3068b_range_inclusion
#print axioms S3068b_range_inclusion

end LeanFormal.IUT.XiFPaper.S3068bRangeInclusionActual
end