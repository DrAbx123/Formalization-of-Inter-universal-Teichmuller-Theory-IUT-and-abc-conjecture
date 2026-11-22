import tmp.sheaf.xif.paper.S3070HnonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3070HnonActual
open LeanFormal.IUT.XiFPaper.S3068OpenImmersionFactorizationActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3072ZSquareActual

abbrev ChartZ : S2801E37AffineScheme S3062ChartZPreservationProof.K ⟶
    Over.left S2844D6F6BaseChangeActual.S2844X :=
  E37ProjChartZMap S3062ChartZPreservationProof.K
    (S2820E37TransitionIso S3062ChartZPreservationProof.K)

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Actual: an ∞-fixing order-two automorphism restricts to an order-two
endomorphism of chart Z. -/
theorem S3072_zSquare
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β) :
    ∃ z : S2801E37AffineScheme S3062ChartZPreservationProof.K ⟶
        S2801E37AffineScheme S3062ChartZPreservationProof.K,
      z ≫ z = 𝟙 (S2801E37AffineScheme S3062ChartZPreservationProof.K) ∧
        ChartZ ≫ β.left = z ≫ ChartZ := by
  obtain ⟨z, hsquare₀⟩ := S3070_chartZFactorizationTarget β hβ hfix
  have hsquare : ChartZ ≫ β.left = z ≫ ChartZ := hsquare₀
  haveI : IsOpenImmersion ChartZ := by
    simpa [ChartZ] using S3068_chartZ_isOpenImmersion
  haveI : Mono ChartZ := inferInstance
  have hβs2 : β.left ≫ β.left =
      𝟙 (Over.left S2844D6F6BaseChangeActual.S2844X) := by
    have h := congrArg (fun f : S2844D6F6BaseChangeActual.S2844X ⟶
        S2844D6F6BaseChangeActual.S2844X => f.left) hβ
    simpa using h
  have hzsq : z ≫ z = 𝟙 (S2801E37AffineScheme S3062ChartZPreservationProof.K) := by
    apply (cancel_mono ChartZ).mp
    have h := congrArg (fun f => f ≫ β.left) hsquare
    rw [Category.assoc, hβs2, Category.comp_id] at h
    rw [Category.assoc, hsquare] at h
    rw [← Category.assoc] at h
    simpa using h.symm
  exact ⟨z, hzsq, hsquare⟩

#check S3072_zSquare
#print axioms S3072_zSquare

end LeanFormal.IUT.XiFPaper.S3072ZSquareActual
end
