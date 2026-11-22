import tmp.sheaf.xif.paper.S3070HnonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3070HnonActual
open LeanFormal.IUT.XiFPaper.S3069RangeInclusionActual
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

namespace LeanFormal.IUT.XiFPaper.S3070ZSquareActualAdapted

abbrev K2 := S3062ChartZPreservationProof.K
noncomputable local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
noncomputable local instance : Field S2844D6F6BaseChangeActual.K := inferInstance
noncomputable local instance : NumberField S2844D6F6BaseChangeActual.K := LeanFormal.IUT.XiFPaper.S2809E6FiniteActual.S2809_numberField
noncomputable local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

theorem S3070_zSquare
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β) :
    ∃ z : S2801E37AffineScheme S3062ChartZPreservationProof.K ⟶
        S2801E37AffineScheme S3062ChartZPreservationProof.K,
      z ≫ z = 𝟙 (S2801E37AffineScheme S3062ChartZPreservationProof.K) ∧
      E37ProjChartZMap S3062ChartZPreservationProof.K
          (S2820E37TransitionIso S3062ChartZPreservationProof.K) ≫ Over.Hom.left β =
        z ≫ E37ProjChartZMap S3062ChartZPreservationProof.K
          (S2820E37TransitionIso S3062ChartZPreservationProof.K) := by
  obtain ⟨z, hsquare⟩ := S3070_factorization_of_origin β β.left rfl hβ hfix
  let ChartZ := E37ProjChartZMap S3062ChartZPreservationProof.K
    (S2820E37TransitionIso S3062ChartZPreservationProof.K)
  haveI : IsOpenImmersion ChartZ := by
    change IsOpenImmersion (E37ProjChartZMap S2844D6F6BaseChangeActual.K
      (S2820E37TransitionIso S2844D6F6BaseChangeActual.K))
    exact S3068_chartZ_isOpenImmersion
  haveI : Mono ChartZ := IsOpenImmersion.mono _
  have hβleft : Over.Hom.left β ≫ Over.Hom.left β =
      𝟙 (Over.left S2844D6F6BaseChangeActual.S2844X) := by
    have h := congrArg (fun f => Over.Hom.left f) hβ
    simpa using h
  have hsq : z ≫ z = 𝟙 (S2801E37AffineScheme S3062ChartZPreservationProof.K) := by
    apply (cancel_mono ChartZ).mp
    calc (z ≫ z) ≫ ChartZ
        = z ≫ (z ≫ ChartZ) := Category.assoc _ _ _
      _ = z ≫ (ChartZ ≫ Over.Hom.left β) := by erw [hsquare]
      _ = (z ≫ ChartZ) ≫ Over.Hom.left β := (Category.assoc _ _ _).symm
      _ = (ChartZ ≫ Over.Hom.left β) ≫ Over.Hom.left β := by erw [hsquare]
      _ = ChartZ ≫ (Over.Hom.left β ≫ Over.Hom.left β) := Category.assoc _ _ _
      _ = ChartZ ≫ 𝟙 _ := by rw [hβleft]
      _ = ChartZ := Category.comp_id _
  exact ⟨z, hsq, hsquare⟩

#check S3070_zSquare
#print axioms S3070_zSquare

end LeanFormal.IUT.XiFPaper.S3070ZSquareActualAdapted
end
