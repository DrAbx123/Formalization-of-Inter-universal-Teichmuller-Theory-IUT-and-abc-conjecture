import tmp.sheaf.xif.paper.S3056GluingUniqueness

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3056GluingUniqueness
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3057GluingUniquenessActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

noncomputable abbrev S3057D : Scheme.GlueData.{0} :=
  E37ProjGlueData S2844D6F6BaseChangeActual.K
    (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)

/-- S3056GluingUniqueness: chart-Z and chart-Y components determine a scheme
endomorphism. -/
theorem S3057_gluingUniqueness : S3056GluingUniqueness := by
  intro β γ hZ hY
  apply Over.OverMorphism.ext
  apply S3057D.openCover.hom_ext β.left γ.left
  intro i
  cases i with
  | up b =>
    cases b
    · change S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ Over.Hom.left β =
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ Over.Hom.left γ
      exact hZ
    · change S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ Over.Hom.left β =
        S2820E37ChartYMap S2844D6F6BaseChangeActual.K ≫ Over.Hom.left γ
      exact hY

#check S3057_gluingUniqueness
#print axioms S3057_gluingUniqueness

end LeanFormal.IUT.XiFPaper.S3057GluingUniquenessActual
end