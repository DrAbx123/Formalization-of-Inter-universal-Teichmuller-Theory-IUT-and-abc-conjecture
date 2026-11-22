import tmp.sheaf.xif.paper.S3054ProjectiveTransport
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S3056GluingUniqueness
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3056GluingUniqueness
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3059SpecMapComparison
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Spec.map of the affine identity is the identity affine map. -/
theorem S3059_spec_id :
    Spec.map (CommRingCat.ofHom (RingHom.id
      (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K))) =
      𝟙 (S2801E37AffineScheme S2844D6F6BaseChangeActual.K) := by
  simp

/-- Spec.map of the alpha ring substitution is exactly the chart-Z endomorphism. -/
theorem S3059_spec_alpha :
    Spec.map (CommRingCat.ofHom
      (S2853RingHom S2844D6F6BaseChangeActual.K)) =
      S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K := rfl

/-- The global alpha chart-Z square: the chart-Z component of global alpha is
the chart-Z endomorphism. -/
def S3059SpecMapComparison : Prop :=
  S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ alphaOverS2844.left =
    S2853ChartZSchemeEndo S2844D6F6BaseChangeActual.K ≫
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K

/-- The chart-Z square is actual from the glued global alpha construction. -/
theorem S3059_specMapComparison : S3059SpecMapComparison := by
  unfold S3059SpecMapComparison
  rfl

#check S3059_spec_id
#check S3059_spec_alpha
#check S3059SpecMapComparison
#check S3059_specMapComparison
#print axioms S3059_specMapComparison

end LeanFormal.IUT.XiFPaper.S3059SpecMapComparison
end
