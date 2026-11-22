import tmp.sheaf.xif.paper.S3054ProjectiveTransport
import tmp.sheaf.xif.paper.S3055RingAutoOfChartZ
import tmp.sheaf.xif.paper.S3056GluingUniqueness
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2857GlobalAlphaCompatActual
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3054ProjectiveTransport
open LeanFormal.IUT.XiFPaper.S3055RingAutoOfChartZ
open LeanFormal.IUT.XiFPaper.S3056GluingUniqueness
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
namespace LeanFormal.IUT.XiFPaper.S3058GluingUniquenessProofAdapted
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-- Gluing uniqueness, actual via the E37 projective two-chart open cover:
maps out of the glued scheme are determined by their two chart components. -/
theorem S3058_gluingUniqueness : S3056GluingUniqueness := by
  intro β γ hZ hY
  let D := E37ProjGlueData S2844D6F6BaseChangeActual.K
    (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)
  haveI : HasMulticoequalizer D.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram D
  apply D.openCover.hom_ext
  intro x
  cases x with
  | up b =>
    cases b
    · simpa [S2820E37ChartZMap, E37ProjGlueData, D] using hZ
    · simpa [S2820E37ChartYMap, E37ProjGlueData, D] using hY

/-- The S3056 gluing uniqueness target is actual. -/
theorem S3058_gluingUniquenessTarget : S3056GluingUniqueness :=
  S3058_gluingUniqueness

#check S3058_gluingUniqueness
#check S3058_gluingUniquenessTarget
#print axioms S3058_gluingUniqueness

end LeanFormal.IUT.XiFPaper.S3058GluingUniquenessProofAdapted
end
