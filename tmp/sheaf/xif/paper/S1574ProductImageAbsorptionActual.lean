import tmp.sheaf.xif.paper.S1570ReportCInputsClosedActual
import tmp.sheaf.xif.paper.S853OInFZeroAbsorptionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1574ProductImageAbsorptionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.S1570ReportCInputsClosedActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-- Actual implication: the S853 geometric input O_hol <= F(0) gives the
S841 pointwise absorption, hence the product image equality. -/
theorem s1574PointwiseAbsorption_of_OLeZero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    S841PointwiseAbsorption (l := l) T b :=
  s841PointwiseAbsorption_of_O_le_zero (l := l) T b h

/-- Actual implication to the Report-C product equality via S1570. -/
theorem s1574ProductImageEq_of_OLeZero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    S863ProductImageEq T b :=
  s1570ProductImageEq_of_OLeZero T b h

/-- Exact remaining geometric input for the product image: O_hol <= F(0).
No inhabitant is asserted; the tree currently proves only the reverse
F(0) <= O_hol, not this inclusion. -/
def S1574ProductImageFirstMissing : Prop :=
  S853OLeFractionalZeroRequired (l := l) T b

/-- The corresponding exact S841 form. -/
def S1574PointwiseAbsorptionFirstMissing : Prop :=
  S841PointwiseAbsorption (l := l) T b

/-- Conditional product image from the exact S841 input (via S1570). -/
theorem s1574ProductImageEq_of_pointwiseAbsorption
    (h : S1574PointwiseAbsorptionFirstMissing (l := l) T b) :
    S863ProductImageEq T b :=
  s1570ProductImageEq_of_pointwiseAbsorption T b h

end LeanFormal.IUT.XiFPaper.S1574ProductImageAbsorptionActual

end
