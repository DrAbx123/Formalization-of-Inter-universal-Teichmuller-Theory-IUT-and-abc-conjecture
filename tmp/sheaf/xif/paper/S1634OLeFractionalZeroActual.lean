import tmp.sheaf.xif.paper.S1579OLeFractionalZeroAnalysisActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1634OLeFractionalZeroActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S1579OLeFractionalZeroAnalysisActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open LeanFormal.IUT.XiFPaper.S1574ProductImageAbsorptionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-- Route C basic inclusion: the holomorphic lattice is contained in the
fractional lattice F(0). -/
def S1634RouteCBasicInclusion : Prop :=
  s839HolomorphicLattice (l := l) T b ≤
    s853FractionalZero (l := l) T b

/-- The inclusion is exactly the S853/S1579 forward field. -/
theorem s1634RouteCBasicInclusion_iff :
    S1634RouteCBasicInclusion (l := l) T b ↔
      S853OLeFractionalZeroRequired (l := l) T b :=
  Iff.rfl

/-- The actual reverse inclusion available in the tree: F(0) is contained in
the holomorphic lattice. -/
theorem s1634ReverseInclusion_actual :
    s853FractionalZero (l := l) T b ≤
      s839HolomorphicLattice (l := l) T b :=
  s1579IntegerLattice_le_holomorphic (l := l) T b

/-- Exact first missing input for Route C. -/
abbrev S1634ExactFirstInput : Prop :=
  S853OLeFractionalZeroRequired (l := l) T b

/-- If the basic inclusion is supplied, Route C's pointwise absorption follows. -/
theorem s1634PointwiseAbsorption_of_basicInclusion
    (h : S1634RouteCBasicInclusion (l := l) T b) :
    S841PointwiseAbsorption T b :=
  s1579PointwiseAbsorption_of_forward (l := l) T b h

/-- If the basic inclusion is supplied, the product image equality follows. -/
theorem s1634ProductImageEq_of_basicInclusion
    (h : S1634RouteCBasicInclusion (l := l) T b) :
    S863ProductImageEq T b :=
  s1579ProductImageEq_of_forward (l := l) T b h

end LeanFormal.IUT.XiFPaper.S1634OLeFractionalZeroActual

end
