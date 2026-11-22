import tmp.sheaf.xif.paper.S854ProductCompactRouteActual
import tmp.sheaf.xif.paper.S841FractionalCompactAbsorptionActual

/-! # S863: product compactness by continuous multiplication image

F(cRoot) and O_hol are compact (S841, S854).  Their cartesian product is
compact, and multiplication is continuous, so the pointwise product image is
compact.  The submodule product F*O_hol is the additive span of that image,
not literally the image; the exact missing identification is
  (F*O_hol : Set) = mulImage.
Given that identification, paperRootMinimalRegion is compact and the S806
closedness gap follows.  No identification or compactness is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S854ProductCompactRouteActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Pointwise product image of F(cRoot) and O_hol. -/
def s863MulImage : Set (qVFamTensorBlock T b) :=
  (fun p : qVFamTensorBlock T b × qVFamTensorBlock T b => p.1 * p.2) ''
    ((s839FractionalLattice (l := l) T b : Set (qVFamTensorBlock T b)) ×ˢ
      (s839HolomorphicLattice (l := l) T b : Set (qVFamTensorBlock T b)))

/-- Actual compactness of the pointwise product image. -/
theorem s863MulImageCompact : IsCompact (s863MulImage (l := l) T b) := by
  unfold s863MulImage
  exact ((s841FractionalCompact (l := l) T b).prod
    (s854HolomorphicCompact (l := l) T b)).image continuous_mul

/-- Exact identification of the submodule product with the pointwise image. -/
def S863ProductImageEq : Prop :=
  ((s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b)) = s863MulImage (l := l) T b

/-- Actual: product-image identification gives product compactness. -/
theorem s863ProductCompact_of_imageEq
    (h : S863ProductImageEq (l := l) T b) :
    S854ProductCompact (l := l) T b := by
  unfold S854ProductCompact
  rw [h]
  exact s863MulImageCompact (l := l) T b

/-- Actual: product-image identification gives minimal compactness. -/
theorem s863MinimalCompact_of_imageEq
    (h : S863ProductImageEq (l := l) T b) :
    S839MinimalCompact (l := l) T b :=
  s854MinimalCompact_of_productCompact (l := l) T b
    (s863ProductCompact_of_imageEq (l := l) T b h)

/-- Actual: product-image identification closes the S806 gap. -/
theorem paperRootHullNonzeroClosedGap_of_imageEq
    (h : S863ProductImageEq (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_productCompact (l := l) T b
    (s863ProductCompact_of_imageEq (l := l) T b h)

/-- Exact alternative: closedness of the submodule product inside compact O_hol. -/
def S863ProductClosed : Prop :=
  IsClosed ((s839FractionalLattice (l := l) T b *
    s839HolomorphicLattice (l := l) T b :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b))

/-- Exact missing condition for the continuous-image route. -/
def S863ProductImageEqRequired : Prop :=
  S863ProductImageEq (l := l) T b

end LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual

end
