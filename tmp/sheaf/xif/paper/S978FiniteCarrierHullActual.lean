import tmp.sheaf.xif.paper.S975DensityRegionImageActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S957TensorClosureContainmentActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S978FiniteCarrierHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S975DensityRegionImageActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData T b)
variable (L : S965CarrierLinearization T b)

/-- Finite-carrier image of the possible-region union under the actual
linearization e : FinalLValuedCarrier ~ Qp^d. -/
noncomputable def finitePossibleRegionImageUnion :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  L.e '' paperPossibleRegionImageUnion (l := l) T b

/-- Paper tensor hull on the finite carrier: actual closure in the finite
Qp^d topology of the transported region union. -/
noncomputable def finitePaperTensorHull :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  closure (finitePossibleRegionImageUnion (T := T) (b := b) L)

/-- Actual qPilot image containment in the finite hull (region-union route). -/
theorem finiteQPilotImage_subset_finiteHull :
    L.e '' (qVFamToLValued T b '' qPilotPaperRegion (l := l) T b) ⊆
      finitePaperTensorHull (T := T) (b := b) L := by
  rintro y ⟨x, ⟨x0, hx0, rfl⟩, rfl⟩
  exact subset_closure ⟨qVFamToLValued T b x0,
    qPilotRegionImage_subset_regionUnion (l := l) T b ⟨x0, hx0, rfl⟩, rfl⟩

/-- Exact minimal bridge from the finite hull to the S957 D-hull: the finite
hull is contained in the e-image of S957's paperTensorHull. -/
def S978FiniteHullBridge : Prop :=
  finitePaperTensorHull (T := T) (b := b) L ⊆
    L.e '' paperTensorHull (l := l) T b D

/-- Finite-hull bridge gives S957 density. -/
theorem s957ThetaImageDenseInQPilot_of_finiteHullBridge
    (h : S978FiniteHullBridge (T := T) (b := b) D L) :
    S957ThetaImageDenseInQPilot (l := l) T b D := by
  intro y hy
  change y ∈ qVFamToLValued T b '' qPilotPaperRegion (l := l) T b at hy
  have hyfin : L.e y ∈ finitePaperTensorHull (T := T) (b := b) L :=
    finiteQPilotImage_subset_finiteHull (T := T) (b := b) L ⟨y, hy, rfl⟩
  rcases h hyfin with ⟨z, hz, hzy⟩
  have hzy' : y = z := (L.e.injective hzy).symm
  simpa [hzy'] using hz

/-- Exact S957 density gap, retained as a Prop. -/
def S978DensityExactGap : Prop :=
  S957ThetaImageDenseInQPilot (l := l) T b D

end LeanFormal.IUT.XiFPaper.S978FiniteCarrierHullActual

end
