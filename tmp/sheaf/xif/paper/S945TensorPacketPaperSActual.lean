import tmp.sheaf.xif.paper.PaperFinalLValuedThetaIndHullActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual

/-! # S945: paper S on the actual tensor-packet carrier

The tensor-packet carrier is `FinalLValuedCarrier = qVFamBlock ⊗_{Qp} L`.
Actual Ind1/Ind2/Ind3 linear equivalences and the actual root Theta image
live on this carrier (S199).  Define the paper S as the closure of the theta
image union with all actual Ind images, prove the actual image inclusions,
and record the exact qPilot-containment and normalized-log-volume bridges.
No fake image and no empty lower bound.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Paper S on the actual L-valued tensor packet: the actual union of the
theta image and all actual Ind1/Ind2/Ind3 images.  No topology is currently
available on this carrier, so closure is not asserted; the exact closure
carrier bridge is recorded separately. -/
noncomputable def paperTensorS : Set (FinalLValuedCarrier T b) :=
  thetaImageIndUnion (l := l) T b

theorem rootThetaImage_subset_paperTensorS :
    rootThetaImageInLValued (l := l) T b ⊆ paperTensorS (l := l) T b :=
  rootThetaImage_subset_indUnion (l := l) T b

theorem ind1Image_subset_paperTensorS :
    ind1Image (l := l) T b ⊆ paperTensorS (l := l) T b :=
  ind1Image_subset_indUnion (l := l) T b

theorem ind2Image_subset_paperTensorS (u : (FinalL T b)ˣ) :
    ind2Image (l := l) T b u ⊆ paperTensorS (l := l) T b := by
  intro x hx
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨u, hx⟩))

theorem ind3Image_subset_paperTensorS (u : (FinalL T b)ˣ) (m : Nat) :
    ind3Image (l := l) T b u m ⊆ paperTensorS (l := l) T b := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨m, hx⟩⟩)

/-- qPilot region transported to the L-valued tensor packet. -/
noncomputable def qPilotPaperImageInLValued : Set (FinalLValuedCarrier T b) :=
  qVFamToLValued (l := l) T b '' qPilotPaperRegion (l := l) T b

/-- Exact carrier bridge needed for qPilot ⊆ S: after transport to the
L-valued tensor packet, the qPilot region is contained in paper S. -/
def S945QPilotSubsetPaperTensorS : Prop :=
  qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorS (l := l) T b

def S945QPilotSubsetPaperTensorSRequired : Prop :=
  S945QPilotSubsetPaperTensorS (l := l) T b

/-- Exact tensor-packet log-volume data: a carrier with an actual additive
Haar measure and a positive finite unit region.  The tree does not supply
this normalization on the L-valued tensor packet. -/
structure S945TensorLogVolumeData where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [locallyCompactSpace : LocallyCompactSpace carrier]
  [measurableSpace : MeasurableSpace carrier]
  [borelSpace : BorelSpace carrier]
  measure : Measure carrier
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitRegion : Set carrier
  unit_pos : 0 < measure unitRegion
  unit_lt_top : measure unitRegion < ⊤

def S945TensorLogVolumeRequired : Prop :=
  Nonempty S945TensorLogVolumeData

end LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual

end
