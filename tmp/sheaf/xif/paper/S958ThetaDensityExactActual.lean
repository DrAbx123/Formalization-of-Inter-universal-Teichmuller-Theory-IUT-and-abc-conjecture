import tmp.sheaf.xif.paper.S956PaperTensorClosureActual
import tmp.sheaf.xif.paper.S957TensorClosureContainmentActual
import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
/-! # S958: exact form of the qPilot closure-density input
The requested density S957ThetaImageDenseInQPilot is not derivable from the
current theta/Ind point-set data: thetaImageIndUnion contains the actual
theta/Ind images only, while qPilot is the whole F(cRoot)O region.  This file
proves the exact equivalence with the neighbourhood-approximation condition and
records it as the minimal missing input.  No union containment is asserted. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S958ThetaDensityExactActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S946TensorPaperSContainmentActual
open LeanFormal.IUT.XiFPaper.S956PaperTensorClosureActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open MeasureTheory Topology
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData (l := l) T b)
/-- The S957 density target is exactly the S956 approximation condition. -/
theorem s958_density_iff_approximation :
    S957ThetaImageDenseInQPilot (l := l) T b D ↔
      (letI : TopologicalSpace (FinalLValuedCarrier T b) := D.topologicalSpace
       S956QPilotApproximationCondition (l := l) T b) := by
  letI : TopologicalSpace (FinalLValuedCarrier T b) := D.topologicalSpace
  change qPilotPaperImageInLValued (l := l) T b ⊆
      closure (thetaImageIndUnion (l := l) T b) ↔
    ∀ x : qVFamTensorBlock T b, x ∈ qPilotPaperRegion (l := l) T b →
      ∀ U : Set (FinalLValuedCarrier T b),
        U ∈ 𝓝 (qVFamToLValued (l := l) T b x) →
        (U ∩ thetaImageIndUnion (l := l) T b).Nonempty
  constructor
  · intro h x hx U hU
    exact (mem_closure_iff_nhds.mp (h ⟨x, hx, rfl⟩)) U hU
  · rintro h y ⟨x, hx, rfl⟩
    exact mem_closure_iff_nhds.mpr (h x hx)
/-- Exact minimal missing density input. -/
def S958DensityExactInput : Prop :=
  letI : TopologicalSpace (FinalLValuedCarrier T b) := D.topologicalSpace
  S956QPilotApproximationCondition (l := l) T b
theorem s958_density_iff_exactInput :
    S957ThetaImageDenseInQPilot (l := l) T b D ↔
      S958DensityExactInput (l := l) T b D :=
  s958_density_iff_approximation (l := l) T b D
end LeanFormal.IUT.XiFPaper.S958ThetaDensityExactActual
