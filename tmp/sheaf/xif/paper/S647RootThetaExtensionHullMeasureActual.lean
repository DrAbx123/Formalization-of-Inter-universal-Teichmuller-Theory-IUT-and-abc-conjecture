import tmp.sheaf.xif.paper.RootThetaExtensionHullCarrierActual
/-! # S647: extension-valued root Theta hull: measure/log comparison interface
The extension carrier/hull/image are actual in RootThetaExtensionHullCarrierActual.
No measure on the algebraic-closure unit product is constructed in the repo;
the exact measure/log-volume/comparison datum is recorded and a conditional
RootThetaHullLogComparison is constructed from it.  No completion hull is used. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S647RootThetaExtensionHullMeasureActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual
open MeasureTheory
universe u v
variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
/-- Exact measure/log datum for the extension-valued root Theta hull. -/
structure RootThetaExtensionHullMeasureData where
  measurableSpace : MeasurableSpace (RootThetaExtensionCarrier (G := G))
  measure : @Measure (RootThetaExtensionCarrier (G := G)) measurableSpace
  hull_measurable : @MeasurableSet (RootThetaExtensionCarrier (G := G)) measurableSpace
    (rootThetaExtensionHull (G := G))
  hullLogVolume : ENNReal
  qParameterLogVolume : ENNReal
  hullLogVolume_eq : hullLogVolume = measure (rootThetaExtensionHull (G := G))
  comparison : hullLogVolume <= qParameterLogVolume
/-- Exact missing measure/log datum. -/
def RootThetaExtensionHullMeasureRequired : Prop :=
  Nonempty (RootThetaExtensionHullMeasureData (G := G))
/-- Conditional actual comparison object from explicit measure/log data. -/
noncomputable def rootThetaHullLogComparisonOf
    (D : RootThetaExtensionHullMeasureData (G := G)) :
    RootThetaHullLogComparison :=
  { rootHullLogVolume := D.hullLogVolume
    qParameterLogVolume := D.qParameterLogVolume
    comparison := D.comparison }
theorem rootThetaHullLogComparisonOf_required
    (D : RootThetaExtensionHullMeasureData (G := G)) :
    RootThetaHullLogComparisonRequired :=
  ⟨rootThetaHullLogComparisonOf (G := G) D⟩
/-- Exact separation from the completion hull: a map extension->completion is
not asserted; no completion root hull is used here. -/
def RootThetaExtensionHullIsCarrier : Prop :=
  rootThetaExtensionImageSet (G := G) ⊆ rootThetaExtensionHull (G := G)
theorem rootThetaExtensionHullIsCarrier_proved :
    RootThetaExtensionHullIsCarrier (G := G) :=
  rootThetaExtensionImage_subset_hull (G := G)
end LeanFormal.IUT.XiFPaper.S647RootThetaExtensionHullMeasureActual
