import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual
import tmp.sheaf.xif.paper.RootThetaExtensionHullCarrierActual

/-!
# Root Theta image -> completion qUnit power image

The actual map on paper theta labels is the 2l-th power:

  rootTheta j |-> (rootTheta j)^(2l) = embedded qUnit^(j^2).

This gives an actual label-indexed image map from the extension root image to
the embedded completion qUnit power image.  It is not a map of algebraic
closure units to completion elements; stripping the algebraic embedding is the
exact missing object.

The map from the extension hull to a completion tensor root-coefficient hull
(and its normalized log comparison) is recorded as an exact gap.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootThetaToCompletionImageMapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual 2l-th power image of a root Theta point in the algebraic closure. -/
noncomputable def rootThetaPowerImagePoint
    (j : ThetaLabel (l := l)) : (v : V) → RootExtension (G := G) v :=
  fun v => rootThetaPowerPoint (G := G) j v

/-- Actual completion qUnit power image qUnit_v^(j^2). -/
noncomputable def rootThetaCompletionImagePoint
    (j : ThetaLabel (l := l)) :
    (v : V) → CommonPrimeCompletion (G.place v) :=
  fun v => (G.qUnit v : CommonPrimeCompletion (G.place v)) ^
    (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat

/-- Actual compatibility: the 2l-th root image is the embedded completion
qUnit power image. -/
theorem rootThetaPowerImagePoint_eq_embedded_completion
    (j : ThetaLabel (l := l)) :
    rootThetaPowerImagePoint (G := G) j =
      fun v => (unitToAlgClosed (G.qUnit v) : RootExtension (G := G) v) ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := by
  funext v
  exact rootThetaPowerPoint_eq_embedded_qUnit_power (G := G) j v

/-- Actual image-level map data from root Theta labels to completion qUnit
powers. -/
structure RootThetaToCompletionImageMapData where
  rootPowerImage : ThetaLabel (l := l) → (v : V) → RootExtension (G := G) v
  rootPowerImage_eq : rootPowerImage = rootThetaPowerImagePoint (G := G)
  completionImage : ThetaLabel (l := l) →
    (v : V) → CommonPrimeCompletion (G.place v)
  completionImage_eq : completionImage = rootThetaCompletionImagePoint (G := G)
  compatibility : ∀ j : ThetaLabel (l := l),
    rootPowerImage j = fun v =>
      (unitToAlgClosed (G.qUnit v) : RootExtension (G := G) v) ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat

/-- Actual image-level map. -/
noncomputable def rootThetaToCompletionImageMapData :
    RootThetaToCompletionImageMapData (G := G) where
  rootPowerImage := rootThetaPowerImagePoint (G := G)
  rootPowerImage_eq := rfl
  completionImage := rootThetaCompletionImagePoint (G := G)
  completionImage_eq := rfl
  compatibility := rootThetaPowerImagePoint_eq_embedded_completion (G := G)

/-- Exact missing object: an actual extension root hull -> completion
root-coefficient hull map, its image compatibility, and normalized log
comparison.  Only the label-indexed completion qUnit power image is actual. -/
structure RootThetaCompletionHullMapGap : Type where
  completionTensorMap : Prop
  imageHullCompatibility : Prop
  hullMap : Prop
  normalizedLogComparison : Prop

/-- Exact missing object. -/
def RootThetaCompletionHullMapGapRequired : Prop :=
  Nonempty RootThetaCompletionHullMapGap

/-- Consumer relation: the actual map exists only at label/image power level;
the extension hull -> completion hull map remains the exact gap. -/
def RootThetaImageMapIsPowerOnly : Prop :=
  RootThetaCompletionHullMapGapRequired

end LeanFormal.IUT.XiFPaper.RootThetaToCompletionImageMapActual
end
