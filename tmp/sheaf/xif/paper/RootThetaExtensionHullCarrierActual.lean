import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual
import tmp.sheaf.xif.paper.PaperRootThetaHullCarrierGapActual

/-!
# Actual extension-valued root Theta image/hull carrier

This file constructs the actual extension-valued product carrier and hull from
the root-valued paper theta image:

* carrier: product of algebraic-closure unit groups;
* image: paperRootThetaImagePointTheta over positive ThetaLabel;
* hull: the actual mu_{2l}-orbit union paperRootThetaHull (positive labels);
* image subset hull, actual.

It records the actual 2l-th power comparison to the embedded completion qUnit
power, and the exact missing map from the extension hull to the completion
root-coefficient hull.  The completion hull is not renamed or used as the
actual extension root hull.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaHullCarrierGapActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual extension-valued product carrier. -/
abbrev RootThetaExtensionCarrier : Type (max u v) :=
  RootThetaCarrier (G := G)

/-- The actual positive-label root Theta image set. -/
noncomputable abbrev rootThetaExtensionImageSet :
    Set (RootThetaExtensionCarrier (G := G)) :=
  paperRootThetaImageSet (G := G)

/-- The actual extension-valued root Theta hull. -/
noncomputable abbrev rootThetaExtensionHull :
    Set (RootThetaExtensionCarrier (G := G)) :=
  paperRootThetaHull (G := G)

/-- Actual image containment in the extension-valued hull. -/
theorem rootThetaExtensionImage_subset_hull :
    rootThetaExtensionImageSet (G := G) ⊆
      rootThetaExtensionHull (G := G) := by
  rintro x hx
  rw [rootThetaExtensionImageSet] at hx
  rcases hx with ⟨j, rfl⟩
  have h := paperRootThetaHull_mem (G := G) j 0
  convert h using 2
  ext v
  unfold paperRootThetaMuPoint paperRootThetaImagePointTheta paperRootThetaImagePoint
  simp

/-- Actual extension-valued image/hull carrier data. -/
structure RootThetaExtensionHullCarrierData where
  imageSet : Set (RootThetaExtensionCarrier (G := G))
  imageSet_eq : imageSet = rootThetaExtensionImageSet (G := G)
  hull : Set (RootThetaExtensionCarrier (G := G))
  hull_eq : hull = rootThetaExtensionHull (G := G)
  image_subset_hull : imageSet ⊆ hull

/-- Actual extension-valued image/hull carrier. -/
noncomputable def rootThetaExtensionHullCarrierData :
    RootThetaExtensionHullCarrierData (G := G) where
  imageSet := rootThetaExtensionImageSet (G := G)
  imageSet_eq := rfl
  hull := rootThetaExtensionHull (G := G)
  hull_eq := rfl
  image_subset_hull := rootThetaExtensionImage_subset_hull (G := G)

/-- Actual 2l-th power of a root Theta unit, in the algebraic closure. -/
noncomputable def rootThetaPowerPoint
    (j : ThetaLabel (l := l)) (v : V) :
    RootExtension (G := G) v :=
  (((paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v :
      (RootExtension (G := G) v)ˣ) : RootExtension (G := G) v) ^
    (2 * l.value))

/-- Actual power comparison: the 2l-th power of the root Theta unit is the
embedded completion qUnit power. -/
theorem rootThetaPowerPoint_eq_embedded_qUnit_power
    (j : ThetaLabel (l := l)) (v : V) :
    rootThetaPowerPoint (G := G) j v =
      (unitToAlgClosed (G.qUnit v) : RootExtension (G := G) v) ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := by
  unfold rootThetaPowerPoint
  exact congrArg Units.val
    (paperRootThetaUnit_pow_twoL (G := G) (thetaLabelToSigned (l := l) j) v)

/-- Exact missing map from the extension-valued root hull to the
completion-valued root-coefficient hull, with its normalized log comparison. -/
structure RootThetaToCompletionHullMapGap : Type where
  rootTensorLift : Prop
  completionUnitRoot : Prop
  hullMap : Prop
  normalizedLogComparison : Prop

/-- Exact missing map object. -/
def RootThetaToCompletionHullMapGapRequired : Prop :=
  Nonempty RootThetaToCompletionHullMapGap

/-- Consumer relation: the completion root-coefficient hull is not identified
with the extension root hull; an actual extension-to-completion map is the
exact missing object above, not a proved equality. -/
def CompletionHullIsOnlySurrogate : Prop :=
  RootThetaToCompletionHullMapGapRequired

end LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual
end
