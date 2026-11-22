import tmp.sheaf.xif.paper.PaperRootThetaHullCarrierGapActual
import tmp.sheaf.xif.paper.PaperRootThetaProductCarrierActual

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S653RootThetaTensorHullCarrierGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaHullCarrierGapActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionEquivActual
open scoped BigOperators Pointwise

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual pointwise map from the root-extension product to the source
spectral-norm product carrier. -/
noncomputable def rootThetaProductImageMap
    (x : RootThetaCarrier (G := G)) : RootThetaProductCarrier (G := G) :=
  fun v => rootExtensionEquivUnits (G := G) v (x v)

theorem rootThetaProductImageMap_imagePoint
    (j : ThetaLabel (l := l)) :
    rootThetaProductImageMap (G := G) (paperRootThetaImagePointTheta (G := G) j) =
      rootThetaProductImagePoint (G := G) j := rfl

/-- The product image of the actual nonzero root image is the actual product
root image set. -/
theorem rootThetaProductImageMap_imageSet :
    rootThetaProductImageMap (G := G) ''
        paperNonzeroRootThetaImageSet (G := G) =
      rootThetaProductImageSet (G := G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨paperRootThetaImagePointTheta (G := G) j, ⟨j, rfl⟩, rfl⟩

/-- Universe-lifted tensor-hull carrier matching the actual product carrier. -/
structure RootThetaTensorHullCarrierGapAt where
  tensorCarrier : Type (max u v)
  imageMap : RootThetaCarrier (G := G) → tensorCarrier
  imageSet : Set tensorCarrier
  imageSet_eq : imageSet = imageMap '' paperNonzeroRootThetaImageSet (G := G)
  unitReference : Set tensorCarrier
  lambdaHull : Set tensorCarrier
  image_subset_hull : imageSet ⊆ lambdaHull
  carrier_compat : Prop

/-- Conditional actual universe-lifted tensor-hull carrier, using the actual
product carrier, product unit ball/unitReference, and the exact root norm bound. -/
noncomputable def rootThetaTensorHullCarrierGapAtOfNormBound
    (hroot : RootThetaRootNormBound (G := G)) :
    RootThetaTensorHullCarrierGapAt (G := G) where
  tensorCarrier := RootThetaProductCarrier (G := G)
  imageMap := rootThetaProductImageMap (G := G)
  imageSet := rootThetaProductImageSet (G := G)
  imageSet_eq := (rootThetaProductImageMap_imageSet (G := G)).symm
  unitReference := rootThetaUnitBall (G := G)
  lambdaHull := rootThetaUnitBall (G := G)
  image_subset_hull := rootThetaProductImageSet_subset_unitBall (G := G) hroot
  carrier_compat := RootThetaRootNormBound (G := G)

/-- Exact minimal gap: the actual root norm bound on each product factor,
plus the original gap structure's Type-0 carrier restriction. -/
def MinimalRootThetaTensorHullCarrierGap : Prop :=
  RootThetaRootNormBound (G := G)

theorem rootThetaTensorHullCarrierGapAtOfNormBound_exists
    (hroot : RootThetaRootNormBound (G := G)) :
    Nonempty (RootThetaTensorHullCarrierGapAt (G := G)) :=
  ⟨rootThetaTensorHullCarrierGapAtOfNormBound (G := G) hroot⟩

end LeanFormal.IUT.XiFPaper.S653RootThetaTensorHullCarrierGapActual

end
