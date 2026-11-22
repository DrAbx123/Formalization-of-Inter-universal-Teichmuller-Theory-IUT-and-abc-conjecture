/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import Mathlib.Tactic
/-! # Exact interface for the two remaining product-Haar identifications -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ProductHaarIdentificationGapActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The exact P3 product carrier. -/
def P3ProductCarrier : Type := (b : Bad (nativePlaceSelection T)) → rootNormedExtension T b
/-- Missing identification: the C3 tensor integer region is the product unit region
under the field-product coordinate equivalence. No inhabitant is asserted. -/
structure TensorIntegerRegionProductIdentification (X Y : Type*) where
  e : X ≃ Y
  integerRegion : Set X
  productRegion : Set Y
  image_eq : e '' integerRegion = productRegion
/-- Missing identification: node06/09 region carrier is the P3 product carrier
with a Set.pi local region. No inhabitant is asserted. -/
structure P3CarrierProductIdentification (X : Type) where
  carrierEquiv : X ≃ P3ProductCarrier T
  region : Set X
  localRegion : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)
  region_image : carrierEquiv '' region = Set.pi Set.univ localRegion
/-- Audit rows. -/
def gapRows : List (String × String) :=
  [ ("tensorIntegerRegion product image", "missing equality e '' region = productRegion"),
    ("P3 carrier", "node06/09 X ≃ (b : Bad) → rootNormedExtension T b"),
    ("P3 local region", "missing equality region image = Set.pi localRegion"),
    ("product Haar", "applies only after the two identifications") ]
theorem gapRows_length : gapRows.length = 4 := rfl
#check TensorIntegerRegionProductIdentification
#check P3CarrierProductIdentification
#check P3ProductCarrier
end LeanFormal.IUT.XiFPaper.Mzk1ProductHaarIdentificationGapActual
end