/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GeneralDualVolumeActual

/-! # Restricted determinant volume: conditional wrapper (task-109) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1RestrictedDetConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1GeneralDualVolumeActual
variable {M : Type*} [AddCommGroup M] [MeasurableSpace M]
/-- The restricted determinant Haar product identity, conditional on the exact
relative scaling pair.  This is a re-export of the task-104 green core. -/
theorem restricted_det_product_of_scaling
    (μ : Measure M) (L O Ldual Odual : AddSubgroup M) (c : ENNReal)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hL : μ (L : Set M) = c * μ (O : Set M))
    (hD : μ (Ldual : Set M) = c⁻¹ * μ (Odual : Set M)) :
    μ (L : Set M) * μ (Ldual : Set M) = μ (O : Set M) * μ (Odual : Set M) :=
  relativeHaarVolume_product_of_scaling μ L O Ldual Odual c hc0 hctop hL hD
def restrictedDetRows : List (String × String) :=
  [ ("restricted_det_product_of_scaling", "green conditional core"),
    ("SNF/det-Haar", "GAP") ]
theorem restrictedDetRows_length : restrictedDetRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RestrictedDetConditionalActual
