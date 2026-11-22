/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleLawActual
import tmp.sheaf.xif.paper.Mzk1HullProductScalingQpilotActual
import tmp.sheaf.xif.paper.Mzk1BadPartProductLogQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual

/-! # Mzk1CarrierBadInvSupplementQpilotActual — carrier bad-inv split supplement (A663)

Read-only supplementary evidence around the mainline canonical carrier bad-inverse
scaling law: re-exports the image/product-Haar laws for general product regions
and records the linkage to the qpilot product closed-ball scaling and bad-part
product log laws.  The canonical file is not overwritten. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvSupplementQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLawActual
open LeanFormal.IUT.XiFPaper.Mzk1HullProductScalingQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1BadPartProductLogQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Supplement: image law of the bad-inverse scaling on a general product region
(mainline re-export). -/
theorem carrierBadInv_image_pi (e : Bad (nativePlaceSelection T) → Nat)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    badInvScale T e '' (Set.pi Set.univ S) =
      Set.pi Set.univ (fun b =>
        (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (e b))⁻¹) • S b) :=
  badInvScale_image_pi T e S

/-- Supplement: product-Haar law of the bad-inverse scaling (mainline re-export). -/
theorem carrierBadInv_productHaar (e : Bad (nativePlaceSelection T) → Nat)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T e '' (Set.pi Set.univ S)) =
      (∏ b : Bad (nativePlaceSelection T),
          (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (Set.pi Set.univ S) :=
  badInvScale_productHaar_pi T e S

/-- Rows for the carrier bad-inv supplement. -/
def carrierBadInvRows : List (String × String) :=
  [ ("mainline carrier bad-inv scale law", "GREEN (canonical, read-only)"),
    ("bad-inverse image of product region", "GREEN (re-export)"),
    ("bad-inverse product Haar law", "GREEN (re-export)"),
    ("qpilot product closed-ball scaling + bad-part log", "GREEN (supplementary)") ]

theorem carrierBadInvRows_length : carrierBadInvRows.length = 4 := rfl

#check carrierBadInv_image_pi
#check carrierBadInv_productHaar
#check carrierBadInvRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvSupplementQpilotActual
end
