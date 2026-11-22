/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleLawActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import Mathlib.Tactic

/-! # Mzk1CanonicalLandingQpilotActual — mainline canonical landing record (A664/A698)

Read-only landing record for the mainline canonical carrier bad-inverse scaling law:
the product-Haar law (scalar-free statement) is re-exported for general product
regions and the landing rows are recorded. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalLandingQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLawActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Landing re-export: bad-inverse product-Haar law (canonical). -/
theorem canonicalLanding_productHaar (e : Bad (nativePlaceSelection T) → Nat)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T e '' (Set.pi Set.univ S)) =
      (∏ b : Bad (nativePlaceSelection T),
          (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (Set.pi Set.univ S) :=
  badInvScale_productHaar_pi T e S

/-- Landing rows: mainline canonical and qpilot supplementary evidence. -/
def canonicalLandingRows : List (String × String) :=
  [ ("Mzk1CarrierBadInvScaleLawActual (canonical)", "GREEN (mainline)"),
    ("bad-inverse product-Haar law re-export", "GREEN"),
    ("qpilot BadInvScalingLaw / scaling log laws", "SUPPLEMENTARY (separate files)"),
    ("ObjectTightnessD1 calibration", "MAINLINE (read-only linkage)") ]

theorem canonicalLandingRows_length : canonicalLandingRows.length = 4 := rfl

#check canonicalLanding_productHaar
#check canonicalLandingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CanonicalLandingQpilotActual
end
