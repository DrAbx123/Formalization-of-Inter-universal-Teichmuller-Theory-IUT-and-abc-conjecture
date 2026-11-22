import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingProductActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual

/-!
# shehdd A657 hull product law consumer (Sha, read-only)

Hull **product law** (exact): the product Haar log-volume of the hull region is the
product of the per-place 1D root-extension Haar volumes, and the R/p product
region has the analogous exact product formula.  Re-exported read-only from the
green hull file `Mzk1HaarStrictScalingProductActual`:
* `hullRegion_toReal` (hull product law);
* `rpRegion_toReal` (R/p product law);
* `hullRegion_eq_s1902Hull`, `hullRegion_measure_lt_top`.

Scaling consequence (decision): the product law converts scalar scaling of each
1D factor into an ADDITIVE log-volume lever over the product, consistent with the
exact log scaling law `c3LogVolume_smul_norm` and the A655 direction decision.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullProductLawShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Hull product law: product Haar log-volume = product of 1D log-volumes. -/
theorem hull_product_law :
    (rootExtensionProductHaar T (hullRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rootImageRadius T b : Real))).toReal :=
  hullRegion_toReal T

/-- R/p product law: same exact product formula for the R/p region. -/
theorem rp_product_law :
    (rootExtensionProductHaar T (rpRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rpRadius T b))).toReal :=
  rpRegion_toReal T

theorem hull_eq_s1902Hull : hullRegion T = s1902Hull T :=
  hullRegion_eq_s1902Hull T

theorem hull_measure_lt_top : rootExtensionProductHaar T (hullRegion T) < ⊤ :=
  hullRegion_measure_lt_top T

structure ProductLawRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def productLawRows : List ProductLawRow :=
  [ ⟨"hull product law", "product Haar volume = product of 1D root-extension volumes (exact)", "GREEN_SOURCE"⟩
  , ⟨"R/p product law", "same exact product formula for rpRegion", "GREEN_SOURCE"⟩
  , ⟨"product scaling lever", "log of product = sum of per-coordinate log levers", "DECISION"⟩
  , ⟨"direction decision", "growing direction keeps positive total lever; shrinking fails Gap1", "DECISION"⟩
  , ⟨"scope", "consumer/audit only; named gaps unchanged", "INTEGRITY"⟩
  ]

theorem productLawRows_length : productLawRows.length = 5 := rfl

theorem productLawRows_statuses_ok :
    productLawRows.all (fun r =>
      r.status ∈ ["GREEN_SOURCE", "DECISION", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1HullProductLawShaActual

/-! ### Axiom gates (read-only re-exports) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullProductLawShaActual.hull_product_law
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullProductLawShaActual.rp_product_law
