import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullLowerActual
import Mathlib.Tactic
/-!
# PIECE 1: `urNonzeroLabelHull` = closure of the ceiling region

Combines DONE donors:
* `Mzk1URThetaHullNonzeroActual.urNonzeroLabelHull_eq_closure_region_one`
* `Mzk1URThetaHullLowerActual.urLabelOneRegion_eq_ceilRegion`
to identify the nonzero-label hull with the closure of the ceiling region
`thetaTensorScaledRegion qVFamTensorPlaces qVFamTensorTuple (fun _ => urCeilC)`.
Needed for the packet-hull containment (PIECE 2). No root, no equality assumptions.
-/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroCeilActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullLowerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [DecidableEq qVFamTensorV]
variable (b : Bad (nativePlaceSelection T))

theorem urNonzeroLabelHull_eq_closure_ceilRegion :
    urNonzeroLabelHull (l := l) T b =
      closure (thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => urCeilC (l := l) T b)) := by
  rw [urNonzeroLabelHull_eq_closure_region_one (l := l) T b,
    urLabelOneRegion_eq_ceilRegion (l := l) T b]

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroCeilActual
end