/- J_b (root lattice) as the j=1 rootThetaRegion, and J_b ⊆ rootNormHull (paper Θ).

  `J_b = F(cP/(2l)) * O_hol` is the rootThetaRegion at a signed label whose Gaussian
  exponent is 1: `rootThetaRegion places tuple rootHalfCoefficient oneLabel` with
  `(gaussExponent oneLabel.1).toNat = 1`.  Since `rootNormHull` is the closure of the
  union of all such label regions, `J_b ⊆ rootNormHull` follows immediately.

  THE WEIGHT IDENTITY is the DONE `Mzk1ULR0QMEndpointActual.sum_weight_nu_eq_neg_Mpaper`:
  `sum_b (thetaLamWeight_b/(2l)) * nu(J_b) = -M_paper_v2` (inputs: nu(J_b) = -cP_b log p
  [Mzk1URBadPlaceActualMapActual.badPlaceQRegion_nu], the R0-b crosswalk and Qb fiber log
  extraction).  This file does NOT reprove it; it only adds the geometric J_b containment.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.Mzk1ULR0QMEndpointActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2JbRootMassRouteFreshActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0QMEndpointActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]

/-- **J_b 的几何定义**：Gaussian 指数为 1 的标签对应的 rootThetaRegion。 -/
noncomputable def rootLatticeJ
    (oneLabel : SignedLabel l.value) : Set (qVFamTensorBlock T b) :=
  rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b) oneLabel

/-- **J_b ⊆ rootNormHull**（论文 Θ）：`rootNormHull` 是所有标签区域的闭包并。 -/
theorem rootLatticeJ_subset_rootNormHull
    (oneLabel : SignedLabel l.value) :
    rootLatticeJ (l := l) T b oneLabel ⊆ rootNormHull (l := l) T b := by
  intro x hx
  unfold rootLatticeJ at hx
  change x ∈ closure (rootThetaImageSet (l := l)
    (qVFamTensorPlaces T b) qVFamTensorTuple (rootHalfCoefficient (l := l) T b))
  exact subset_closure (Set.mem_iUnion.mpr ⟨oneLabel, hx⟩)

#print axioms rootLatticeJ_subset_rootNormHull

end LeanFormal.IUT.XiFPaper.Mzk1G1F2JbRootMassRouteFreshActual
