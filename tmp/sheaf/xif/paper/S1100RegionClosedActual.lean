import tmp.sheaf.xif.paper.S1098MeasurabilityActual
import tmp.sheaf.xif.paper.S863ProductImageCompactActual
import tmp.sheaf.xif.paper.S839PaperRootMinimalProductCompactActual

/-! # S1100: closedness/measurability of paperLambdaORegion

paperLambdaORegion(cRoot) is exactly the S863 product lattice
  s839FractionalLattice * s839HolomorphicLattice
(coercion to Set is rfl).  S863 records its closedness as the exact
S863ProductClosed hypothesis; its compactness route is also exact
(S863ProductImageEq).  Therefore closedness/measurability are reduced to that
existing exact condition.

The direct S900 Submodule.closed_of_finiteDimensional pattern does not apply:
it requires a finite-dimensional submodule over a nontrivially normed field,
while the lattice is a Z_p-submodule (Z_p is not a field).  No fake closedness
is asserted. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1100RegionClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1098MeasurabilityActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The lambda-O region is the S863 product lattice (same set). -/
theorem s1100Region_eq_product :
    paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b) =
      ((s839FractionalLattice (l := l) T b *
        s839HolomorphicLattice (l := l) T b :
          Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b)) := rfl

/-- S863's exact product-closedness gives the S1098 closedness input. -/
theorem s1100RegionClosed_of_S863
    (h : S863ProductClosed (l := l) T b) :
    S1098RegionClosedRequired (l := l) T b := by
  rw [s1100Region_eq_product (l := l) T b]
  exact h

/-- Compactness gives closedness (T2), hence the S1098 closedness input. -/
theorem s1100RegionClosed_of_compact
    (h : IsCompact (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b))) :
    S1098RegionClosedRequired (l := l) T b :=
  h.isClosed

/-- Exact minimum: S863 product closedness (or compactness) for the region. -/
def S1100ExactMinimum : Prop :=
  S863ProductClosed (l := l) T b ∨
    IsCompact (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b))

end LeanFormal.IUT.XiFPaper.S1100RegionClosedActual

end
