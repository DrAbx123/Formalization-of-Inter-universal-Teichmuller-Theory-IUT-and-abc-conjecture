import tmp.sheaf.xif.paper.S708QPilotRootLabelRegionNormActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
/-! # S717: tensor-lattice norm lemma and normalization check for S708
The root-label region at j=1 uses c_root = N/(2l), so its natural norm bound
is p^(-N/(2l)) = the rootImageRadius candidate, NOT p^(-N).  The S708 target
p^(-N) is the qPilot classical c_norm=N radius; using it for the root-label
region would be a false normalization whenever N>0 and 2l>1.  This file records
the corrected identification and the exact missing tensor-lattice norm lemma. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT.XiFPaper.S708QPilotRootLabelRegionNormActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.NumberFieldFinitePlace
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Exact root coefficient c_root = N/(2l) for the j=1 label. -/
noncomputable def rootLabelCoefficientAtOne : qVFamTensorV → Real :=
  qPilotRootLabelCoefficient T b (oneSignedLabel (l := l))
/-- Corrected first identification: the j=1 region is bounded by the root-image
radius p^(-N/(2l)), not by p^(-N). -/
def S717CorrectedRootLabelRegionNormBound : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotRootLabelRegion T b (oneSignedLabel (l := l)) →
      ‖x‖ ≤ Real.rpow (qVFamTensorP T b : Real)
        (-((qVFamily T b).order : Real) / (2 * (l.value : Real)))
/-- Exact missing tensor-lattice norm lemma at coefficient c: the fractional
tensor lattice is contained in the norm ball p^(-sum c). -/
def TensorFractionalLatticeNormLemma (c : qVFamTensorV → Real) : Prop :=
  ∀ x ∈ arithmeticTupleFractionalLattice
    (qVFamTensorPlaces T b) qVFamTensorTuple c,
      ‖x‖ ≤ Real.rpow (qVFamTensorP T b : Real) (-(∑ i, c i))
/-- The S717 exact goal is the tensor-lattice norm lemma at c_root. -/
def S717ExactGoal : Prop :=
  TensorFractionalLatticeNormLemma (l := l) T b (rootLabelCoefficientAtOne T b)
end LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
