import tmp.sheaf.xif.paper.Mzk1A1LatticeValuationActual
import tmp.sheaf.xif.paper.Mzk1A1LatticeInverseActual
import tmp.sheaf.xif.paper.PaperRootExtensionDiscreteValuationActual
import tmp.sheaf.xif.paper.Mzk1A1QhatSaturationReadoutActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
/-! #A1.6 precise valuation inputs (conditional gate record).

The two inputs needed to remove the conditionality of the qhat<->J_s saturated
identification are recorded as named Props.  The root-side discrete DVR and
uniformizer are available (`PaperRootExtensionDiscreteValuationActual`); the
base discrete valuation and the ramification identity are not constructed. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A1ValuationInputsActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeValuationActual
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1A1QhatSaturationReadoutActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Actual-source input 1: the lambda-lattice is the principal normalized
valuation lattice for the root-extension discrete valuation. -/
def A1PrincipalLatticeRecognition
    (bval : ↑(rootNormedExtension T b) -> Nat) (m : Nat) : Prop :=
  lambdaLattice T b = principalLattice bval m
/-- Actual-source input 2: the ramification identity for the base and root
normalized valuations. -/
def A1RamificationIdentity
    (aval : rootBase T b -> Nat) (bval : ↑(rootNormedExtension T b) -> Nat)
    (e : Nat) : Prop :=
  ∀ x : rootBase T b,
    bval (algebraMap (rootBase T b) (↑(rootNormedExtension T b)) x) = e * aval x
/-- Bundled precise valuation data; no inhabitant is claimed here. -/
def A1ValuationData : Prop :=
  ∃ (aval : rootBase T b -> Nat) (bval : ↑(rootNormedExtension T b) -> Nat)
    (m e : Nat), 0 < e ∧ A1RamificationIdentity T b aval bval e ∧
      A1PrincipalLatticeRecognition T b bval m
/-- Conditional qhat<->J_s statement from the bundled data, by the green
valuation composition. -/
theorem qVFamily_mem_saturatedLattice_of_valuationData
    (h : A1ValuationData T b) :
    ∃ (aval : rootBase T b -> Nat) (bval : ↑(rootNormedExtension T b) -> Nat)
      (m e : Nat),
      ((qVFamily T b).q : rootBase T b) ∈ saturatedLattice aval m e := by
  rcases h with ⟨aval, bval, m, e, he, hram, hLambda⟩
  exact ⟨aval, bval, m, e,
    qVFamily_mem_saturatedLattice (T := T) (b := b) aval bval m e he hram hLambda⟩
end LeanFormal.IUT.XiFPaper.Mzk1A1ValuationInputsActual
end