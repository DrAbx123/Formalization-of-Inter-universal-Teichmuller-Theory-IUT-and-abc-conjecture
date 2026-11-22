import tmp.sheaf.xif.paper.Mzk1A1LatticeInverseActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
/-! #A1 compare: actual q-lattice vs lambda-lattice at one block.

Proved: the actual qhat-lattice is contained in the lambda-lattice (A1.4).
The valuation/exponent comparison (A1.6) needs the normalized valuation and
ramification index interfaces; the exact missing items are recorded below. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1LatticeInverseActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The qhat-lattice used in the inverse-lattice file is exactly the actual
q-lattice `c0QLattice`. -/
theorem qhatLattice_eq_c0QLattice :
    qhatLattice T b = c0QLattice T b := rfl
/-- A1.4 at the actual source q-lattice: `qhat * O_L subset lambda * O_L`. -/
theorem c0QLattice_subset_lambdaLattice :
    c0QLattice T b ⊆ lambdaLattice T b := by
  intro z hz
  exact qhatLattice_subset_lambdaLattice T b (by simpa [qhatLattice_eq_c0QLattice] using hz)
/-- The inverse lambda-lattice contains the embedded q element. -/
theorem qVFamily_mem_inverseLambdaLattice_compare :
    ((qVFamily T b).q : rootBase T b) ∈ inverseLambdaLattice T b :=
  qVFamily_mem_inverseLambdaLattice T b
/-- Exact missing interfaces for A1.6; no hypothesis is added in this file. -/
def a1LatticeCompareMissing : List String :=
  [ "normalized valuation v_F on rootBase and v_L on rootNormedExtension",
    "ramification identity v_L(algebraMap x) = e * v_F(x)",
    "principal lattice description J_s = pi_F^(ceil(m/e)) O_F",
    "signed relative readout (1/d_F) log(mu(J)/mu(O)) = log||lambda||_L - delta with 0 <= delta < log p / e_F",
    "multi-generator Q_A subset J_A by per-generator integrality (no eta(Q_A) product assumption)" ]
theorem a1LatticeCompareMissing_length : a1LatticeCompareMissing.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1A1LatticeCompareActual
end