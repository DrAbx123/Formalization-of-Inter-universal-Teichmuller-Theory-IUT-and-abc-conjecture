/- G-K 7.3 local topology, batch 2: topologies on the chart L-point spaces. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGKLocalTopologyActual
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

noncomputable section
open Polynomial MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual

/-- The affine chart-0 L-point space (subspace of L^2; topology inherited). -/
def chart0PointSpace (n : Nat) (L : Type) [Field L] [Algebra ℚ L] [TopologicalSpace L] :=
  {p : L × L // p ∈ chart0Points n L}

/-- The affine infinity-chart L-point space. -/
def chartInfPointSpace (n : Nat) (L : Type) [Field L] [Algebra ℚ L] [TopologicalSpace L] :=
  {p : L × L // p ∈ chartInfPoints n L}

/-- In a topological field, the chart-0 point set is closed. -/
theorem chart0Points_isClosed {L : Type} [Field L] [Algebra ℚ L] [TopologicalSpace L]
    [IsTopologicalRing L] [T1Space L] (n : Nat) : IsClosed (chart0Points n L) := by
  have hcont : Continuous (fun p : L × L => p.1 ^ n + p.2 ^ n) := by fun_prop
  have h1 : IsClosed ({(1 : L)} : Set L) := isClosed_singleton
  exact h1.preimage hcont

/-- In a topological field, the infinity-chart point set is closed. -/
theorem chartInfPoints_isClosed {L : Type} [Field L] [Algebra ℚ L] [TopologicalSpace L]
    [IsTopologicalRing L] [T1Space L] (n : Nat) : IsClosed (chartInfPoints n L) := by
  have hcont : Continuous (fun p : L × L => 1 + p.1 ^ n - p.2 ^ n) := by fun_prop
  have h1 : IsClosed ({(0 : L)} : Set L) := isClosed_singleton
  have hmem : chartInfPoints n L = {p : L × L | 1 + p.1 ^ n - p.2 ^ n = 0} := by
    ext p
    simp [chartInfPoints, sub_eq_zero]
  rw [hmem]
  exact h1.preimage hcont

#print axioms chart0Points_isClosed
#print axioms chartInfPoints_isClosed
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual
