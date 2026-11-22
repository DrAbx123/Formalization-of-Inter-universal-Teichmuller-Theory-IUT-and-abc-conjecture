import LeanFormal.IUT.Foundations.LocalFields.DifferentTraceProduct
/-! P3 (R3.6): trace-duality coefficient lattice on finite products. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TraceDualityCoefficientActual
open LeanFormal.IUT.DifferentTraceProduct
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι] (A : ι → Type*)
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra K (A i)]
variable [∀ i, IsScalarTower R K (A i)] [∀ i, FiniteDimensional K (A i)]
/-- The trace-duality coefficient lattice on the product algebra. -/
noncomputable def traceDualityCoefficient : Submodule R (∀ i, A i) :=
  (Algebra.traceForm K (∀ i, A i)).dualSubmodule
    ((1 : Submodule (∀ i, A i) (∀ i, A i)).restrictScalars R)
/-- Product factorization of the trace-duality coefficient lattice. -/
theorem traceDualityCoefficient_eq_pi
    (lattices : ∀ i, Submodule R (A i)) :
    (Algebra.traceForm K (∀ i, A i)).dualSubmodule (Submodule.pi Set.univ lattices) =
      Submodule.pi Set.univ (fun i =>
        (Algebra.traceForm K (A i)).dualSubmodule (lattices i)) :=
  dualSubmodule_pi R K A lattices
end LeanFormal.IUT.XiFPaper.Mzk1P3TraceDualityCoefficientActual
end