import tmp.sheaf.xif.paper.Mzk1P3DomainDecompositionMapActual
import tmp.sheaf.xif.paper.Mzk1P3TraceDualityCoefficientActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3DomainTraceActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P3DomainDecompositionMapActual
open LeanFormal.IUT.DifferentTraceProduct
/-- Domain-decomposition projection followed by the trace-duality coefficient
is the componentwise trace-duality coefficient. -/
theorem domainTraceCoefficient_projection {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra K (A i)]
    [∀ i, IsScalarTower R K (A i)] [∀ i, FiniteDimensional K (A i)]
    (lattices : ∀ i, Submodule R (A i)) :
    (Algebra.traceForm K (∀ i, A i)).dualSubmodule (Submodule.pi Set.univ lattices) =
      Submodule.pi Set.univ (fun i =>
        (Algebra.traceForm K (A i)).dualSubmodule (lattices i)) :=
  dualSubmodule_pi R K A lattices
end LeanFormal.IUT.XiFPaper.Mzk1P3DomainTraceActual
end