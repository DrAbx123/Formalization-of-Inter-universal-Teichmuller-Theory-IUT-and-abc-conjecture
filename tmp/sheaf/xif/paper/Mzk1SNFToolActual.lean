import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! GAP-DUAL-SNF tool: Mathlib `Submodule.smithNormalForm` wrapper.

Over a PID `R` (in particular `Z_p`, a DVR), any submodule `N` of a finite
free `M` has bases `bM` of `M` and `bN` of `N` such that
`(bN i : M) = a i • bM (f i)` (Smith normal form).  This replaces the
previously-planned external SNF port.  No sorry/axiom. -/
noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual

open Module

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- Existence form of Smith normal form: basis of `M`, basis of `N`, an
embedding of indices and diagonal entries `a` with `bN i = a i • bM (f i)`. -/
theorem exists_smith_normal_form {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ (n : ℕ) (bM : Module.Basis ι R M) (bN : Module.Basis (Fin n) R N)
      (f : Fin n ↪ ι) (a : Fin n → R),
      ∀ i, (bN i : M) = a i • bM (f i) := by
  obtain ⟨n, snf⟩ := N.smithNormalForm b
  exact ⟨n, snf.bM, snf.bN, snf.f, snf.a, snf.snf⟩


end LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual
end