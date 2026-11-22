import tmp.sheaf.n8.closure.EtaBasisChangeFinal

/-!
# Eta lattice-to-Q_p basis realization: exact gap

Available actual algebra (EtaBasisChangeFinal): from explicit Q_p-bases bM, bN,
diagonal SNF relation, integral D and D-coordinate relation,

  toMatrix bM bM f = diagonal(a) * D,
  det f = unit * prod a,  ||det f|| = ||prod a||.

Missing exact theorem: a full Z_p-lattice L in a Q_p-vector space V has a
Z_p-basis which is a Q_p-basis of V, and similarly for N=fL, matching the SNF
diagonal relation.  Mathlib's ZLattice basis API is for real vector spaces
(ZLattice.covolume, Basis.ofZLatticeBasis over R), not for Q_p.  No arbitrary
basis is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open Module Matrix
open scoped BigOperators
open LeanFormal.IUT.N8Closure.EtaBasisChangeAssembled
open LeanFormal.IUT.N8Closure.EtaBasisChangeFinal

namespace LeanFormal.IUT.N8Closure.EtaLatticeBasisRealizationActual

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact missing full-lattice-to-Q_p basis realization theorem. -/
def MissingFullLatticeToQpBasisTheorem : Prop :=
  ∀ (f : E →ₗ[ℚ_[p]] E), LinearMap.det f ≠ 0 →
    Nonempty (BasisChangeAssembledData (p := p) (n := n) f)

/-- Actual conditional closure: full lattice basis realization would give the
assembled basis-change data and hence the determinant/norm formula. -/
theorem det_norm_from_fullLatticeRealization
    (h : MissingFullLatticeToQpBasisTheorem (p := p) (E := E) (n := n))
    (f : E →ₗ[ℚ_[p]] E) (hf : LinearMap.det f ≠ 0) :
    (∃ u : ℤ_[p]ˣ,
        LinearMap.det f = (u : ℚ_[p]) *
          ((∏ i, (Classical.choice (h f hf)).a i : ℤ_[p]) : ℚ_[p])) ∧
      ‖LinearMap.det f‖ =
        ‖(((∏ i, (Classical.choice (h f hf)).a i : ℤ_[p])) : ℚ_[p])‖ :=
  det_norm_from_assembled (p := p) (Classical.choice (h f hf))

end LeanFormal.IUT.N8Closure.EtaLatticeBasisRealizationActual
