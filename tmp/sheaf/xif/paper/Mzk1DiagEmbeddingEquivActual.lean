import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-! CONDITIONAL/GAP-step: definitions for the diagonal dual quotient chain.
This file is the definition base only (integer-product map, integral lattice,
diagonal dual lattices).  Linear equivalence/quotient proofs are GAP.
No sorry/axiom. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual

open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

/-- The integral coordinate lattice in `d → Q_p`. -/
def coordSmall : Submodule (PadicInt p) (d → ℚ_[p]) :=
  Submodule.pi Set.univ (fun _ =>
    Submodule.span (PadicInt p) {(1 : ℚ_[p])})

/-- Componentwise integer embedding (function form). -/
def integerProductEmbedding (x : d → PadicInt p) : d → ℚ_[p] :=
  fun i => algebraMap (PadicInt p) ℚ_[p] (x i)

/-- The dual diagonal lattice `XG(f) = ∏ p^{f_i} Z_p` in `d → Q_p`. -/
def coordDual (f : d → Nat) : Submodule (PadicInt p) (d → ℚ_[p]) :=
  Submodule.pi Set.univ (fun i =>
    Submodule.span (PadicInt p) {((p : ℚ_[p]) ^ (f i))})

/-- The integer-ambient dual diagonal lattice. -/
def coordDualInt (f : d → Nat) : Submodule (PadicInt p) (d → PadicInt p) :=
  diagLatticeSubmodule (p := p) (d := d) f

end LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
end