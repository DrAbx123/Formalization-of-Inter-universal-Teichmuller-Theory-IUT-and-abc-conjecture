import tmp.sheaf.n8.closure.EtaPAdicDetHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-!
# Eta lattice-index/determinant bridge: exact gap

Production PadicLatticeIndexFormula proves, for an explicit Smith normal form
of a full-rank Z_p-sublattice N <= M,

  Nat.card (M / N) = prod_i Nat.card (Z_p / (a_i)).

The missing theorem is the determinant side

  det_Qp(f) = unit * prod_i a_i

for the Q_p-linear map f represented by the Smith data, hence
||det_Qp f|| = index^{-1}.  Without that determinant/SNF comparison, Haar
uniqueness cannot be calibrated to det.

This file re-exports the actual SNF index arithmetic and records the exact
missing bridge; no arbitrary index or factor is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.deprecated false

open LeanFormal.IUT
open LeanFormal.IUT.PadicLatticeIndex

namespace LeanFormal.IUT.N8Closure.EtaLatticeIndexDetBridgeActual

universe u v

variable {p : Nat} [Fact p.Prime]
variable {κ : Type v} [Fintype κ]

/-- A concrete Smith normal form witness for a full-rank sublattice. -/
structure SNFIndexWitness (M : Type u) [AddCommGroup M] [Module ℤ_[p] M] where
  N : Submodule ℤ_[p] M
  bM : Module.Basis κ ℤ_[p] M
  bN : Module.Basis κ ℤ_[p] N
  a : κ → ℤ_[p]
  hSNF : ∀ i, (bN i : M) = a i • bM i

/-- Actual production SNF index formula: the index is the product of the
principal quotient cardinalities. -/
theorem snf_index_formula
    {M : Type u} [AddCommGroup M] [Module ℤ_[p] M]
    (W : SNFIndexWitness (p := p) (κ := κ) M) :
    Nat.card (M ⧸ W.N) =
      ∏ i, Nat.card (ℤ_[p] ⧸ Ideal.span ({W.a i} : Set ℤ_[p])) :=
  LeanFormal.IUT.PadicLatticeIndex.natCard_quotient_eq_prod_span_of_smithNormalForm
    W.hSNF

/-- Actual p-power form of the SNF index formula. -/
theorem snf_index_formula_pow
    {M : Type u} [AddCommGroup M] [Module ℤ_[p] M]
    (W : SNFIndexWitness (p := p) (κ := κ) M)
    (u : κ → ℤ_[p]ˣ) (k : κ → ℕ)
    (hunit : ∀ i, W.a i = (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    Nat.card (M ⧸ W.N) = p ^ ∑ i, k i :=
  LeanFormal.IUT.PadicLatticeIndex.natCard_quotient_eq_pow_sum_of_unit_mul_pow
    W.hSNF hunit

end LeanFormal.IUT.N8Closure.EtaLatticeIndexDetBridgeActual
