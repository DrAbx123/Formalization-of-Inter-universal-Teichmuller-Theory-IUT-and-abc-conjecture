import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellScalarClosure

/-!
# The actual logarithmic shell as an integral lattice

The valuation integers and the actual scaled full-unit logarithmic image
are constructed as Zp submodules of the local field. Compactness supplies
finite generation and freeness. An actual Qp basis inside the integers,
and hence inside the log-shell, verifies full rational-padic span.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

def valuationIntegerLattice : Submodule ℤ_[p] K where
  carrier := Integers K
  zero_mem' := (Integers K).zero_mem
  add_mem' := (Integers K).add_mem
  smul_mem' z x hx := by
    change z • x ∈ Integers K
    rw [padicInteger_smul_eq]
    apply (mem_integers_iff _).mpr
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) z.property).trans ((mem_integers_iff _).mp hx)

def integralLogShellLattice : Submodule ℤ_[p] K where
  carrier := integralLogShell (K := K) (p := p)
  zero_mem' := (integralLogShell (K := K) (p := p)).zero_mem
  add_mem' := (integralLogShell (K := K) (p := p)).add_mem
  smul_mem' z x hx := by
    change z • x ∈ integralLogShell (K := K) (p := p)
    rw [padicInteger_smul_eq, Algebra.smul_def]
    exact integralLogShell_padicInt_mul_mem z hx

theorem valuationIntegerLattice_le_integralLogShellLattice :
    valuationIntegerLattice (K := K) (p := p) ≤ integralLogShellLattice (K := K) (p := p) :=
  integers_subset_integralLogShell (K := K) (p := p)

omit [CharZero K] [CompleteSpace K] in
theorem isCompact_valuationIntegerLattice :
    IsCompact (valuationIntegerLattice (K := K) (p := p) : Set K) := by
  have heq : (valuationIntegerLattice (K := K) (p := p) : Set K) =
      Metric.closedBall (0 : K) 1 := by
    ext x
    change (‖x‖ ≤ 1) ↔ dist x 0 ≤ 1
    simp only [dist_eq_norm, sub_zero]
  rw [heq]
  exact isCompact_closedBall (0 : K) 1

theorem isCompact_integralLogShellLattice :
    IsCompact (integralLogShellLattice (K := K) (p := p) : Set K) :=
  isCompact_integralLogShell (K := K) (p := p)

variable [FiniteDimensional ℚ_[p] K]

instance valuationIntegerLatticeFinite :
    Module.Finite ℤ_[p] (valuationIntegerLattice (K := K) (p := p)) :=
  finite_of_isCompact (p := p) _ isCompact_valuationIntegerLattice

instance integralLogShellLatticeFinite :
    Module.Finite ℤ_[p] (integralLogShellLattice (K := K) (p := p)) :=
  finite_of_isCompact (p := p) _ isCompact_integralLogShellLattice

instance valuationIntegerLatticeFree :
    Module.Free ℤ_[p] (valuationIntegerLattice (K := K) (p := p)) :=
  free_of_isCompact (p := p) _ isCompact_valuationIntegerLattice

instance integralLogShellLatticeFree :
    Module.Free ℤ_[p] (integralLogShellLattice (K := K) (p := p)) :=
  free_of_isCompact (p := p) _ isCompact_integralLogShellLattice

theorem exists_basis_mem_integralLogShellLattice :
    ∃ basis : Module.Basis (Fin (Module.finrank ℚ_[p] K)) ℚ_[p] K,
      ∀ i, basis i ∈ integralLogShellLattice (K := K) (p := p) := by
  obtain ⟨basis, hnorm⟩ := exists_basis_norm_le_one (p := p) (M := K)
  refine ⟨basis, ?_⟩
  intro i
  change basis i ∈ integralLogShell (K := K) (p := p)
  exact integers_subset_integralLogShell (p := p) ((mem_integers_iff _).mpr (hnorm i))

theorem span_padic_integralLogShellLattice_eq_top :
    Submodule.span ℚ_[p] (integralLogShellLattice (K := K) (p := p) : Set K) = ⊤ := by
  obtain ⟨basis, hmem⟩ := exists_basis_mem_integralLogShellLattice (K := K) (p := p)
  apply top_unique
  rw [← basis.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact hmem i

theorem finrank_integralLogShellLattice :
    Module.finrank ℤ_[p] (integralLogShellLattice (K := K) (p := p)) =
      Module.finrank ℚ_[p] K :=
  finrank_of_full_integral_submodule _ (span_padic_integralLogShellLattice_eq_top (p := p))

end

end LeanFormal.IUT.LocalFieldLogarithm
