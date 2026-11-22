import LeanFormal.IUT.Foundations.LocalFields.CompactIntegralSubmoduleFinite
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Topology.Algebra.Module.Compact

/-!
# Actual integral lattices in finite-dimensional Qp spaces

Restriction along Zp -> Qp supplies the integral action. A finite Qp basis
constructs an open, finitely generated Zp lattice. Compact integral
submodules and integral spans of compact sets are then finite and free;
their compactness follows from the actual compact scalar ring Zp.
-/

namespace LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]

scoped instance padicIntegerModule : Module ℤ_[p] M :=
  Module.compHom M (algebraMap ℤ_[p] ℚ_[p])

open scoped LeanFormal.IUT.FinitePadicIntegralLattice

theorem padicInteger_smul_eq (z : ℤ_[p]) (x : M) : z • x = (z : ℚ_[p]) • x := rfl

scoped instance padicIntegerScalarTower : IsScalarTower ℤ_[p] ℚ_[p] M :=
  IsScalarTower.of_compHom ℤ_[p] ℚ_[p] M

scoped instance padicIntegerContinuousSMul : ContinuousSMul ℤ_[p] M where
  continuous_smul := by
    change Continuous (fun z : ℤ_[p] × M => (z.1 : ℚ_[p]) • z.2)
    exact (PadicInt.isOpenEmbedding_coe.continuous.comp continuous_fst).smul continuous_snd

scoped instance padicIntegerNoZeroSMulDivisors : NoZeroSMulDivisors ℤ_[p] M where
  eq_zero_or_eq_zero_of_smul_eq_zero {z} {x} h := by
    rw [padicInteger_smul_eq] at h
    rcases smul_eq_zero.mp h with hz | hx
    · left
      apply Subtype.ext
      exact hz
    · exact Or.inr hx

def padicBasisOfIntegralBasis {κ : Type*} (S : Submodule ℤ_[p] M)
    (basis : Module.Basis κ ℤ_[p] S)
    (hspan : Submodule.span ℚ_[p] (S : Set M) = ⊤) : Module.Basis κ ℚ_[p] M := by
  have hintegral : Submodule.span ℤ_[p] (Set.range (fun j => (basis j : M))) = S := by
    change Submodule.span ℤ_[p] (Set.range (S.subtype ∘ basis)) = S
    rw [Set.range_comp, ← Submodule.map_span, basis.span_eq]
    simp
  apply Module.Basis.mk
    ((LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp
      (basis.linearIndependent.map' S.subtype (by simp)))
  change ⊤ ≤ Submodule.span ℚ_[p] (Set.range (fun j => (basis j : M)))
  rw [← Submodule.span_span_of_tower ℤ_[p] ℚ_[p], hintegral, hspan]

theorem padicBasisOfIntegralBasis_apply {κ : Type*} (S : Submodule ℤ_[p] M)
    (basis : Module.Basis κ ℤ_[p] S)
    (hspan : Submodule.span ℚ_[p] (S : Set M) = ⊤) (j : κ) :
    padicBasisOfIntegralBasis S basis hspan j = (basis j : M) := by
  simp [padicBasisOfIntegralBasis]

variable [FiniteDimensional ℚ_[p] M]
variable {κ : Type*} [Finite κ]

def basisIntegralLattice (basis : Module.Basis κ ℚ_[p] M) : Submodule ℤ_[p] M :=
  Submodule.span ℤ_[p] (Set.range basis)

omit [FiniteDimensional ℚ_[p] M] in
theorem basisIntegralLattice_fg (basis : Module.Basis κ ℚ_[p] M) :
    (basisIntegralLattice basis).FG := Submodule.fg_span (Set.finite_range basis)

omit [FiniteDimensional ℚ_[p] M] in
theorem mem_basisIntegralLattice_of_repr (basis : Module.Basis κ ℚ_[p] M) (x : M)
    (hx : ∀ i, ‖basis.repr x i‖ ≤ 1) : x ∈ basisIntegralLattice basis := by
  classical
  letI := Fintype.ofFinite κ
  rw [← basis.sum_repr x]
  apply Submodule.sum_mem
  intro i _
  have hterm := (basisIntegralLattice basis).smul_mem
    (⟨basis.repr x i, hx i⟩ : ℤ_[p]) (Submodule.subset_span ⟨i, rfl⟩)
  simpa only [padicInteger_smul_eq (p := p)] using hterm

theorem isOpen_basisIntegralLattice (basis : Module.Basis κ ℚ_[p] M) :
    IsOpen (basisIntegralLattice basis : Set M) := by
  classical
  letI := Fintype.ofFinite κ
  let coordinates := basis.equivFun.toContinuousLinearEquiv
  let neighborhood : Set M := {x | ∀ i, ‖coordinates x i‖ < 1}
  have hopen : IsOpen neighborhood := by
    simp only [neighborhood, Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      (continuous_norm.comp ((continuous_apply i).comp coordinates.continuous)) continuous_const)
  have hzero : (0 : M) ∈ neighborhood := by
    intro i
    simp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have htranslated : IsOpen {y : M | y - x ∈ neighborhood} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hself : x ∈ {y : M | y - x ∈ neighborhood} := by
    simpa only [Set.mem_setOf_eq, sub_self] using hzero
  apply Filter.mem_of_superset (htranslated.mem_nhds hself)
  intro y hy
  change y ∈ basisIntegralLattice basis
  have hdifference : y - x ∈ basisIntegralLattice basis :=
    mem_basisIntegralLattice_of_repr basis (y - x) (fun i => (hy i).le)
  simpa only [sub_add_cancel] using (basisIntegralLattice basis).add_mem hdifference hx

theorem isOpen_of_basis_mem (basis : Module.Basis κ ℚ_[p] M) (S : Submodule ℤ_[p] M)
    (hS : ∀ i, basis i ∈ S) : IsOpen (S : Set M) := by
  have hinclusion : basisIntegralLattice basis ≤ S :=
    Submodule.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hS i)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hopen : IsOpen {y : M | y - x ∈ basisIntegralLattice basis} :=
    (isOpen_basisIntegralLattice basis).preimage (continuous_id.sub continuous_const)
  have hself : x ∈ {y : M | y - x ∈ basisIntegralLattice basis} := by
    simpa only [Set.mem_setOf_eq, sub_self] using (basisIntegralLattice basis).zero_mem
  apply Filter.mem_of_superset (hopen.mem_nhds hself)
  intro y hy
  change y ∈ S
  simpa only [sub_add_cancel] using S.add_mem (hinclusion hy) hx

theorem exists_basis_norm_le_one :
    ∃ basis : Module.Basis (Fin (Module.finrank ℚ_[p] M)) ℚ_[p] M, ∀ i, ‖basis i‖ ≤ 1 := by
  classical
  let basis := Module.finBasis ℚ_[p] M
  have hsmall (i : Fin (Module.finrank ℚ_[p] M)) :
      ∃ a : ℚ_[p], 0 < ‖a‖ ∧ ‖a‖ < 1 / (‖basis i‖ + 1) :=
    NormedField.exists_norm_lt ℚ_[p] (by positivity)
  choose scalar hpositive hbound using hsmall
  let units : (i : Fin (Module.finrank ℚ_[p] M)) → ℚ_[p]ˣ :=
    fun i => Units.mk0 (scalar i) (norm_pos_iff.mp (hpositive i))
  refine ⟨basis.unitsSMul units, ?_⟩
  intro i
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, norm_smul]
  change ‖scalar i‖ * ‖basis i‖ ≤ 1
  have hproduct : ‖scalar i‖ * (‖basis i‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp (hbound i)
  exact (mul_le_mul_of_nonneg_left (by linarith : ‖basis i‖ ≤ ‖basis i‖ + 1)
    (norm_nonneg _)).trans hproduct.le

theorem finite_of_isCompact (S : Submodule ℤ_[p] M) (hS : IsCompact (S : Set M)) :
    Module.Finite ℤ_[p] S := by
  let basis := Module.finBasis ℚ_[p] M
  exact CompactIntegralSubmodule.finite_of_isCompact_of_open_fg S (basisIntegralLattice basis)
    hS (isOpen_basisIntegralLattice basis) (basisIntegralLattice_fg basis)

theorem finite_span_of_isCompact (S : Set M) (hS : IsCompact S) :
    Module.Finite ℤ_[p] (Submodule.span ℤ_[p] S) := by
  let basis := Module.finBasis ℚ_[p] M
  exact CompactIntegralSubmodule.finite_span_of_isCompact_of_open_fg S
    (basisIntegralLattice basis) hS (isOpen_basisIntegralLattice basis)
    (basisIntegralLattice_fg basis)

theorem isCompact_span_of_isCompact (S : Set M) (hS : IsCompact S) :
    IsCompact (Submodule.span ℤ_[p] S : Set M) := by
  have hfinite := finite_span_of_isCompact (p := p) S hS
  exact Submodule.isCompact_of_fg (Module.Finite.iff_fg.mp hfinite)

theorem free_of_isCompact (S : Submodule ℤ_[p] M) (hS : IsCompact (S : Set M)) :
    Module.Free ℤ_[p] S := by
  letI := finite_of_isCompact (p := p) S hS
  infer_instance

theorem free_span_of_isCompact (S : Set M) (hS : IsCompact S) :
    Module.Free ℤ_[p] (Submodule.span ℤ_[p] S) := by
  letI := finite_span_of_isCompact (p := p) S hS
  infer_instance

omit [FiniteDimensional ℚ_[p] M] in
theorem finrank_of_full_integral_submodule (S : Submodule ℤ_[p] M)
    [Module.Finite ℤ_[p] S] [Module.Free ℤ_[p] S]
    (hspan : Submodule.span ℚ_[p] (S : Set M) = ⊤) :
    Module.finrank ℤ_[p] S = Module.finrank ℚ_[p] M := by
  classical
  let basis := Module.Free.chooseBasis ℤ_[p] S
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ_[p] S)
  rw [Module.finrank_eq_card_basis basis,
    Module.finrank_eq_card_basis (padicBasisOfIntegralBasis S basis hspan)]

end

end LeanFormal.IUT.FinitePadicIntegralLattice
