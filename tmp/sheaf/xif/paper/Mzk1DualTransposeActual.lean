import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# GAP-DUAL-TRANSPOSE (A2): dual of a mapped lattice

For a nondegenerate bilinear form `B` on a `Q_p`-vector space `M`, a linear map
`e : M →_Qp M`, and a `Z_p`-lattice `L`, this file proves the membership form of
`(e L)^# = e^{-T} L^#`:

* `mem_padicIntegralTraceDualLattice_map_iff`:
  `x ∈ (L.map e)^# ↔ ∀ y ∈ L, B x (e y) ∈ Z_p`;
* `mem_padicIntegralTraceDualLattice_map_iff_leftAdjoint`:
  `x ∈ (L.map e)^# ↔ B.leftAdjointOfNondegenerate hB e x ∈ L^#`.

The inverse/image equality `(eL)^# = (e.leftAdjoint)⁻¹ (L^#)` is the next step;
it needs invertibility of the left adjoint (or `e` unitary) and is recorded as
a remaining GAP.  No sorry/axiom.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open LeanFormal.IUT.IntegralTraceDual

namespace LeanFormal.IUT.XiFPaper.Mzk1DualTransposeActual

variable {p : Nat} [Fact p.Prime]
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]

/-- Membership in the dual of a mapped lattice, in pairing form. -/
theorem mem_padicIntegralTraceDualLattice_map_iff
    (B : LinearMap.BilinForm ℚ_[p] M) (L : Submodule ℤ_[p] M)
    (e : M →ₗ[ℚ_[p]] M) (x : M) :
    x ∈ padicIntegralTraceDualLattice B (L.map (e.restrictScalars ℤ_[p])) ↔
      ∀ y ∈ L, B x (e y) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  rw [mem_padicIntegralTraceDualLattice_iff]
  constructor
  · intro h y hy
    exact h (e y) (Submodule.mem_map_of_mem (f := e.restrictScalars ℤ_[p]) hy)
  · intro h z hz
    rw [Submodule.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact h y hy

/-- The transpose form: membership in the dual of `e L` is membership of the
left adjoint of `e` in the dual of `L`. -/
theorem mem_padicIntegralTraceDualLattice_map_iff_leftAdjoint
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (L : Submodule ℤ_[p] M) (e : M →ₗ[ℚ_[p]] M) (x : M) :
    x ∈ padicIntegralTraceDualLattice B (L.map (e.restrictScalars ℤ_[p])) ↔
      B.leftAdjointOfNondegenerate hB e x ∈ padicIntegralTraceDualLattice B L := by
  have hAdj := B.isAdjointPairLeftAdjointOfNondegenerate hB e
  rw [mem_padicIntegralTraceDualLattice_map_iff]
  constructor
  · intro h
    rw [mem_padicIntegralTraceDualLattice_iff]
    intro y hy
    rw [hAdj x y]
    exact h y hy
  · intro h y hy
    rw [← hAdj x y]
    exact (mem_padicIntegralTraceDualLattice_iff.mp h) y hy

/-- Inverse/image form of the transpose: `(e L)^# = (e.leftAdjoint)^{-1}(L^#)`
as a `comap` equality.  No invertibility of `e` is needed for this membership
form (the map below is the left adjoint restricted to `Z_p`). -/
theorem padicIntegralTraceDualLattice_map_eq_comap
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (L : Submodule ℤ_[p] M) (e : M ≃ₗ[ℚ_[p]] M) :
    padicIntegralTraceDualLattice B
        (L.map ((e : M →ₗ[ℚ_[p]] M).restrictScalars ℤ_[p])) =
      (padicIntegralTraceDualLattice B L).comap
        ((B.leftAdjointOfNondegenerate hB (e : M →ₗ[ℚ_[p]] M)).restrictScalars ℤ_[p]) := by
  ext x
  rw [Submodule.mem_comap]
  exact mem_padicIntegralTraceDualLattice_map_iff_leftAdjoint B hB L
    (e : M →ₗ[ℚ_[p]] M) x


/-- X_G matrix-column form: the trace dual of the lattice spanned by columns
`v i` is the set of `x` whose pairings with every column are integral.
This is the column-pairing form of `X_G = (G · Z_p^r)^#`. -/
theorem mem_padicIntegralTraceDualLattice_span_range_iff
    (B : LinearMap.BilinForm ℚ_[p] M) {ι : Type*} (v : ι → M) (x : M) :
    x ∈ padicIntegralTraceDualLattice B
        (Submodule.span ℤ_[p] (Set.range v)) ↔
      ∀ i, B x (v i) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  constructor
  · intro h i
    exact (mem_padicIntegralTraceDualLattice_iff.mp h) (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  · intro h
    rw [mem_padicIntegralTraceDualLattice_iff]
    intro y hy
    have hspanle : Submodule.span ℤ_[p]
        (Set.range fun i => (B x) (v i)) ≤ (1 : Submodule ℤ_[p] ℚ_[p]) := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      exact h i
    have hy' : (B x) y ∈ Submodule.span ℤ_[p]
        (Set.range fun i => (B x) (v i)) := by
      have hm := Submodule.mem_map_of_mem
        (f := (B x).restrictScalars ℤ_[p]) hy
      rw [Submodule.map_span] at hm
      have hset : (⇑((B x).restrictScalars ℤ_[p]) '' Set.range v) =
          Set.range (fun i => (B x) (v i)) := by
        simpa [LinearMap.coe_restrictScalars, Set.range_comp, Function.comp_def] using
          (Set.range_comp (fun a => (B x) a) v).symm
      rw [hset] at hm
      exact hm
    exact hspanle hy'

/-- On an actual basis, the same column form is the dual-basis span form.
This aligns the column pairing with `padicIntegralTraceDualLattice_span_basis`. -/
theorem mem_padicIntegralTraceDualLattice_basis_iff
    (B : LinearMap.BilinForm ℚ_[p] M) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℚ_[p] M) (x : M) :
    x ∈ padicIntegralTraceDualLattice B (basisIntegralLattice b) ↔
      ∀ i, B x (b i) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  simpa [basisIntegralLattice] using
    (mem_padicIntegralTraceDualLattice_span_range_iff B (fun i => b i) x)

end LeanFormal.IUT.XiFPaper.Mzk1DualTransposeActual

end
