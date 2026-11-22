import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.MeasureTheory.Group.Measure

/-!
# The actual integral lattice and residue kernel in finite p-adic coordinates

The lattice is the image of the entire product of p-adic integer rings.
Its first residue kernel consists exactly of multiples of p. This is the
concrete finite-index input for the Haar p-scaling formula, not a supplied
lattice or index field.
-/

namespace LeanFormal.IUT.PadicIntegerProductLattice

open scoped Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*}

def integerProductEmbedding : (ι → ℤ_[p]) →+ (ι → ℚ_[p]) where
  toFun x i := (x i : ℚ_[p])
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

def padicIntegerCoordinateLattice : Set (ι → ℚ_[p]) :=
  Set.range (integerProductEmbedding (p := p) (ι := ι))

theorem continuous_integerProductEmbedding :
    Continuous (integerProductEmbedding (p := p) (ι := ι)) :=
  continuous_pi (fun i => PadicInt.isOpenEmbedding_coe.continuous.comp (continuous_apply i))

theorem isOpenEmbedding_integerProductEmbedding [Finite ι] :
    Topology.IsOpenEmbedding (integerProductEmbedding (p := p) (ι := ι)) :=
  Topology.IsOpenEmbedding.piMap (fun _ => PadicInt.isOpenEmbedding_coe)

theorem isCompact_padicIntegerCoordinateLattice :
    IsCompact (padicIntegerCoordinateLattice (p := p) (ι := ι)) :=
  isCompact_range continuous_integerProductEmbedding

theorem isOpen_padicIntegerCoordinateLattice [Finite ι] :
    IsOpen (padicIntegerCoordinateLattice (p := p) (ι := ι)) := by
  change IsOpen (Set.range (integerProductEmbedding (p := p) (ι := ι)))
  simpa only [Set.image_univ] using
    (isOpenEmbedding_integerProductEmbedding (p := p) (ι := ι)).isOpenMap Set.univ isOpen_univ

theorem zero_mem_padicIntegerCoordinateLattice :
    (0 : ι → ℚ_[p]) ∈ padicIntegerCoordinateLattice (p := p) :=
  ⟨0, map_zero integerProductEmbedding⟩

def integerProductResidueHom : (ι → ℤ_[p]) →+ (ι → ZMod (p ^ 1)) where
  toFun x i := PadicInt.toZModPow 1 (x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem integerProductResidueHom_surjective :
    Function.Surjective (integerProductResidueHom (p := p) (ι := ι)) := by
  intro x
  refine ⟨fun i => ((x i).val : ℤ_[p]), ?_⟩
  ext i
  simp [integerProductResidueHom]

theorem mem_integerProductResidueHom_ker_iff (x : ι → ℤ_[p]) :
    x ∈ (integerProductResidueHom (p := p)).ker ↔
      ∃ y : ι → ℤ_[p], ∀ i, x i = (p : ℤ_[p]) * y i := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  change (∀ i, PadicInt.toZModPow 1 (x i) = 0) ↔ _
  constructor
  · intro hx
    have hdiv : ∀ i, (p : ℤ_[p]) ∣ x i := by
      intro i
      have hker : x i ∈ RingHom.ker (PadicInt.toZModPow 1) := hx i
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
      simpa only [pow_one] using hker
    choose y hy using hdiv
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩ i
    rw [hy i]
    change (p : ℤ_[p]) * y i ∈ RingHom.ker (PadicInt.toZModPow 1)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
    exact dvd_mul_right _ _

instance integerProductResidueHom_ker_finiteIndex [Finite ι] :
    (integerProductResidueHom (p := p) (ι := ι)).ker.FiniteIndex :=
  AddSubgroup.finiteIndex_ker _

theorem integerProductResidueHom_ker_index [Fintype ι] :
    (integerProductResidueHom (p := p) (ι := ι)).ker.index = p ^ Fintype.card ι := by
  classical
  change Nat.card ((ι → ℤ_[p]) ⧸ (integerProductResidueHom (p := p)).ker) = _
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    integerProductResidueHom_surjective).toEquiv]
  simp only [pow_one]
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, ZMod.card]

theorem isCompact_integerProductResidueHom_ker :
    IsCompact ((integerProductResidueHom (p := p) (ι := ι)).ker : Set (ι → ℤ_[p])) := by
  have heq : ((integerProductResidueHom (p := p) (ι := ι)).ker : Set (ι → ℤ_[p])) =
      Set.range (fun y : ι → ℤ_[p] => fun i => (p : ℤ_[p]) * y i) := by
    ext x
    change x ∈ (integerProductResidueHom (p := p)).ker ↔ _
    rw [mem_integerProductResidueHom_ker_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, funext (fun i => (hy i).symm)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, fun _ => rfl⟩
  rw [heq]
  exact isCompact_range (continuous_pi (fun i => continuous_const.mul (continuous_apply i)))

theorem image_integerProductResidueHom_ker :
    integerProductEmbedding (p := p) ''
      ((integerProductResidueHom (p := p) (ι := ι)).ker : Set (ι → ℤ_[p])) =
        (p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p) := by
  change integerProductEmbedding (p := p) ''
      ((integerProductResidueHom (p := p) (ι := ι)).ker : Set (ι → ℤ_[p])) =
    (fun x : ι → ℚ_[p] => (p : ℚ_[p]) • x) '' padicIntegerCoordinateLattice (p := p)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (mem_integerProductResidueHom_ker_iff x).mp hx
    refine ⟨integerProductEmbedding y, ⟨y, rfl⟩, ?_⟩
    ext i
    change (p : ℚ_[p]) * (y i : ℚ_[p]) = (x i : ℚ_[p])
    rw [hy i]
    simp
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨fun i => (p : ℤ_[p]) * y i, ?_, ?_⟩
    · exact (mem_integerProductResidueHom_ker_iff _).mpr ⟨y, fun _ => rfl⟩
    · ext i
      change ((p : ℤ_[p]) * y i : ℚ_[p]) = (p : ℚ_[p]) * (y i : ℚ_[p])
      simp

end

end LeanFormal.IUT.PadicIntegerProductLattice
