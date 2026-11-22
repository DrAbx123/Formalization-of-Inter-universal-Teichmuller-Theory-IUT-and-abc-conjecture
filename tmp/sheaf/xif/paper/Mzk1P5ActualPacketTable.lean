import tmp.sheaf.xif.paper.Mzk1P5GammaSubsetHullActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
local instance piAlgebra : Algebra ℚ_[p] ((j : J) → E j) := Pi.algebra _ _
variable (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
/-- Actual four-column packet table on the product carrier: the Haar reference
lattice is the actual unit lattice `O_t = span_O 1`, and the finite source image
is the actual tensor log-shell product image. -/
structure ActualPacketTable (rootEquation : Prop) (valuation : J → Real) where
  sourceArrowRootEquation : Prop
  tensorFactorIndex : Type*
  tensorFactorProjection : tensorFactorIndex → J
  tensorFactorValuation : tensorFactorIndex → Real
  haarReferenceLattice :
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ)) →
      Submodule (integralRing hna) ((j : J) → E j)
/-- The unit lattice `O_t = span_O 1` is an actual full Haar reference lattice. -/
def unitReferenceLattice :
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ)) →
      Submodule (integralRing hna) ((j : J) → E j) := fun hna =>
  Submodule.span (integralRing hna) {(1 : (j : J) → E j)}
/-- Actual packet table; all lattice/source data are actual constructions. -/
def actualPacketTable [∀ j, Nonempty (E j)]
    (rootEquation : Prop) (valuation : J → Real) :
    ActualPacketTable (E := E) rootEquation valuation where
  sourceArrowRootEquation := rootEquation
  tensorFactorIndex := J
  tensorFactorProjection := fun j => j
  tensorFactorValuation := valuation
  haarReferenceLattice := unitReferenceLattice (E := E)
/-- The actual finite source image `G_t`: the tensor log-shell product image. -/
def finiteSourceImage (A : ι → Type) [∀ i, NormedField (A i)]
    [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
    [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
    [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set ((j : J) → E j) := by
  letI : Finite ι := Finite.of_fintype _
  letI : Finite J := Finite.of_fintype _
  exact tensorLogShellProductImage A e
/-- Actual P5 lower bound: `Γ_t ⊆ H_t` for the actual finite source image. -/
theorem gamma_subset_hull_actual
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ)) :
    gammaP5 hna (finiteSourceImage A e) ⊆ HP5 (finiteSourceImage A e) :=
  gammaP5_subset_HP5 hna (finiteSourceImage A e)

/-- The actual unit lattice `C_t` is contained in `Γ_t`: the tensor identity
belongs to the actual finite source image. -/
theorem unitReferenceLattice_le_gammaP5
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ)) :
    unitReferenceLattice (E := E) hna ≤
      gammaP5 hna (finiteSourceImage A e) := by
  apply Submodule.span_le.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact Submodule.subset_span
    (one_mem_tensorLogShellProductImage A e)
/-- Actual integral span/hull equality for the tensor log-shell product image. -/
theorem gammaP5_eq_HP5_actual [Finite ι] [Finite J]
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ)) :
    gammaP5 hna (finiteSourceImage A e) = HP5 (finiteSourceImage A e) := by
  unfold gammaP5 HP5 finiteSourceImage
  exact integralSpan_eq_hull hna
    (isCompact_tensorLogShellProductImage A e)
    ⟨1, one_mem_tensorLogShellProductImage A e⟩
    (fun j => ⟨1, one_mem_tensorLogShellProductImage A e, one_ne_zero⟩)
#check unitReferenceLattice_le_gammaP5
#check gammaP5_eq_HP5_actual
#check ActualPacketTable
#check actualPacketTable
#check finiteSourceImage
#check gamma_subset_hull_actual
end LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
end