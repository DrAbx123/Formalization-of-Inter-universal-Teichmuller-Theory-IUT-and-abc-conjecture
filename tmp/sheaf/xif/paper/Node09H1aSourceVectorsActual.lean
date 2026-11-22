import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralTensorLattice
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aSourceVectorsActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [MeasurableSpace ((j : J) → E j)]
local instance piAlgebra : Algebra ℚ_[p] ((j : J) → E j) := Pi.algebra _ _
/-- The finite source vector attached to a tensor log-shell basis vector. -/
noncomputable def sourceVector
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A)) (k : FinitePadicTensorIndex (p := p) A) :
    (j : J) → E j := e (basis k)
/-- Each source vector lies in the actual finite source image. -/
theorem sourceVector_mem_finiteSourceImage
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hbasis : ∀ k, basis k ∈ tensorLogShellRegion (p := p) A)
    (k : FinitePadicTensorIndex (p := p) A) :
    sourceVector A e basis k ∈ finiteSourceImage A e := by
  exact ⟨basis k, hbasis k, rfl⟩
/-- Existence of finite source vectors from the tensor log-shell basis. -/
theorem exists_sourceVectors_mem_finiteSourceImage
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    ∃ basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
        (FinitePadicTensor (p := p) A),
      ∀ k, sourceVector A e basis k ∈ finiteSourceImage A e := by
  obtain ⟨basis, hbasis⟩ := exists_basis_mem_tensorLogShellRegion (p := p) A
  exact ⟨basis, fun k => sourceVector_mem_finiteSourceImage A e basis hbasis k⟩
/-- The coordinatewise minimum of the finite source vectors. -/
noncomputable def minVector
    [∀ j, LinearOrder (E j)] [Nonempty (FinitePadicTensorIndex (p := p) A)]
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A)) : (j : J) → E j :=
  fun j => Finset.univ.inf' Finset.univ_nonempty (fun k => sourceVector A e basis k j)
/-- The min vector is coordinatewise at most every source vector. -/
theorem minVector_le_sourceVector
    [∀ j, LinearOrder (E j)] [Nonempty (FinitePadicTensorIndex (p := p) A)]
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A)) (j : J)
    (k : FinitePadicTensorIndex (p := p) A) :
    minVector A e basis j ≤ sourceVector A e basis k j :=
  Finset.inf'_le (fun k => sourceVector A e basis k j) (Finset.mem_univ k)
#check sourceVector
#check exists_sourceVectors_mem_finiteSourceImage
end LeanFormal.IUT.XiFPaper.Node09H1aSourceVectorsActual
end