import tmp.sheaf.xif.paper.Node09H1aSourceVectorsActual
import tmp.sheaf.xif.paper.Node09H1aValuationActual
import tmp.sheaf.xif.paper.Mzk1P5GammaSubsetHullActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1bVolumeActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Node09H1aSourceVectorsActual
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [∀ j, CharZero (E j)] [∀ j, CompleteSpace (E j)] [∀ j, ProperSpace (E j)]
/-- Actual residue degree `f_j`, extracted from the residue-cardinality donor. -/
noncomputable def residueDegree (E : J → Type) [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, CharZero (E j)]
    [∀ j, CompleteSpace (E j)] [∀ j, IsUltrametricDist (E j)] [∀ j, ProperSpace (E j)]
    (j : J) : Nat :=
  Classical.choose (LeanFormal.IUT.LocalFieldLogarithm.logShellResidueCard_eq_prime_pow
    (K := E j) (p := p))
theorem residueDegree_pos (E : J → Type) [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, CharZero (E j)]
    [∀ j, CompleteSpace (E j)] [∀ j, IsUltrametricDist (E j)] [∀ j, ProperSpace (E j)]
    (j : J) : 1 ≤ residueDegree (p := p) E j :=
  (Classical.choose_spec (LeanFormal.IUT.LocalFieldLogarithm.logShellResidueCard_eq_prime_pow
    (K := E j) (p := p))).1
/-- Source-vector valuation at tensor factor `j`, normalized by `log p`. -/
noncomputable def sourceFactorValuation
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (k : FinitePadicTensorIndex (p := p) A) (j : J) : ℝ :=
  -Real.log ‖sourceVector A e basis k j‖ / Real.log p
/-- H1a minimum valuation over the finite actual source columns. -/
noncomputable def rP5
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) : ℝ :=
  (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).inf' hne
    (fun k => sourceFactorValuation A e basis k j)
theorem rP5_eq_sourceFactorValuation
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) :
    ∃ k, rP5 A e basis hne j = sourceFactorValuation A e basis k j := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' hne
    (fun k => sourceFactorValuation A e basis k j)
  exact ⟨k, by simpa [rP5] using hk⟩
/-- Combined H1b signed volume density `f_j * r_j * log p`. -/
noncomputable def vP5
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) : ℝ :=
  (residueDegree (p := p) E j : ℝ) * rP5 A e basis hne j * Real.log p
#check residueDegree
#check rP5
#check vP5
end LeanFormal.IUT.XiFPaper.Node09H1bVolumeActual
end