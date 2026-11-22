import tmp.sheaf.xif.paper.H1aCompactGammaFinalActual
import tmp.sheaf.xif.paper.Node09H1aCompactMaxPrincipalActual
import tmp.sheaf.xif.paper.Node09H1aProductFormulaActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.H1aNodeAssemblyFinalActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.H1aCompactGammaFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.XiFPaper.Node09H1aCompactMaxPrincipalActual
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
open scoped BigOperators
variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] [DecidableEq J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, IsUltrametricDist (E j)] [∀ j, ProperSpace (E j)]
variable [MeasurableSpace ((j : J) → E j)]
local instance piAlgebra : Algebra ℚ_[p] ((j : J) → E j) := Pi.algebra _ _
/-- Each coordinate projection of gammaP5 is principal. -/
theorem exists_coordSubmodule_span
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hne : coordSubmodule (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j ≠ ⊥) :
    ∃ x : E j, coordSubmodule (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j =
      Submodule.span (Integers (E j)) {x} := by
  let hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ) :=
    fun j => fun x y => IsUltrametricDist.norm_add_le_max x y
  have hM : IsCompact (Submodule.span (integralRing hna)
      (finiteSourceImage A e) : Set ((j : J) → E j)) := by
    change IsCompact (gammaP5 hna (finiteSourceImage A e))
    exact isCompact_gammaP5_finiteSourceImage (p := p) A e
  have hcomp : IsCompact (coordSubmodule hna (Submodule.span (integralRing hna)
      (finiteSourceImage A e)) j : Set (E j)) :=
    isCompact_coordSubmodule hna _ hM j
  exact submodule_eq_span_of_compact_max_norm _ hcomp hne
/-- Product formula for gammaP5. -/
theorem gammaP5_eq_pi_coordSubmodule
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    gammaP5 (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (finiteSourceImage A e) =
    Set.pi Set.univ (fun j => (coordSubmodule
      (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j : Set (E j))) := by
  exact submodule_eq_pi_coord _ _
#check exists_coordSubmodule_span
#check gammaP5_eq_pi_coordSubmodule
end LeanFormal.IUT.XiFPaper.H1aNodeAssemblyFinalActual
end