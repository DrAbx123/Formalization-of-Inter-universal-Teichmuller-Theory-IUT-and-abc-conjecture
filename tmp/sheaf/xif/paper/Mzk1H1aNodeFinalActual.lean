import tmp.sheaf.xif.paper.H1aNodeAssemblyDoneActual
import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1H1aNodeFinalActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.H1aNodeAssemblyDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
open scoped Pointwise BigOperators
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
/-- A principal fractional lattice over a DVR is a uniformizer zpow. -/
theorem span_singleton_eq_span_uniformizer_zpow
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {π : R} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ n : Int, Submodule.span R {x} =
      Submodule.span R {((algebraMap R K π) ^ n)} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  refine ⟨n, ?_⟩
  rw [hu]
  exact (Submodule.span_singleton_eq_span_singleton (R := R) (M := K)).mpr ⟨u, rfl⟩ |>.symm
/-- H1a: every coordinate ideal of gammaP5 is a uniformizer power. -/
theorem coordSubmodule_eq_span_uniformizer_zpow
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hne : coordSubmodule (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j ≠ ⊥) :
    ∃ n : Int, coordSubmodule (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j =
      Submodule.span (Integers (E j))
        {(((dvrUniformizer (R := Integers (E j))) : Integers (E j)) : E j) ^ n} := by
  obtain ⟨x, hspan⟩ := exists_coordSubmodule_span (p := p) (A := A) (E := E) (e := e) hne
  have hx0 : x ≠ 0 := by
    intro hx
    apply hne
    rw [hspan, hx, Submodule.span_singleton_eq_bot]
  have hpi : Irreducible (dvrUniformizer (R := Integers (E j))) := dvrUniformizer_irreducible
  obtain ⟨n, hn⟩ := span_singleton_eq_span_uniformizer_zpow
    (R := Integers (E j)) (K := E j) hpi hx0
  refine ⟨n, ?_⟩
  rw [hspan, hn]
/-- H1a product formula. -/
theorem gammaP5_eq_pi_coordSubmodule
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    gammaP5 (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (finiteSourceImage A e) =
    Set.pi Set.univ (fun j => (coordSubmodule
      (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y)
      (Submodule.span (integralRing (fun j => fun x y => IsUltrametricDist.norm_add_le_max x y))
        (finiteSourceImage A e)) j : Set (E j))) :=
  gammaP5_eq_pi_coordSubmodule (p := p) (A := A) (E := E) e
#print axioms span_singleton_eq_span_uniformizer_zpow
#print axioms coordSubmodule_eq_span_uniformizer_zpow
#print axioms gammaP5_eq_pi_coordSubmodule
end LeanFormal.IUT.XiFPaper.Mzk1H1aNodeFinalActual
end