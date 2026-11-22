import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]

/-- Finite dependent choice of places over a finite family of rational
places.  Each chosen place is produced by the actual lying-over theorem via
`NumberFieldFinitePlace.comap_surjective`. -/
theorem S2738_exists_place_family_over
    {ι : Type*} (p : ι → NumberField.FinitePlace ℚ) :
    ∃ P : ι → NumberField.FinitePlace K,
      ∀ i, comap (k := ℚ) (P i) = p i := by
  classical
  choose P hP using fun i =>
    NumberFieldFinitePlace.comap_surjective (k := ℚ) (K := K) (p i)
  exact ⟨P, hP⟩

/-- Finset-indexed version: only the places in a given finite set are
required to lie over the prescribed rational places. -/
theorem S2738_exists_place_family_over_finset
    {ι : Type*} (s : Finset ι) (p : ι → NumberField.FinitePlace ℚ) :
    ∃ P : ι → NumberField.FinitePlace K,
      ∀ i ∈ s, comap (k := ℚ) (P i) = p i :=
  let ⟨P, hP⟩ := S2738_exists_place_family_over (K := K) p
  ⟨P, fun i _ => hP i⟩

/-- Product of the corresponding prime ideals: finite dependent product of
the maximal ideals of the chosen places. -/
noncomputable def S2738PrimeProduct
    {ι : Type*} [Fintype ι] (P : ι → NumberField.FinitePlace K) :
    Ideal (NumberField.RingOfIntegers K) :=
  ∏ i, (P i).maximalIdeal.asIdeal

/-- `Ideal.absNorm` is multiplicative over the finite dependent product. -/
theorem S2738_absNorm_primeProduct
    {ι : Type*} [Fintype ι] (P : ι → NumberField.FinitePlace K) :
    Ideal.absNorm (S2738PrimeProduct P) =
      ∏ i, Ideal.absNorm ((P i).maximalIdeal.asIdeal) :=
  map_prod Ideal.absNorm (fun i => (P i).maximalIdeal.asIdeal) Finset.univ

#check S2738_exists_place_family_over
#check S2738_absNorm_primeProduct
#print axioms S2738_absNorm_primeProduct

end LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual
end
