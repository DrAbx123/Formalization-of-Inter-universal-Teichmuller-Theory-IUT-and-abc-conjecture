import tmp.sheaf.xif.paper.S2738PrimeOverFamilyActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual

universe u

/-- The finite subtype of the arithmetic prime support of a rational point. -/
abbrev SupportIndex (x : ℚ) : Type :=
  {p : Nat // p ∈ arithmeticPrimeSupport x}

instance supportIndexFintype (x : ℚ) : Fintype (SupportIndex x) :=
  Finset.Subtype.fintype (arithmeticPrimeSupport x)

/-- Chosen rational finite places at the support primes. -/
noncomputable def supportRationalPlace (x : ℚ) :
    SupportIndex x → NumberField.FinitePlace ℚ :=
  fun i =>
    letI : Fact (Nat.Prime i.1) :=
      ⟨prime_of_mem_arithmeticPrimeSupport i.2⟩
    rationalFinitePlace i.1

/-- Actual chosen number-field places over the support primes. -/
noncomputable def supportPlace {K : Type u} [Field K] [NumberField K]
    [Algebra ℚ K] (x : ℚ) : SupportIndex x → NumberField.FinitePlace K :=
  Classical.choose
    (S2738_exists_place_family_over (K := K) (fun i : SupportIndex x =>
      supportRationalPlace x i))

theorem supportPlace_comap {K : Type u} [Field K] [NumberField K]
    [Algebra ℚ K] (x : ℚ) (i : SupportIndex x) :
    NumberFieldFinitePlace.comap (k := ℚ) (supportPlace (K := K) x i) =
      supportRationalPlace x i :=
  Classical.choose_spec
    (S2738_exists_place_family_over (K := K) (fun i : SupportIndex x =>
      supportRationalPlace x i)) i

/-- The product of the chosen maximal ideals over the full ABC prime support. -/
noncomputable def supportIdeal {K : Type u} [Field K] [NumberField K]
    [Algebra ℚ K] (x : ℚ) :
    Ideal (NumberField.RingOfIntegers K) :=
  ∏ i : SupportIndex x, (supportPlace (K := K) x i).maximalIdeal.asIdeal

theorem supportIdeal_absNorm {K : Type u} [Field K] [NumberField K]
    [Algebra ℚ K] (x : ℚ) :
    Ideal.absNorm (supportIdeal (K := K) x) =
      ∏ i : SupportIndex x,
        Ideal.absNorm ((supportPlace (K := K) x i).maximalIdeal.asIdeal) :=
  map_prod Ideal.absNorm _ Finset.univ

/-- Every prime of the ABC support is realized by a chosen number-field place. -/
theorem support_covered {K : Type u} [Field K] [NumberField K]
    [Algebra ℚ K] (x : ℚ) :
    ∀ p : SupportIndex x,
      NumberFieldFinitePlace.comap (k := ℚ)
        (supportPlace (K := K) x p) =
      supportRationalPlace x p := by
  intro p
  exact supportPlace_comap (K := K) x p

#check SupportIndex
#check supportIndexFintype
#check supportRationalPlace
#check supportPlace
#check supportPlace_comap
#check supportIdeal
#check supportIdeal_absNorm
#check support_covered
#print axioms support_covered

end LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
end
