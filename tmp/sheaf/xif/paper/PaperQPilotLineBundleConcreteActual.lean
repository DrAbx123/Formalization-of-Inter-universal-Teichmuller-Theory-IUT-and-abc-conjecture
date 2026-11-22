import tmp.sheaf.xif.paper.SHELandingActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! # Paper q-pilot line bundle over concreteInput/FinitePrimePlace 2 7

This file constructs, at the concrete finite prime places 2,...,7 used by
SourceProcessionBoundary.Input.concreteInput l:

* the actual one-column structure with local rings CompletionIntegers at the
  rational finite place associated to each concrete prime;
* the actual integral arithmetic vector bundle with total space Z and the
  completed localizations;
* the actual q-pilot ideal over a supplied finite bad subset S of the concrete
  primes, as the product of the corresponding prime ideals of Z;
* the actual fractional-ideal line bundle O(-S) = (product ideal)^-1;
* the boundary/oneColumn/lineBundle/fractionalIdeal target data over the actual
  concrete input.

No native-place mismatch is used.  No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.PaperQPilotLineBundleConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.SourceProcessionBoundary

universe u

/-- The concrete finite places 2,...,7. -/
abbrev ConcretePlaces : Type := FinitePrimePlace 2 7

/-- The actual rational finite place associated to a concrete prime. -/
noncomputable def concretePlace (v : ConcretePlaces) : NumberField.FinitePlace ℚ := by
  letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
  exact rationalFinitePlace v.1

/-- The actual one-column structure over the concrete primes: completed
valuation rings as local rings and completed fields as local fields. -/
noncomputable def concreteOneColumn :
    SourceOneColumnArithmeticHolomorphicStructure ConcretePlaces :=
  { localRing := fun v => CompletionIntegers (concretePlace v)
    ringOf := fun _ => inferInstance
    localField := fun v => Completion (concretePlace v)
    fieldOf := fun _ => inferInstance
    localizationInclusion := fun v =>
      ValuationSubring.subtype (CompletionIntegers (concretePlace v)) }

/-- The actual completed localization of a Z-section at a concrete prime. -/
noncomputable def concreteLocalization (v : ConcretePlaces)
    (x : NumberField.RingOfIntegers ℚ) :
    (concreteOneColumn).localRing v :=
  algebraMap (NumberField.RingOfIntegers ℚ)
    (CompletionIntegers (concretePlace v)) x

/-- The actual integral arithmetic vector bundle over the concrete one-column
structure: total space Z, completed localizations. -/
noncomputable def concreteIntegralBundle :
    SourceArithmeticVectorBundle concreteOneColumn where
  total := NumberField.RingOfIntegers ℚ
  localization v x := concreteLocalization v x

/-- The actual q-pilot ideal over a supplied finite bad subset S of the concrete
primes: the product of the corresponding Z-prime ideals. -/
noncomputable def concretePrimeIdeal (v : ConcretePlaces) : Ideal ℤ :=
  Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers ℚ))
    (concretePlace v).maximalIdeal.asIdeal

noncomputable def concreteQPilotIdeal (S : Finset ConcretePlaces) : Ideal ℤ :=
  ∏ v ∈ S, concretePrimeIdeal v

/-- The actual q-pilot fractional-ideal line bundle O(-S). -/
noncomputable def concreteQPilotLineBundle
    (S : Finset ConcretePlaces) :
    FractionalIdeal (nonZeroDivisors ℤ) ℚ :=
  (concreteQPilotIdeal S : FractionalIdeal (nonZeroDivisors ℤ) ℚ)⁻¹

/-- The line bundle is the inverse of the actual q-pilot ideal. -/
theorem concreteQPilotLineBundle_eq_inv_ideal
    (S : Finset ConcretePlaces) :
    concreteQPilotLineBundle S =
      (concreteQPilotIdeal S : FractionalIdeal (nonZeroDivisors ℤ) ℚ)⁻¹ := rfl

/-- The concrete q-pilot line-bundle target data over the actual concreteInput. -/
structure ConcreteQPilotLineBundleTarget (l : PrimeGeFive) where
  /-- The actual concrete source boundary (V = FinitePrimePlace 2 7). -/
  boundary : SourceProcessionBoundary.Input
    (l := l) (V := ConcretePlaces)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
  /-- Actual one-column structure. -/
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure ConcretePlaces
  /-- Actual integral arithmetic vector bundle. -/
  lineBundle : SourceArithmeticVectorBundle oneColumn
  /-- Supplied finite bad subset of the concrete primes. -/
  badSubset : Finset ConcretePlaces
  /-- Actual q-pilot ideal. -/
  ideal : Ideal ℤ
  ideal_eq : ideal = concreteQPilotIdeal badSubset
  /-- Actual fractional-ideal line bundle O(-S). -/
  fractionalLineBundle : FractionalIdeal (nonZeroDivisors ℤ) ℚ
  fractionalLineBundle_eq : fractionalLineBundle =
    (ideal : FractionalIdeal (nonZeroDivisors ℤ) ℚ)⁻¹

/-- The concrete q-pilot line-bundle target built from concreteInput and the
actual completed-ring line bundle. -/
noncomputable def concreteQPilotLineBundleTarget
    (l : PrimeGeFive) (S : Finset ConcretePlaces) :
    ConcreteQPilotLineBundleTarget l where
  boundary := SourceProcessionBoundary.Input.concreteInput l
  oneColumn := concreteOneColumn
  lineBundle := concreteIntegralBundle
  badSubset := S
  ideal := concreteQPilotIdeal S
  ideal_eq := rfl
  fractionalLineBundle := concreteQPilotLineBundle S
  fractionalLineBundle_eq := by
    change concreteQPilotLineBundle S =
      (concreteQPilotIdeal S : FractionalIdeal (nonZeroDivisors ℤ) ℚ)⁻¹
    exact concreteQPilotLineBundle_eq_inv_ideal S

/-- The target boundary is the actual concreteInput. -/
theorem concreteQPilotLineBundleTarget_boundary
    (l : PrimeGeFive) (S : Finset ConcretePlaces) :
    (concreteQPilotLineBundleTarget l S).boundary =
      SourceProcessionBoundary.Input.concreteInput l := rfl

/-- The target ideal is the actual product of concrete Z-prime ideals. -/
theorem concreteQPilotLineBundleTarget_ideal
    (l : PrimeGeFive) (S : Finset ConcretePlaces) :
    (concreteQPilotLineBundleTarget l S).ideal =
      ∏ v ∈ S, concretePrimeIdeal v := rfl

/-- The target fractional line bundle is exactly O(-S). -/
theorem concreteQPilotLineBundleTarget_fractional
    (l : PrimeGeFive) (S : Finset ConcretePlaces) :
    (concreteQPilotLineBundleTarget l S).fractionalLineBundle =
      (concreteQPilotIdeal S : FractionalIdeal (nonZeroDivisors ℤ) ℚ)⁻¹ :=
  concreteQPilotLineBundle_eq_inv_ideal S

end LeanFormal.IUT.Theorem311Source.PaperQPilotLineBundleConcreteActual

end
