import tmp.sheaf.n8.closure.C1P6UnitResidueImageDecidable
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

/-!
# C1ResidueFieldFiniteActual

Actual finiteness of the completion residue fields used in the unit residue
comparison, via the production residue equivalences with the number-ring
residue fields (`residueEquivAdicCompletionIntegers` and its `comap` variant)
and the production `residueFieldFinite` instances.

This instantiates the conditional decidability of
`C1P6UnitResidueComparison` without any arbitrary `Fintype`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ResidueFieldFiniteActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison
open LeanFormal.IUT.N8Closure.C1P6UnitResidueImageDecidable
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual finiteness of the top completion residue field. -/
noncomputable instance topResidueFieldFinite : Finite (TopResidueField X) := by
  haveI h : Finite (NumberFieldFinitePlace.ResidueField (topPlace X)) :=
    NumberFieldFinitePlace.residueFieldFinite (topPlace X)
  exact Finite.of_equiv _
    (NumberFieldFinitePlace.residueEquivAdicCompletionIntegers
      (K := X.S.arithmetic.F) (place := topPlace X)).toEquiv

/-- Actual finiteness of the base completion residue field. -/
noncomputable instance baseResidueFieldFinite : Finite (BaseResidueField X) := by
  haveI h : Finite (NumberFieldFinitePlace.ResidueField (basePlace X)) :=
    NumberFieldFinitePlace.residueFieldFinite (basePlace X)
  exact Finite.of_equiv _
    (NumberFieldFinitePlace.residueEquivAdicCompletionIntegers_comap
      (k := X.S.arithmetic.Fmod) (place := topPlace X)).toEquiv

/-- Actual decidable instance for the unit residue comparison. -/
noncomputable def unitResidueComparisonDecidable :
    Decidable (C1P6UnitResidueComparison X) :=
  c1P6UnitResidueComparison_decidable_of_finite X

end LeanFormal.IUT.N8Closure.C1ResidueFieldFiniteActual