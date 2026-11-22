/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3AgreeFLTActual
import tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange
import tmp.sheaf.xif.paper.Mzk1P3BadCharPipelineActual
import Mathlib.Tactic

/-! # P3 GAP-PC-FINITE via FLT: Module.Finite of completed valuation rings

FLT `DedekindDomain/Completion/BaseChange.lean` contains the instance
`Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)`
(priority 1001, requiring `[Module.Finite A B]` and `[FiniteDimensional K L]`).
This discharges the content gap GAP-PC-FINITE for the places of number fields,
conditional only on the arithmetic instances of the extension K/k.
-/

noncomputable section
open scoped WithZero Valued TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 200000

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FiniteFLTActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeFLTActual

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable [FiniteDimensional k K] [Algebra.IsSeparable k K]
variable [Algebra (NumberField.RingOfIntegers k) K]
variable [IsScalarTower (NumberField.RingOfIntegers k) k K]
variable [IsScalarTower (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) K]
variable [IsScalarTower ℤ (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [Module.Finite (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [Module.IsTorsionFree (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K)]
variable [IsIntegralClosure (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers k) K]

/-- FLT finiteness instance transported to the actual places. -/
theorem moduleFinite_completedValuationRings
    (place : NumberField.FinitePlace K) :
    Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) := by
  let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    (comap (k := k) place).maximalIdeal
  let w : v.Extension (NumberField.RingOfIntegers K) := placeExtension (k := k) place
  haveI : Module.Finite (v.adicCompletionIntegers k) (w.1.adicCompletionIntegers K) :=
    inferInstance
  exact this

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem nativeBadToKPlace_moduleFinite
    [FiniteDimensional T.arithmetic.Fmod T.arithmetic.K]
    [Algebra.IsSeparable T.arithmetic.Fmod T.arithmetic.K]
    [Algebra (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.K]
    [IsScalarTower (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.Fmod T.arithmetic.K]
    [IsScalarTower (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K) T.arithmetic.K]
    [IsScalarTower ℤ (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [Module.Finite (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [Module.IsTorsionFree (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.K)]
    [IsIntegralClosure (NumberField.RingOfIntegers T.arithmetic.K)
      (NumberField.RingOfIntegers T.arithmetic.Fmod) T.arithmetic.K]
    (b : Bad (nativePlaceSelection T)) :
    Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K) :=
  moduleFinite_completedValuationRings (k := T.arithmetic.Fmod) (K := T.arithmetic.K)
    (nativeBadToKPlace T b)

def finiteFLTRows : List (String × String × String) :=
  [ ("moduleFinite_completedValuationRings", "FLT BaseChange finiteness instance", "PROVED (conditional on arithmetic instances)"),
    ("nativeBadToKPlace_moduleFinite", "GAP-PC-FINITE for the actual bad places", "PROVED (conditional)"),
    ("content inputs", "FiniteDimensional/IsSeparable/Module.Finite/IsTorsionFree/IsIntegralClosure/Towers", "arithmetic instances of T") ]

theorem finiteFLTRows_length : finiteFLTRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3FiniteFLTActual

end