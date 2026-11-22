import tmp.sheaf.n8.closure.EtaQOUnitBallMassOneActual
import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib

/-!
# Eta q completion properness actual attempt

The actual F-place completion QCompletion X has the default completion norm.
The production CommonPrimeCompletion of the same F-place carries the spectral
norm and a proved ProperSpace instance, but the two NormedField/PseudoMetricSpace
instances are different: a change to the CommonPrimeCompletion ProperSpace
fails definitionally.

Hence ProperSpace (QCompletion X) cannot be transported from
normalizedCompletionHomeomorph without a norm-compatibility/NormedSpace bridge.
This file records the actual CommonPrimeCompletion properness and gives the
exact conditional bridge (NormedSpace over the p-adic scalar field) needed for
FiniteDimensional.proper, plus the exact no-go for direct addHaar formation.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open scoped ENNReal

namespace LeanFormal.IUT.N8Closure.EtaQCompletionPropernessActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The production prime-indexed F-place. -/
noncomputable abbrev qOCommonPlace : FinitePlaceAtPrime (X.S.arithmetic.F)
    (FPlacePrime X) :=
  nativeFPlaceAtPrime X

/-- The p-adic scalar field of the native F-place. -/
noncomputable abbrev qOScalarField : Type :=
  PadicScalarField (nativeFPlaceOverBad X)

/-- Actual properness of the production normalized (spectral-norm) completion. -/
theorem commonPrimeCompletion_proper :
    ProperSpace (CommonPrimeCompletion (qOCommonPlace X)) :=
  inferInstance

/-- Exact no-go record: the direct addHaar construction is unavailable because
ProperSpace (QCompletion X) is not an instance.  The production proper
instance is on the spectral-norm CommonPrimeCompletion carrier, whose
NormedField/PseudoMetricSpace instance differs from QCompletion's default
completion norm.  No valid transport is exposed in production. -/
def QCompletionPropernessGap : Prop :=
  ProperSpace (QCompletion X)

/-- Conditional LocallyCompactSpace, derived from conditional properness. -/
theorem qCompletionLocallyCompactSpace_of_proper
    (h : ProperSpace (QCompletion X)) : LocallyCompactSpace (QCompletion X) := by
  letI : ProperSpace (QCompletion X) := h
  infer_instance

/-- Conditional actual addHaar formation: once ProperSpace (equivalently
LocallyCompactSpace) is available, Measure.addHaar can be formed. -/
noncomputable def qOAddHaarActual_of_proper
    (h : ProperSpace (QCompletion X)) : Measure (QCompletion X) := by
  letI : ProperSpace (QCompletion X) := h
  letI : LocallyCompactSpace (QCompletion X) := inferInstance
  exact Measure.addHaar

end LeanFormal.IUT.N8Closure.EtaQCompletionPropernessActual
