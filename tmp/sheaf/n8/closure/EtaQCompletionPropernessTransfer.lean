import tmp.sheaf.n8.closure.EtaQOUnitBallMassOneActual
import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib

/-!
# Eta q completion properness transfer

Actual topological homeomorphism

  commonPrimeCompletionActualHomeomorph : CommonPrimeCompletion place ≃ₜ Completion place.val

transfers LocallyCompactSpace from the production spectral-norm proper
completion to QCompletion X.  A NontriviallyNormedField instance for
QCompletion X is constructed from the actual inverse native q element:
qPilotSignedLog < 0 gives ‖q‖ < 1, hence ‖q⁻¹‖ > 1.  ProperSpace then follows
from the locally compact normed field (ProperSpace.of_locallyCompactSpace), and
Measure.addHaar is formed directly.  No change/inferInstanceAs and no arbitrary
instance is used.
-/

noncomputable section

set_option maxHeartbeats 800000

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

namespace LeanFormal.IUT.N8Closure.EtaQCompletionPropernessTransfer

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The production prime-indexed F-place. -/
noncomputable abbrev qOCommonPlace : FinitePlaceAtPrime (X.S.arithmetic.F)
    (FPlacePrime X) :=
  nativeFPlaceAtPrime X

/-- Actual topological homeomorphism from the production normalized completion
to QCompletion X. -/
noncomputable def qOCompletionHomeomorph :
    CommonPrimeCompletion (qOCommonPlace X) ≃ₜ QCompletion X :=
  commonPrimeCompletionActualHomeomorph (qOCommonPlace X)

/-- Actual LocallyCompactSpace on QCompletion X, transferred along the
homeomorphism from the proper CommonPrimeCompletion. -/
noncomputable instance qCompletionLocallyCompactSpace : LocallyCompactSpace (QCompletion X) := by
  haveI : LocallyCompactSpace (CommonPrimeCompletion (qOCommonPlace X)) :=
    locallyCompact_of_proper
  exact (qOCompletionHomeomorph X).locallyCompactSpace_iff.mp inferInstance

/-- Actual nontrivial normed field structure: the inverse of the native q is an
element of norm > 1, since the native q has norm < 1. -/
noncomputable instance qCompletionNontriviallyNormedField :
    NontriviallyNormedField (QCompletion X) where
  non_trivial := by
    refine ⟨((C9QPilotRegion.nativeQ X).q)⁻¹, ?_⟩
    rw [norm_inv]
    exact (one_lt_inv₀
      (ArithmeticQPilotLogVolume.qNorm_pos (C9QPilotRegion.nativeQ X))).2
      (ArithmeticQPilotLogVolume.qNorm_lt_one (C9QPilotRegion.nativeQ X))

/-- Actual ProperSpace on QCompletion X, from the locally compact normed field. -/
noncomputable instance qCompletionProperSpace : ProperSpace (QCompletion X) :=
  ProperSpace.of_locallyCompactSpace (QCompletion X)

/-- Actual additive Haar measure on QCompletion X. -/
noncomputable def qOAddHaarActual : Measure (QCompletion X) :=
  Measure.addHaar

noncomputable instance qOAddHaarActual_isHaar : Measure.IsAddHaarMeasure (qOAddHaarActual X) :=
  Measure.isAddHaarMeasure_addHaarMeasure
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts (QCompletion X)))

/-- Actual integral-unit-ball mass. -/
noncomputable def qOAddHaarActualIntegersMass : ENNReal :=
  qOAddHaarActual X (Integers (QCompletion X) : Set (QCompletion X))

theorem qOAddHaarActualIntegersMass_ne_zero : qOAddHaarActualIntegersMass X ≠ 0 :=
  (measure_localIntegers_pos_lt_top (K := QCompletion X) (qOAddHaarActual X)).1.ne'

theorem qOAddHaarActualIntegersMass_ne_top : qOAddHaarActualIntegersMass X ≠ ⊤ :=
  (measure_localIntegers_pos_lt_top (K := QCompletion X) (qOAddHaarActual X)).2.ne

/-- Actual normalized Haar measure with unit-ball mass 1. -/
noncomputable def qOAddHaarNormalized : Measure (QCompletion X) :=
  (qOAddHaarActualIntegersMass X)⁻¹ • qOAddHaarActual X

theorem qOAddHaarNormalized_integers :
    qOAddHaarNormalized X (Integers (QCompletion X) : Set (QCompletion X)) = 1 := by
  rw [qOAddHaarNormalized, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (qOAddHaarActualIntegersMass_ne_zero X)
    (qOAddHaarActualIntegersMass_ne_top X)

end LeanFormal.IUT.N8Closure.EtaQCompletionPropernessTransfer
