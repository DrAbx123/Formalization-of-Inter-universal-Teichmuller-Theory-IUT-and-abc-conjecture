import tmp.sheaf.xif.paper.NativeCuspRealActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual

/-!
# CuspRealizationData from an actual cusp coordinate map

The native cusp is the geometric object

  nativeCuspGeometric T
    : Iut.OrbicurveBoundaryCusp
        (nativeCompletion T).sourceSignQuotientData.cK.

CuspRealizationData requires real epsilon/cuspScale data and a native
geometric-to-real realization. No function from OrbicurveBoundaryCusp to Real
and no cuspScale Real are present in the tree.

This file isolates the exact missing coordinate map as CuspCoordinateMap and
shows that such a map plus a base cusp constructs CuspRealizationData
conditionally. No real coordinate, scale, compatibility proposition, toy data,
forbidden placeholder, or unfilled proof is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CuspRealizationActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.XiFPaper.NativeD7CuspActual
open LeanFormal.IUT.XiFPaper.NativeCuspRealActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The native cusp boundary object. -/
abbrev nativeCuspObject :
    Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK :=
  nativeCuspGeometric T

/-- Exact missing coordinate map: real epsilon and cuspScale functions on the
geometric boundary cusp, with positivity, compatibility, and native realization
proofs. -/
structure CuspCoordinateMap
    (X : Iut.HyperbolicOrbicurve (nativeCompletion T).sourceSignQuotientData.cK) where
  epsilonOf : Iut.OrbicurveBoundaryCusp X -> Real
  epsilon_positive : forall cusp, 0 < epsilonOf cusp
  epsilon_nonzero : forall cusp, epsilonOf cusp != 0
  cuspScaleOf : Iut.OrbicurveBoundaryCusp X -> Real
  cuspScale_positive : forall cusp, 0 < cuspScaleOf cusp
  epsilon_scale_relation : forall cusp, epsilonOf cusp * cuspScaleOf cusp != 0
  epsilon_compatibility : Iut.OrbicurveBoundaryCusp X -> Prop
  epsilon_compatibility_proved : forall cusp, epsilon_compatibility cusp
  native_epsilon_realization : Iut.OrbicurveBoundaryCusp X -> Prop
  native_epsilon_realization_proved : forall cusp, native_epsilon_realization cusp

/-- Conditional construction of CuspRealizationData from an exact coordinate
map and a chosen native cusp. -/
def cuspRealizationDataOfCoordinateMap
    (M : CuspCoordinateMap (nativeCompletion T).sourceSignQuotientData.cK)
    (cusp : Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK) :
    CuspRealizationData (l := l) T where
  epsilon := M.epsilonOf cusp
  epsilon_positive := M.epsilon_positive cusp
  epsilon_nonzero := M.epsilon_nonzero cusp
  cuspScale := M.cuspScaleOf cusp
  cuspScale_positive := M.cuspScale_positive cusp
  epsilon_scale_relation := M.epsilon_scale_relation cusp
  epsilon_compatibility := M.epsilon_compatibility cusp
  epsilon_compatibility_proved := M.epsilon_compatibility_proved cusp
  native_epsilon_realization := M.native_epsilon_realization cusp
  native_epsilon_realization_proved := M.native_epsilon_realization_proved cusp

/-- Exact missing object: a real coordinate map on the geometric cusp. -/
def MissingCuspCoordinateMap : Prop :=
  Nonempty (CuspCoordinateMap
    (nativeCompletion T).sourceSignQuotientData.cK)

/-- The actual geometric cusp is available as the input to such a map. -/
theorem nativeCuspObject_type :
    Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK :=
  nativeCuspObject T

/-- Conditional native cusp hypotheses from the exact coordinate map and the
actual geometric cusp. -/
theorem nativeCuspHypotheses_of_coordinateMap
    (M : CuspCoordinateMap (nativeCompletion T).sourceSignQuotientData.cK) :
    Nonempty NativeCuspClauseHypotheses :=
  ⟨nativeCuspHypothesesOfRealization T
    (cuspRealizationDataOfCoordinateMap T M (nativeCuspObject T))⟩

end LeanFormal.IUT.XiFPaper.CuspRealizationActualAdapted

end
