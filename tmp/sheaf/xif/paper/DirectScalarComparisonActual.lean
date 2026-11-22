import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperThetaPilotHullLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Direct scalar comparison: native q-pilot vs paper Theta hull

This file works only at the scalar level.  No object equality and no carrier
identification is used.

Actual scalars:

* paper q-pilot signed log-volume:
    paperQPilotSignedLog T
      = -nativeGlobalQPilotNormalizedLogMagnitude T;
* actual paper Theta-pilot hull log-volume:
    paperThetaHullLog T
      = sum_b paperBadThetaPilotHullLogVolume T b.

The direct comparison is

  paperQPilotSignedLog T <= paperThetaHullLog T.

By the actual ray definition hullLogVolumeRay = Set.Iic, this is equivalent to

  paperQPilotSignedLog T in hullLogVolumeRay (paperThetaHullLog T).

It is also equivalent to the positive magnitude form

  nativeGlobalThetaPilotHullLogMagnitude T
    <= nativeGlobalQPilotNormalizedLogMagnitude T,

which is the Corollary 3.12 direction.  The comparison itself is not proved;
the exact remaining paper Theta-hull normalization gap is recorded.  No fake
inequality/sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.DirectScalarComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual paper q-pilot signed log-volume, as the negative native normalized
q-pilot magnitude. -/
noncomputable def paperQPilotSignedLog : Real :=
  -nativeGlobalQPilotNormalizedLogMagnitude T

/-- Actual paper Theta-pilot hull log-volume: the sum of the actual paper hull
log-volumes over the native bad family. -/
noncomputable def paperThetaHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    paperBadThetaPilotHullLogVolume (l := l) T b

/-- Actual paper q-pilot magnitude |log q|. -/
noncomputable def paperQPilotMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- Actual paper Theta-pilot hull magnitude |log Theta|. -/
noncomputable def paperThetaHullMagnitude : Real :=
  -paperThetaHullLog T

/-- The q-pilot signed scalar is the negative magnitude. -/
theorem paperQPilotSignedLog_eq_neg_magnitude :
    paperQPilotSignedLog T = -paperQPilotMagnitude T := rfl

/-- The Theta-hull signed scalar is the negative magnitude. -/
theorem paperThetaHullLog_eq_neg_magnitude :
    paperThetaHullLog T = -paperThetaHullMagnitude T := by
  unfold paperThetaHullLog paperThetaHullMagnitude
  rw [Finset.sum_neg_distrib]
  ring

/-- Direct scalar comparison: paper q-pilot signed log <= paper Theta hull log. -/
def DirectScalarComparison : Prop :=
  paperQPilotSignedLog T ≤ paperThetaHullLog T

/-- The direct scalar comparison is exactly membership in the paper ray. -/
theorem directScalarComparison_iff_mem_ray :
    DirectScalarComparison T ↔
      paperQPilotSignedLog T ∈ hullLogVolumeRay (paperThetaHullLog T) := by
  unfold DirectScalarComparison
  rw [mem_hullLogVolumeRay_iff]

/-- The direct scalar comparison is equivalent to the Cor 3.12 magnitude
direction thetaHullMagnitude <= qPilotMagnitude. -/
theorem directScalarComparison_iff_magnitude :
    DirectScalarComparison T ↔
      paperThetaHullMagnitude T ≤ paperQPilotMagnitude T := by
  unfold DirectScalarComparison paperQPilotSignedLog paperQPilotMagnitude
    paperThetaHullLog paperThetaHullMagnitude
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Exact remaining gap: the paper Theta-pilot hull has the actual Haar volume
candidate, but the mono-analytic unit-region normalization is not supplied.
This is the only input gap recorded for the direct scalar comparison. -/
def DirectScalarComparisonNormalizationGap : Prop :=
  PaperThetaPilotHullNormalizationRequired (l := l) T

/-- Conditional direct scalar comparison from the exact comparison hypothesis.
This is a theorem surface, not an asserted inequality. -/
theorem directScalarComparison_of_hypothesis
    (h : paperQPilotSignedLog T ≤ paperThetaHullLog T) :
    DirectScalarComparison T :=
  h

end LeanFormal.IUT.XiFPaper.DirectScalarComparisonActual

end
