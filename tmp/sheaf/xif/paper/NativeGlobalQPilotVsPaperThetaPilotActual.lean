import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperThetaPilotHullLogVolumeActual

/-! # Native global q-pilot vs paper Theta-pilot hull

Combines the actual native global q-pilot normalized magnitude

  nativeGlobalQPilotNormalizedLogMagnitude T
    = sum_b nativeBadLocalWeight T b * baseQLogMagnitude T b

with the actual paper Theta-pilot hull log-volume of
PaperThetaPilotHullLogVolumeActual at the actual native base q values.

The paper Theta-pilot hull log-volume candidate is the sum over the native bad
family of the actual paper hull log-volume at paperBaseQReal T b, with the
paper sign:

  nativeGlobalThetaPilotHullLogMagnitude T
    = sum_b -paperBadThetaPilotHullLogVolume T b.

SIGN/DIRECTION ANALYSIS (IUT III Corollary 3.12).

The actual paper hull log-volume is

  paperBadThetaPilotHullLogVolume T b
    = Real.log (paperThetaPilotHullVolume T b).toReal
    = -|log Theta_b|,

so the paper sign magnitude |log Theta_b| is

  nativeBadThetaPilotHullLogMagnitude T b
    = -paperBadThetaPilotHullLogVolume T b.

Meanwhile the normalized q-pilot magnitude is positive and is |log q|.

Corollary 3.12 states

  -|log Theta| >= -|log q|,

which is equivalent (multiplying by -1 and reversing the inequality) to

  |log Theta| <= |log q|,

i.e. exactly

  nativeGlobalThetaPilotHullLogMagnitude T
    <= nativeGlobalQPilotMagnitude T.

The comparison below is therefore defined in this corrected direction:
theta-hull magnitude <= q-pilot magnitude.  It is NOT proved: the raw Haar hull
volume still lacks the mono-analytic/unit-region normalization and compactness
data of PaperThetaPilotHullLogVolumeActual.  The exact missing normalization
proposition is recorded and the comparison Prop is not asserted.
No reverse inequality and no fake inequality/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeGlobalQPilotVsPaperThetaPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual paper sign magnitude of the Theta-pilot hull at one native bad place:
the negative of the actual paper hull log-volume. -/
noncomputable def nativeBadThetaPilotHullLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  -paperBadThetaPilotHullLogVolume (l := l) T b

/-- Actual global paper Theta-pilot hull log-magnitude candidate: sum over the
native bad family of the actual paper hull magnitudes. -/
noncomputable def nativeGlobalThetaPilotHullLogMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadThetaPilotHullLogMagnitude T b

/-- Actual native q-pilot normalized magnitude, packaged. -/
noncomputable def nativeGlobalQPilotMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- Actual data/inputs of the paper source comparison: the native global q-pilot
normalized magnitude and the actual paper Theta-pilot hull log-magnitude. -/
structure NativePaperSourceComparisonData where
  qPilotMagnitude : Real
  qPilotMagnitude_eq : qPilotMagnitude = nativeGlobalQPilotMagnitude T
  thetaPilotHullLogMagnitude : Real
  thetaPilotHullLogMagnitude_eq :
    thetaPilotHullLogMagnitude = nativeGlobalThetaPilotHullLogMagnitude T

/-- The actual comparison inputs constructed from the two actual global
scalars. -/
noncomputable def nativePaperSourceComparisonData :
    NativePaperSourceComparisonData T where
  qPilotMagnitude := nativeGlobalQPilotMagnitude T
  qPilotMagnitude_eq := rfl
  thetaPilotHullLogMagnitude := nativeGlobalThetaPilotHullLogMagnitude T
  thetaPilotHullLogMagnitude_eq := rfl

/-- The paper source comparison defined directly on the two actual global
scalars.  This is a Prop definition only; no inequality is proved or assumed. -/
def NativePaperSourceComparison : Prop :=
  nativeGlobalThetaPilotHullLogMagnitude T ≤ nativeGlobalQPilotMagnitude T

/-- Exact missing Theta-hull normalization data: the raw Haar hull volume does
not yet carry the mono-analytic unit-region normalization and compactness. -/
def NativePaperSourceComparisonThetaHullObstruction : Prop :=
  PaperThetaPilotHullNormalizationRequired (l := l) T

/-- The comparison is not asserted; its exact missing normalization obstruction
is the paper hull normalization requirement. -/
def NativePaperSourceComparisonUnproved : Prop :=
  NativePaperSourceComparisonThetaHullObstruction (l := l) T

/-- The comparison target in terms of the constructed comparison data. -/
theorem nativePaperSourceComparison_iff_data :
    NativePaperSourceComparison T ↔
      (nativePaperSourceComparisonData T).thetaPilotHullLogMagnitude ≤
        (nativePaperSourceComparisonData T).qPilotMagnitude :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.NativeGlobalQPilotVsPaperThetaPilotActual

end
