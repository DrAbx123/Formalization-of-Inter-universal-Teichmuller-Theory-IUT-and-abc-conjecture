import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActualAdapted

/-! # Native q-pilot / paper Theta-pilot shared-source alignment

Checks that NativeGlobalQPilotNormalizedLogVolumeActual and
PaperThetaPilotCarrierActualAdapted use the SAME native T and the SAME actual base q
family.

Both files take T : SourceNativeInitialThetaData l and index by the native bad
family Bad (nativePlaceSelection T).  Both use BaseQFamilyActual.baseQ T b, the
actual DVR q candidate at nativeBaseSectionPlace T b.

The q-pilot normalized magnitude uses

  baseQLogMagnitude T b = -log ||(baseQ T b).q||,

while the paper Theta-pilot carrier uses

  paperBaseQReal T b = ||(baseQ T b).q||.

This file proves those are the same q value and records the shared family.  No
I.initial.badPlaces bridge and no different q source is introduced.  No
inequality/sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeGlobalQPilotThetaPilotAlignmentActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActualAdapted
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The shared actual bad index used by both the native q-pilot normalization
and the paper Theta-pilot carrier. -/
abbrev SharedNativeBadIndex : Type := Bad (nativePlaceSelection T)

/-- Both constructions use the same actual q candidate baseQ T b. -/
noncomputable def sharedNativeBaseQ
    (b : SharedNativeBadIndex T) :
    FinitePlaceQCandidate (nativeBaseSectionPlace T b) :=
  baseQ T b

/-- The q-pilot base q log-magnitude is the negative log of the shared q norm. -/
theorem sharedBaseQLogMagnitude_eq :
    ∀ b : SharedNativeBadIndex T,
      baseQLogMagnitude T b = -Real.log ‖(sharedNativeBaseQ T b).q‖ := by
  intro b
  unfold baseQLogMagnitude baseQ localLogMagnitude localSignedLog sharedNativeBaseQ
  rfl

/-- The paper Theta-pilot real q is exactly the norm of the same shared q. -/
theorem sharedPaperBaseQReal_eq :
    ∀ b : SharedNativeBadIndex T,
      paperBaseQReal T b = ‖(sharedNativeBaseQ T b).q‖ := by
  intro b
  rfl

/-- The native q-pilot local normalized magnitude uses the shared q norm. -/
theorem sharedNativeQPilotLocalMagnitude_eq :
    ∀ b : SharedNativeBadIndex T,
      nativeQPilotLocalNormalizedLogMagnitude T b =
        nativeQPilotLocalNormalizedWeight T b *
          (-Real.log ‖(sharedNativeBaseQ T b).q‖) := by
  intro b
  rw [nativeQPilotLocalNormalizedLogMagnitude_eq, sharedBaseQLogMagnitude_eq]

end LeanFormal.IUT.XiFPaper.NativeGlobalQPilotThetaPilotAlignmentActualAdapted

end
