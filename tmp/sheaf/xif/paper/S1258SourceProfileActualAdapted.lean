import tmp.sheaf.xif.paper.S1231SourceCoreActual
import tmp.sheaf.xif.paper.S1233ThetaPossibleImageActual

/-! # S1258: actual Profile on I.family.index

Uses the actual S1231 Core (source index translations), the S1232 sourceLogVolume
shift laws, and the S1233 thetaPossibleImage.  This builds Profile; Carrier is
blocked separately by the missing exact level/ind3 equality and connector.
No SourceIndActionData type exists in the tree. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1258SourceProfileActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual
open LeanFormal.IUT.XiFPaper.S1231SourceCoreActual
open LeanFormal.IUT.XiFPaper.S1232LogVolumeShiftActual
open LeanFormal.IUT.XiFPaper.S1233ThetaPossibleImageActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual Profile on the source family index. -/
noncomputable def sourceProfile :
    Profile (sourceCore (I := I)) where
  logVolume := sourceLogVolume (I := I)
  possibleImage := thetaPossibleImage (I := I)
  ind1_invariant := by
    intro g c
    exact (s1232LogVolumeShiftLaws (I := I)).1 g c
  ind2_invariant := by
    intro g c
    exact (s1232LogVolumeShiftLaws (I := I)).2.1 g c
  ind3_upper := by
    intro n c
    exact (s1232LogVolumeShiftLaws (I := I)).2.2 n c
  possibleImage_nonempty := by
    intro c
    exact thetaPossibleImage_nonempty (I := I) c
  possibleImage_ind1 := by
    intro g c
    exact thetaPossibleImage_eq (I := I) _ _
  possibleImage_ind2 := by
    intro g c
    exact thetaPossibleImage_eq (I := I) _ _
  possibleImage_ind3 := by
    intro n c z hz
    exact ⟨z, by simpa [thetaPossibleImage_eq (I := I) _ _] using hz, le_rfl⟩

/-- Actual Core+Profile pair on Choice = I.family.index. -/
structure SourceCoreProfile where
  core : Core ℤ (I.family.index)
  profile : Profile core

noncomputable def sourceCoreProfile (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceCoreProfile (I := I) where
  core := sourceCore (I := I)
  profile := sourceProfile (I := I)

end LeanFormal.IUT.XiFPaper.S1258SourceProfileActualAdapted
end