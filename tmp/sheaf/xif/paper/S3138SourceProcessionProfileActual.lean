import tmp.sheaf.xif.paper.S3138SourceProcessionCoreActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: actual source procession log-volume and profile

Second half of the source-level procession kernel for IUT III Theorem 3.11.
From a genuine `OriginalInput` this file constructs the actual Theta log-volume
readout on the source choices and proves that it is a `Profile` for the source
core of `S3138SourceProcessionCoreActual`.

The log-volume is the actual theater Theta log-volume
`(I.family.theater i).thetaPacket.logVolume`.  Its constancy over the family is
proved from the family link q-transport (`I.family.link_q`) together with the
Gaussian-exponent formula `FiniteThetaPacket.log_scale`; the possible image is
the singleton of that readout (the source packet profile has no spread).

Source: IUT II (Theta-packet log-volume), IUT III Theorem 3.11 (procession
profile).  Consumer: `S3138SourceProcessionCarrierActual` (connector, carrier)
and `S3138SourceStepXIActual`.
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The actual theater Theta log-volume attached to a source choice. -/
noncomputable def sourceStepXILogVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceStepXIChoice I) : Real :=
  (I.family.theater c.1).thetaPacket.logVolume

/-- The actual theater Theta log-volume is constant on the family index: the
family links preserve the Theta q, and the packet log-volume is determined by
the packet q through the Gaussian exponents. -/
theorem sourceStepXIThetaLogVolume_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (i j : I.family.index) :
    (I.family.theater i).thetaPacket.logVolume =
      (I.family.theater j).thetaPacket.logVolume := by
  rw [FiniteThetaPacket.logVolume_eq_sum, FiniteThetaPacket.logVolume_eq_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [FiniteThetaPacket.log_scale, FiniteThetaPacket.log_scale, I.family.link_q i j]

/-- Constancy of the source log-volume on choices. -/
theorem sourceStepXILogVolume_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c c' : SourceStepXIChoice I) :
    sourceStepXILogVolume I c = sourceStepXILogVolume I c' :=
  sourceStepXIThetaLogVolume_eq I c.1 c'.1

/-- The actual `Profile` of the source procession: the actual theater
log-volume with the singleton possible image. -/
noncomputable def sourceStepXIProfile
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Profile (sourceStepXICore I) where
  logVolume := sourceStepXILogVolume I
  possibleImage c := {sourceStepXILogVolume I c}
  ind1_invariant := by
    intro g c
    exact sourceStepXILogVolume_eq I ((sourceStepXICore I).ind1 g c) c
  ind2_invariant := by
    intro g c
    exact sourceStepXILogVolume_eq I ((sourceStepXICore I).ind2 g c) c
  ind3_upper := by
    intro n c
    exact le_of_eq (sourceStepXILogVolume_eq I c ((sourceStepXICore I).ind3 n c))
  possibleImage_nonempty := by
    intro c
    exact ⟨sourceStepXILogVolume I c, by simp⟩
  possibleImage_ind1 := by
    intro g c
    rw [sourceStepXILogVolume_eq I ((sourceStepXICore I).ind1 g c) c]
  possibleImage_ind2 := by
    intro g c
    rw [sourceStepXILogVolume_eq I ((sourceStepXICore I).ind2 g c) c]
  possibleImage_ind3 := by
    intro n c z hz
    refine ⟨sourceStepXILogVolume I ((sourceStepXICore I).ind3 n c), by simp, ?_⟩
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact le_of_eq (sourceStepXILogVolume_eq I c ((sourceStepXICore I).ind3 n c))

/-- The source profile at the base choice is the actual Theta log-volume of
the input theater at `(0,0)`. -/
theorem sourceStepXIProfile_base_theta
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (sourceStepXIProfile I).logVolume (sourceStepXICore I).base =
      (I.theaterAt 0 0).thetaPacket.logVolume := rfl

/-- The source profile log-volume is independent of the chosen family index at
fixed level: the actual source log-volume is a function of the level readout
only through the actual family link transport. -/
theorem sourceStepXIProfile_logVolume_const
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c c' : SourceStepXIChoice I) :
    (sourceStepXIProfile I).logVolume c = (sourceStepXIProfile I).logVolume c' :=
  sourceStepXILogVolume_eq I c c'

end LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual

end
