import tmp.sheaf.xif.paper.S1225SourceChoiceCoreActual

/-! # S1232: sourceLogVolume shift laws, actual

All theaters in I.family have the same thetaPacket.q by the actual family link
q-invariance I.family.link_q.  FiniteThetaPacket.logVolume is determined by q
via log(scale j) = gaussExponent j * log q, hence logVolume is constant on the
whole family index.  Therefore the S1225 shift laws hold actually; no exact
condition remains. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1232LogVolumeShiftActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- All source theater theta packet q values are equal. -/
theorem sourceThetaQ_eq (c c' : Choice (I := I)) :
    (I.family.theater c).thetaPacket.q =
      (I.family.theater c').thetaPacket.q :=
  I.family.link_q c c'

/-- The actual sourceLogVolume is constant on the family index. -/
theorem sourceLogVolume_eq (c c' : Choice (I := I)) :
    sourceLogVolume (I := I) c = sourceLogVolume (I := I) c' := by
  unfold sourceLogVolume
  rw [FiniteThetaPacket.logVolume_eq_sum, FiniteThetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteThetaPacket.log_scale, FiniteThetaPacket.log_scale,
    sourceThetaQ_eq (I := I) c c']

/-- Actual S1225 log-volume shift laws. -/
theorem s1232LogVolumeShiftLaws :
    S1225LogVolumeShiftLaws (I := I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g c
    exact sourceLogVolume_eq (I := I) (sourceInd1 (I := I) g c) c
  · intro g c
    exact sourceLogVolume_eq (I := I) (sourceInd2 (I := I) g c) c
  · intro n c
    exact le_of_eq (sourceLogVolume_eq (I := I) c (sourceInd3 (I := I) n c))

end LeanFormal.IUT.XiFPaper.S1232LogVolumeShiftActual
end