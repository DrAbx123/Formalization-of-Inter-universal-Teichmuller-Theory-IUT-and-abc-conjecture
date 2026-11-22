import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore

/-! # Mzk1HodgeTheaterLinkGlueActual — consumer forms of the Hodge-theater link algebra

Small reference/glue module (no new mathematics): consumes the proved link algebra of
`HodgeTheaterCore.lean` (refl/symm/trans and the `ThreeTheaterSystem` composite) in the
forms used by the Theorem 3.11 object layer.  The public Gogopex/LANA `IUT_LEAN`
Hodge-theater/prime-strip structures are the external counterparts recorded in that file.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinkGlueActual

open LeanFormal.IUT

universe ua uv upi umon

variable {l : PrimeGeFive} {V : Type uv}

/-- Left unit of the link composition. -/
theorem trans_refl_left {S T : HodgeTheater.{ua, uv, upi, umon} l V}
    (f : HodgeTheaterLink S T) :
    HodgeTheaterLink.trans (HodgeTheaterLink.refl S) f = f :=
  HodgeTheaterLink.refl_trans f

/-- Right unit of the link composition. -/
theorem trans_refl_right {S T : HodgeTheater.{ua, uv, upi, umon} l V}
    (f : HodgeTheaterLink S T) :
    HodgeTheaterLink.trans f (HodgeTheaterLink.refl T) = f :=
  HodgeTheaterLink.trans_refl f

/-- Involution of the link symmetry. -/
theorem symm_symm_apply {S T : HodgeTheater.{ua, uv, upi, umon} l V}
    (f : HodgeTheaterLink S T) :
    HodgeTheaterLink.symm (HodgeTheaterLink.symm f) = f :=
  HodgeTheaterLink.symm_symm f

/-- The three-theater composite is the declared composite link. -/
theorem threeSystem_sourceToTarget_eq (system : ThreeTheaterSystem l V) :
    system.sourceToTarget =
      HodgeTheaterLink.trans system.source_to_middle system.middle_to_target :=
  rfl

/-- The theta `q`-alignment transported by the three-theater composite. -/
theorem threeSystem_sourceToTarget_q (system : ThreeTheaterSystem l V) :
    system.source.thetaPacket.q = system.target.thetaPacket.q :=
  system.sourceToTarget_q

/-- The theta scale alignment transported by the three-theater composite. -/
theorem threeSystem_sourceToTarget_scale (system : ThreeTheaterSystem l V)
    (j : SignedLabel l.value) :
    system.source.thetaPacket.scale j = system.target.thetaPacket.scale j :=
  system.sourceToTarget_scale j

/-- The three-theater composite absorbs the source unit link. -/
theorem threeSystem_refl_sourceToTarget (system : ThreeTheaterSystem l V) :
    HodgeTheaterLink.trans (HodgeTheaterLink.refl system.source)
      system.sourceToTarget = system.sourceToTarget :=
  HodgeTheaterLink.refl_trans _

/-- The three-theater composite absorbs the target unit link. -/
theorem threeSystem_sourceToTarget_refl (system : ThreeTheaterSystem l V) :
    HodgeTheaterLink.trans system.sourceToTarget
      (HodgeTheaterLink.refl system.target) = system.sourceToTarget :=
  HodgeTheaterLink.trans_refl _

#check trans_refl_left
#check symm_symm_apply
#check threeSystem_sourceToTarget_eq
#check threeSystem_sourceToTarget_q
#check threeSystem_sourceToTarget_scale

end LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterLinkGlueActual
end
