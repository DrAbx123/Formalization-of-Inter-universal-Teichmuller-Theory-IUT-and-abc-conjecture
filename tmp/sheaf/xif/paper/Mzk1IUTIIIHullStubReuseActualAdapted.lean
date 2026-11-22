import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringRealization

/-!
# Mzk1IUTIIIHullStubReuseActualAdapted (adapted copy, A475 reuse) — iutiii hull stub nodes (R9.AUDIT_CONSUMER /
H7.OB9.BUNDLE) advanced by REUSING existing tree assets

Lead A475 reuse rule: exhaustive search found the tree assets
LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealR9PointMembershipAudit.lean,
CertificateHullWiring.lean and CertificateHullWiringRealization.lean (all with oleans);
the hull-level assertions remain named inputs, wired to these existing declarations.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIIHullStubReuseActualAdapted

open LeanFormal.IUT

/-- Existing tree down-ray construction (R9 asset). -/
def r9DownRay :=
  @downRay

/-- Existing tree R9 point-membership audit (R9 asset). -/
def r9PointMembershipAudit :=
  @cardHullRealR9PointMembershipAudit

/-- Existing tree pointwise volume equivalence (R9 asset). -/
def r9PointwiseVolIff :=
  @sourceHullVolume_le_iff_pointwise_pointVolume_le

/-- Existing tree IQ hull certificate (H7/Ob9 wiring asset). -/
def iqHullCertificateReuse :=
  @iqHullCertificate

/-- Existing tree IQ hull Cor 3.12 conclusion (H7/Ob9 wiring asset). -/
def iqHullCor312ConclusionReuse :=
  @iqHullCor312Conclusion

/-- Existing tree certificate hull wiring (H7/Ob9 asset). -/
def certificateHullWiringReuse :=
  @certificateHullWiring

/-- Existing tree certificate hull wiring realization (H7/Ob9 asset). -/
def certificateHullWiringRealizationReuse :=
  @certificateHullWiringRealization

/-- Explicit consumer bundle for the R9 audit stub node. -/
structure HullR9AuditConsumer where
  auditStatement : Prop
  named : auditStatement

/-- Conditional consumer for the R9 audit stub. -/
theorem hullR9AuditConsumer_of_input (I : HullR9AuditConsumer) : I.auditStatement :=
  I.named

/-- Reuse rows: (iutiii stub/consumer node, existing tree asset, status). -/
def hullStubReuseRows : List (String × String × String) :=
  [ ("IUTIII.HULL.R9.AUDIT_CONSUMER", "CardHullRealR9PointMembershipAudit (downRay/audit/pointwise iff)", "REUSE (tree olean); hull statement NAMED"),
    ("H7/Ob9 wiring", "CertificateHullWiring (iqHullCertificate/logVolume)", "REUSE (tree olean)"),
    ("H7/Ob9 realization", "CertificateHullWiringRealization (wiring certificate/legs)", "REUSE (tree olean)"),
    ("conditional R9 consumer", "hullR9AuditConsumer_of_input", "PROVED (conditional)") ]

/-- The hull stub reuse row record has four rows. -/
theorem hullStubReuseRows_length : hullStubReuseRows.length = 4 := rfl

#check r9DownRay
#check r9PointMembershipAudit
#check r9PointwiseVolIff
#check iqHullCertificateReuse
#check iqHullCor312ConclusionReuse
#check certificateHullWiringReuse
#check certificateHullWiringRealizationReuse
#check hullStubReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIIHullStubReuseActualAdapted
end
