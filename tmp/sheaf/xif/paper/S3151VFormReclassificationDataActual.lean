import LeanFormal.IUT.Audit.Status

/-! # S3151: hull V-form reclassification data (Theta-side identity is elementary)

Verified reduction facts: the V-form/canonical identity decomposes into rooted
scaling (R1) + weighted arithmetic identity (R2); sharp residual = concrete
rooted scaling data, NOT the identity.  Doc-only; pins unchanged.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (item, corpus citation, formal artifact) rows. -/
def S3151VFormReclassification : List (String × String × String) := [
  ("RootedScalingDecomposition (R1): rootThetaHullLog b = log(scalar b)",
   "IUT III Prop 3.9(i) corpus 6838-6860 (log-volume of lambda*O = log lambda); Rem 3.9.4 ~7151 (elementary log-link compatibility)",
   "S3132VFormScalingReductionActual.RootedScalingDecomposition"),
  ("hull definition H = lambda*O",
   "IUT III Rem 3.9.5(i) corpus 7652-7680",
   "corpus definition; formalized in the reduction file context"),
  ("canonicalReadout_eq_weighted_scaling",
   "consequence of R1 + weighted rooted definition",
   "S3132VFormScalingReductionActual.canonicalReadout_eq_weighted_scaling"),
  ("ReducedVFormResidual = R1 + R2",
   "decomposed residual data",
   "S3132VFormScalingReductionActual.ReducedVFormResidual"),
  ("vformCanonical_of_reducedResidual",
   "reduction theorem: reduced residual => original V-form identity",
   "S3132VFormScalingReductionActual.vformCanonical_of_reducedResidual") ]

theorem S3151VFormReclassification_length : S3151VFormReclassification.length = 5 := rfl

/-- V-form reclassification record. -/
def S3151VFormReclassificationRecord : Obligation :=
  { id := "IUT.project.vform-reclassification-hull"
    source := "Lead audit appendix item; S3132VFormScalingReductionActual (CITABLE, 4 decls); corpus III Prop 3.9(i) 6838-6860, Rem 3.9.5(i) 7652-7680, Rem 3.9.4 ~7151"
    status := VerificationStatus.interface
    note :=
      "V-FORM RECLASSIFICATION (hull's Theta-side identity): the identity is ELEMENTARY/"
      ++ "DECOMPOSABLE, not a deep independent input. S3132VFormScalingReductionActual proves "
      ++ "RootedScalingDecomposition + canonicalReadout_eq_weighted_scaling + ReducedVFormResidual "
      ++ "=> vformCanonical_of_reducedResidual. SHARP RESIDUAL = concrete rooted scaling data "
      ++ "(R1 + R2), NOT the identity itself. Doc-only appendix addition; pins registry 13129 / "
      ++ "gate 23066 / record 15501 unchanged; no re-pin."
    dependsOn := [ "S3132VFormScalingReductionActual" ] }

#check S3151VFormReclassificationRecord
#check S3151VFormReclassification_length

end LeanFormal.IUT.Audit
