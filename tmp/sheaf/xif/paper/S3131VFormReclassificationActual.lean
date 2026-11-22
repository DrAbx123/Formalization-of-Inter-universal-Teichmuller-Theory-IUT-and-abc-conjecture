import LeanFormal.IUT.Audit.Status

/-! # S3131 Theta-side V-form reclassification (hull revision) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131VFormReclassificationActual

def S3131VFormReclassification : List (String × String) :=
  [ ("old classification", "MissingConcreteVFormCanonicalReadout as an independent hard residual"),
    ("revision", "REVISED: rooted hulls DEFINED as lambda*O (III Rem 3.9.5(i), corpus 7652-7680); log-volume of lambda*O = log lambda (III Prop 3.9(i) corpus 6838-6860; Rem 3.9.4 ~7151)"),
    ("new decomposition", "(R1) RootedScalingDecomposition + (R2) weighted arithmetic identity; ReducedVFormResidual"),
    ("new theorem", "vformCanonical_of_reducedResidual: ReducedVFormResidual => MissingConcreteVFormCanonicalReadout (S3132VFormScalingReductionActual EXIT0 155510, checker CITABLE, 4 decls; probe 155698)"),
    ("sharp residual", "RootedScalingDecomposition (concrete rooted scaling data from T) + ReducedVFormResidual; NOT the identity"),
    ("classification", "elementary/decomposable (class A/B)") ]

theorem S3131VFormReclassification_length : S3131VFormReclassification.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131VFormReclassificationActual