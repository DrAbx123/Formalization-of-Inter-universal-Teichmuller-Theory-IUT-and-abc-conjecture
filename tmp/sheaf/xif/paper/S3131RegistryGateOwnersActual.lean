import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual

/-- Gate-owner handoff dictionary for shehdd's closure gate: residual id -> owner. -/
def S3131RegistryGateOwners : List (String × String) :=
  [ ("R1.M0.native-to-OriginalInput", "shehdd"),
    ("R1.M1.bad-tensor-index", "qpilot"),
    ("R1.M2M3M5.sameC-q-theta-readout", "lattice"),
    ("R2.absNorm-rational-place", "mainline"),
    ("R2.nu-generator-exponent", "mainline"),
    ("canonical.normalized-2l-root-supply", "mainline"),
    ("ThetaHalf.vform-canonical-residual", "hull"),
    ("ThetaHalf.exact-factor-residual", "hull"),
    ("ThetaHalf.canonical-q-formula-gap", "shehdd"),
    ("F4.a.value-group-splitting", "abc"),
    ("F4.b.paper-scaling-zero", "abc"),
    ("F4.c.cardP-ABC-strength", "abc"),
    ("LGP.residuals", "stage4"),
    ("first-triangle.A-C", "stepxi"),
    ("cusp.same-C-id", "shehdd") ]

theorem S3131RegistryGateOwners_length :
    S3131RegistryGateOwners.length = 15 := rfl

#check S3131RegistryGateOwners
#check S3131RegistryGateOwners_length
-- recompiled against rebuilt S3131FinalResidualRegistryActual (SIZE 9250, 15 ids, 03:17:01)
-- recompiled against final registry SIZE 10039 (olean 03:24:43, 15 ids/order unchanged)
