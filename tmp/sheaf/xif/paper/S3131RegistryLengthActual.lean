import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual

open LeanFormal.IUT.Audit

/-- Registry size check: the final residual registry has exactly 14 entries. -/
theorem S3131FinalResidualRegistry_length :
    S3131FinalResidualRegistry.length = 15 := rfl

#check S3131FinalResidualRegistry_length
-- recompiled against rebuilt S3131FinalResidualRegistryActual (SIZE 9250, 15 ids, 03:17:01)
-- recompiled against final registry SIZE 10039 (olean 03:24:43, 15 ids/order unchanged)
