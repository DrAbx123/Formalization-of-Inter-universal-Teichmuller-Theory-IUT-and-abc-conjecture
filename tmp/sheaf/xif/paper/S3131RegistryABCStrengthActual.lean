import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual

/-- The only ABC-strength residual in the final registry (card P, IUT IV section 2).
All other residuals are narrow structural/normalization/input components. -/
def S3131ABCStrengthResiduals : List String :=
  ["F4.c.cardP-ABC-strength"]

theorem S3131ABCStrengthResiduals_length :
    S3131ABCStrengthResiduals.length = 1 := rfl

#check S3131ABCStrengthResiduals
#check S3131ABCStrengthResiduals_length
-- recompiled against rebuilt S3131FinalResidualRegistryActual (SIZE 9250, 15 ids, 03:17:01)
-- recompiled against final registry SIZE 10039 (olean 03:24:43, 15 ids/order unchanged)
