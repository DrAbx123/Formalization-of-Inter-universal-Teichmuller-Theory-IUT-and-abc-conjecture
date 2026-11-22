import tmp.sheaf.xif.paper.S3135ModelValueUnitActual

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueUnitBatchActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelScalingBatchActual

/-- **Model scaling pair-record** (qpilot pair design), GENERIC in the p-adic prime
`p` with `[Fact p.Prime]`: value-side unit plus completion-side base-field unit of
norm one.  The concrete instantiation `p := concreteRationalPrime` lives in the
base-unit file where the `Fact` instance for the concrete prime is in scope. -/
structure S3135ModelScaling (data : S3135ModelValueData) (p : ℕ) [Fact p.Prime] where
  valueUnit : data.Monˣ
  valueUnit_degree_one : data.degree (valueUnit : data.Mon) = 1
  baseUnit : ℚ_[p]ˣ
  baseUnit_norm_one : ‖(baseUnit : ℚ_[p])‖ = 1

/-- The scaling's value side has log-degree zero. -/
theorem s3135_modelScaling_valueLogDegree_zero
    {data : S3135ModelValueData} {p : ℕ} [Fact p.Prime]
    (s : S3135ModelScaling data p) :
    Multiplicative.toAdd (data.degree (s.valueUnit : data.Mon)) = 0 := by
  rw [s.valueUnit_degree_one]
  rfl

/-- The scaling's base unit is nonzero (unit of a field). -/
theorem s3135_modelScaling_baseUnit_ne_zero
    {data : S3135ModelValueData} {p : ℕ} [Fact p.Prime]
    (s : S3135ModelScaling data p) :
    (s.baseUnit : ℚ_[p]) ≠ 0 :=
  Units.ne_zero s.baseUnit

#check S3135ModelScaling
#check s3135_modelScaling_valueLogDegree_zero
#check s3135_modelScaling_baseUnit_ne_zero
end LeanFormal.IUT.XiFPaper.S3135ModelScalingBatchActual
end
