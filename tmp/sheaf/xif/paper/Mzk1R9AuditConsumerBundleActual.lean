import tmp.sheaf.xif.paper.Mzk1R9PointMembershipConsumerActual
import tmp.sheaf.xif.paper.Mzk1R9HullConsumerActual
import tmp.sheaf.xif.paper.Mzk1R9HullRayBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1R9AuditConsumerBundleActual — HULL.R9.AUDIT_CONSUMER stub implementation

Implements the DAG stub node iutiii:IUTIII.HULL.R9.AUDIT_CONSUMER by a real
consumer bundle over the R9 point-membership audit link (green deps):
down-ray = hull log-volume ray, ray membership, unboundedness below.
No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9AuditConsumerBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleActual

/-- H5 hull log-volume ray coincides with the R9 down-ray. -/
theorem r9AuditConsumerBundle_ray_eq (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta := hullLogVolumeRay_eq_downRay theta

/-- Ray membership in audit form. -/
theorem r9AuditConsumerBundle_mem {theta x : ℝ} :
    x ∈ hullLogVolumeRay theta ↔ x ≤ theta := hull09_ray_mem_r9

/-- Unboundedness below of the audit ray. -/
theorem r9AuditConsumerBundle_unbounded (a : ℝ) (k : ℕ) :
    (a - ((k : ℝ) + 1)) ∈ downRay a := downRay_unbounded a k

/-- Bundled consumer for the R9 audit stub node. -/
theorem r9AuditConsumerBundle_bundle (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta ∧
      (∀ x : ℝ, x ∈ hullLogVolumeRay theta ↔ x ≤ theta) ∧
      (∀ k : ℕ, (theta - ((k : ℝ) + 1)) ∈ downRay theta) :=
  ⟨r9AuditConsumerBundle_ray_eq theta, fun x => r9AuditConsumerBundle_mem,
    fun k => r9AuditConsumerBundle_unbounded theta k⟩

def r9AuditConsumerBundleRows : List (String × String × String) :=
  [ ("ray equality", "PROVED", "r9AuditConsumerBundle_ray_eq"),
    ("membership", "PROVED", "r9AuditConsumerBundle_mem"),
    ("unboundedness", "PROVED", "r9AuditConsumerBundle_unbounded"),
    ("bundle", "PROVED", "r9AuditConsumerBundle_bundle") ]

theorem r9AuditConsumerBundleRows_length : r9AuditConsumerBundleRows.length = 4 := rfl

#check r9AuditConsumerBundle_bundle
#check r9AuditConsumerBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9AuditConsumerBundleActual
end