import tmp.sheaf.xif.paper.S3137GateInspectionRecordActual
import tmp.sheaf.xif.paper.S3137ResidualIndexReportActual

/-! Axiom probe: final gate inspection record + index report (data only). -/
open LeanFormal.IUT.Audit

#print axioms S3137GateInspectionRecord
#print axioms S3137GateInspectionQuarantine
#print axioms S3137ResidualIndexReport
#check S3137GateInspectionQuarantine_length
#check S3137ResidualIndexParentMap_length
#check S3137ResidualIndex_total_eq
