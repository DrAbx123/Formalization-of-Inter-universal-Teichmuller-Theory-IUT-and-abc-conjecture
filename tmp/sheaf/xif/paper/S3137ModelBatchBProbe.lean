import tmp.sheaf.xif.paper.S3137ModelOriginalInputSkeletonActual
import tmp.sheaf.xif.paper.S3137ModelPlaceToModConstructionActual
import tmp.sheaf.xif.paper.S3137M2aClosureRecordActual
import tmp.sheaf.xif.paper.S3137AuditPinsRecordActual

/-! Axiom probe: model OriginalInput skeleton, placeToMod construction, M2a closure record, pins. -/
open LeanFormal.IUT.XiFPaper.S3137ModelOriginalInputSkeletonActual
open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModConstructionActual
open LeanFormal.IUT.Audit

#print axioms modelPlaceMap_injective
#print axioms modelPlaceToModDataOfDistinct
#print axioms S3137ModelOriginalInputRecord
#print axioms S3137ModelPlaceToModConstructionRecord
#print axioms S3137M2aClosureRecord
#print axioms S3137AuditPinsRecord
#check modelOriginalInputOfSkeleton
#check modelPlaceToModDataOfDistinct
