import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual
import tmp.sheaf.xif.paper.S3137ModelPlaceToModActual
import tmp.sheaf.xif.paper.S3137VendorMappingActual

/-! Axiom probe: model theater/placeToMod + vendor mapping records. -/
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual
open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModActual
open LeanFormal.IUT.XiFPaper.S3137VendorMappingActual
open LeanFormal.IUT.Audit

#print axioms modelIndex_not_subsingleton
#print axioms modelPlace_zero_ne_one
#print axioms S3137ModelTheaterSkeletonRecord
#print axioms S3137ModelPlaceToModRecord
#print axioms S3137VendorCorollarySchemaMapping
#print axioms S3137VendorTreasureInventory
#print axioms INDEX_VENDOR_COR312_SCHEMA
#check ModelTheaterData.toFamily
#check ModelPlaceToModData.ofInjective
