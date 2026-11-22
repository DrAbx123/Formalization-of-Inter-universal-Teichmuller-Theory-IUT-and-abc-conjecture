import tmp.sheaf.xif.paper.S3137ModelIndexArithmeticActual
import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual
import tmp.sheaf.xif.paper.S3137ModelPlaceToModActual
import tmp.sheaf.xif.paper.S3137C3ClosureRecordActual

/-! Axiom probe: model skeleton (index/theater/placeToMod) + C3 closure record. -/
open LeanFormal.IUT.XiFPaper.S3137ModelIndexArithmeticActual
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual
open LeanFormal.IUT.XiFPaper.S3137ModelPlaceToModActual
open LeanFormal.IUT.Audit

#print axioms modelIndexEquiv_apply
#print axioms modelPermutation_apply
#print axioms modelHorizontalShift_apply
#print axioms modelIndex_not_subsingleton
#print axioms S3137ModelIndexArithmeticRecord
#print axioms S3137ModelTheaterSkeletonRecord
#print axioms S3137ModelPlaceToModRecord
#print axioms S3137C3ConventionClosureRecord
#check ModelTheaterData.toFamily
#check ModelPlaceToModData.ofInjective