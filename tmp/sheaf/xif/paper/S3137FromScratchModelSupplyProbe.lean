import tmp.sheaf.xif.paper.S3137FromScratchModelSupplyActual

/-! Axiom probe: from-scratch model supply (index arithmetic + bad donor + records). -/
open LeanFormal.IUT.XiFPaper.S3137FromScratchModelSupplyActual
open LeanFormal.IUT.Audit

#print axioms fromScratchIndexEquiv_apply
#print axioms S3137FromScratchIndexArithmetic
#print axioms S3137FromScratchBadTensorDonor
#print axioms S3137RealifiedGeneratorDegreeTool
#check badSelfTensorIndexDonor
#check TensorIndexPlaceCompatibility
