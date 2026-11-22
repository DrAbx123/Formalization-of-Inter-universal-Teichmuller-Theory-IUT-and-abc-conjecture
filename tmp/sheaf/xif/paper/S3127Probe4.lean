import tmp.sheaf.xif.paper.S3119StrongTransEqActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
noncomputable section
variable {F : Type} [Field F] {S T : Iut.SchemeOverField F}
variable {eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)}
variable (e : eta ≅ theta)
#check e.hom
#check Pseudofunctor.StrongTrans.Hom
#print Pseudofunctor.StrongTrans.Hom
