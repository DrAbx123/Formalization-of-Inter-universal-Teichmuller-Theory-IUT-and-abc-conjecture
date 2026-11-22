import tmp.sheaf.xif.paper.S3119StrongTransEqActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
noncomputable section
variable {F : Type} [Field F] {S T : Iut.SchemeOverField F}
variable {eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)}
example (h1 h2 : eta ⟶ theta) : h1 = h2 := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _
