import tmp.sheaf.xif.paper.S3119StrongTransEqActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual

namespace LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual

/-- Strict composition bridge: `S1742StrongTransOfHom` preserves composition. -/
theorem S3121StrongTransOfHom_vcomp (F : Type) [Field F]
    {S T U : Iut.SchemeOverField F} (f : S ⟶ T) (g : T ⟶ U) :
    Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (F := F) f)
        (S1742StrongTransOfHom (F := F) g) =
      S1742StrongTransOfHom (F := F) (f ≫ g) := by
  apply S3119StrongTrans_eq_of_hom_eq
  rw [S1742HomOfStrongTrans_vcomp]
  simp [S1742HomOfStrongTrans_strongTransOfHom]


theorem S3121StrongTransOfHom_id (F : Type) [Field F]
    (S : Iut.SchemeOverField F) :
    S1742StrongTransOfHom (F := F) (𝟙 S) =
      Pseudofunctor.StrongTrans.id (S1742YS (F := F) S) := by
  apply S3119StrongTrans_eq_of_hom_eq
  rw [S1742HomOfStrongTrans_strongTransOfHom]
  rfl

#check S3121StrongTransOfHom_id
#print axioms S3121StrongTransOfHom_id

#check S3121StrongTransOfHom_vcomp
#print axioms S3121StrongTransOfHom_vcomp

end LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
end
