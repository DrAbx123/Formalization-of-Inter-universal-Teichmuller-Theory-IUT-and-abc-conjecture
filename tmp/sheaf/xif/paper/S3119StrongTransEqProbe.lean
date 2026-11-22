import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S3119StrongTransEqProbe

theorem S3119StrongTrans_eq_of_hom_eq (F : Type) [Field F]
    {S T : Iut.SchemeOverField F}
    (eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S)
      (S1742YS (F := F) T))
    (h : S1742HomOfStrongTrans (F := F) eta =
      S1742HomOfStrongTrans (F := F) theta) : eta = theta := by
  have happ : ∀ a, eta.app a = theta.app a := by
    intro a
    rw [← S1742AppEq eta a, ← S1742AppEq theta a, h]
  cases eta with
  | mk app nat nn ni nc =>
  cases theta with
  | mk app' nat' nn' ni' nc' =>
  simp only at happ
  have happ' : app = app' := funext happ
  subst app'
  congr
  · funext a b f
    apply CategoryTheory.Iso.ext
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  all_goals exact Subsingleton.elim _ _

#check S3119StrongTrans_eq_of_hom_eq
#print axioms S3119StrongTrans_eq_of_hom_eq
end LeanFormal.IUT.XiFPaper.S3119StrongTransEqProbe
end
