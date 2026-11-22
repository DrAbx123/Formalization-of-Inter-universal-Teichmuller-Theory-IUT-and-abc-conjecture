import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual

/-- The missing converse bridge of S1742: equality of underlying Over morphisms
determines equality of strong transformations between the two Yoneda
pseudofunctors.  The app components agree by S1742AppEq; the naturality
2-isomorphism is an equality in a Discrete fibre, and the coherence fields are
propositions. -/
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

/-- The exact field-5 target, as a proposition. -/
def S3119StrongTrans_eq_of_hom_eq_target (F : Type) [Field F]
    {S T : Iut.SchemeOverField F} : Prop :=
  ∀ eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S)
      (S1742YS (F := F) T),
    S1742HomOfStrongTrans (F := F) eta =
      S1742HomOfStrongTrans (F := F) theta → eta = theta

/-- The target is inhabited. -/
theorem S3119StrongTrans_eq_of_hom_eq_target_proof (F : Type) [Field F]
    {S T : Iut.SchemeOverField F} :
    S3119StrongTrans_eq_of_hom_eq_target (F := F) (S := S) (T := T) := by
  intro eta theta h
  exact S3119StrongTrans_eq_of_hom_eq F eta theta h

#check S3119StrongTrans_eq_of_hom_eq
#check S3119StrongTrans_eq_of_hom_eq_target
#check S3119StrongTrans_eq_of_hom_eq_target_proof
#print axioms S3119StrongTrans_eq_of_hom_eq
#print axioms S3119StrongTrans_eq_of_hom_eq_target_proof
end LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
end
