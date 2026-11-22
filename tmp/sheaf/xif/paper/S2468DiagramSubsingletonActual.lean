import tmp.sheaf.xif.paper.S2466MapCompFullActual
import tmp.sheaf.xif.paper.S1932BuildA
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
open LeanFormal.IUT.XiFPaper.S2465MapCompLemmasActual
open LeanFormal.IUT.XiFPaper.S2466MapCompFullActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2468DiagramSubsingletonActual
local notation "Xf" => S2482Orbicurve.stack.fiber

theorem S2468CatHom₂Subsingleton
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (F G : (S2482Orbicurve.stack.fiber).obj U ⟶ (S2482Orbicurve.stack.fiber).obj U) : Subsingleton (F ⟶ G) :=
  S1932NatTransSubsingleton (Discrete.isDiscrete _) F G

instance S2468StrongTransSubsingleton (F G : Xf ⟶ Xf) : Subsingleton (F ⟶ G) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S2468CatHom₂Subsingleton U (F.app U) (G.app U)).elim _ _

noncomputable def S2468Diagram :
    Iut.SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor F :=
  LocallyDiscrete.mkPseudofunctor
    (fun _ : SingleObj Iut.SignGroup => Xf)
    (fun {b b'} (f : b ⟶ b') => S2465Map (f : Iut.SignGroup))
    (fun b => by
      dsimp [S2465Map]
      rw [if_pos]
      · exact Iso.refl _
      · exact SingleObj.id_as_one (M := Iut.SignGroup) b)
    (fun {b₀ b₁ b₂} f g => by
      let f' : Iut.SignGroup := f
      let g' : Iut.SignGroup := g
      change S2465Map (g' * f') ≅ S2465Map f' ≫ S2465Map g'
      exact S2466MapComp f' g')
    (by intros; exact Subsingleton.elim _ _)
    (by intros; exact Subsingleton.elim _ _)
    (by intros; exact Subsingleton.elim _ _)

#print axioms S2468Diagram

end LeanFormal.IUT.XiFPaper.S2468DiagramSubsingletonActual
end
