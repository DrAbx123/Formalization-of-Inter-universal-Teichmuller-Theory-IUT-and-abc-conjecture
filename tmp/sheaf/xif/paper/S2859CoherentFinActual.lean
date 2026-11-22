import tmp.sheaf.xif.paper.S2858Z2GroupFinActual
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2859CoherentFinActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2858Z2GroupFinActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

noncomputable def sMapCompC {b₀ b₁ b₂ : SingleObj SignGroup}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    sMap X inv (f ≫ g) ≅ sMap X inv f ≫ sMap X inv g :=
  sMapCompGroup X inv invSq (show SignGroup from f) (show SignGroup from g)

noncomputable def sMapIdC (b : SingleObj SignGroup) :
    sMap X inv (𝟙 b) ≅ (𝟙 X.stack.fiber : X.stack.fiber ⟶ X.stack.fiber) := by
  rw [CategoryTheory.SingleObj.id_as_one]
  simp [sMap]
  exact Iso.refl _

noncomputable def diagramC : SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F :=
  Iut.signActionDiagramOf (F := F)
    (fun _ => X.stack.fiber)
    (fun {b b'} (f : b ⟶ b') => sMap X inv f)
    (fun b => sMapIdC X inv b)
    (fun {b₀ b₁ b₂} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) => sMapCompC X inv invSq f g)
    (by
      intro b₀ b₁ b₂ b₃ f g h
      have hgg : (Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by decide
      rcases signGroup_cases f with rfl | rfl <;>
      rcases signGroup_cases g with rfl | rfl <;>
      rcases signGroup_cases h with rfl | rfl <;>
      simp [sMap, sMapCompC, sMapCompGroup, sMapIdC, e,
        SingleObj.comp_as_mul, SingleObj.id_as_one, hgg, mul_one, one_mul]
      all_goals try rw [cast_eq] at *
      case inl.inl.inr =>
        set_option pp.all true in trace_state
        first
        | (rw [invSq.inv_hom_id]; simp)
        | (try bicategory_coherence; try simp)
      case inl.inr.inr =>
        set_option pp.all true in trace_state
        first
        | (rw [invSq.inv_hom_id]; simp)
        | (try bicategory_coherence; try simp))
    (by
      intro b₀ b₁ f
      rcases signGroup_cases f with rfl | rfl <;>
      simp [sMap, sMapCompC, sMapCompGroup, sMapIdC,
        SingleObj.comp_as_mul, SingleObj.id_as_one])
    (by
      intro b₀ b₁ f
      rcases signGroup_cases f with rfl | rfl <;>
      simp [sMap, sMapCompC, sMapCompGroup, sMapIdC,
        SingleObj.comp_as_mul, SingleObj.id_as_one])

#check diagramC
#print axioms diagramC

end LeanFormal.IUT.XiFPaper.S2859CoherentFinActual