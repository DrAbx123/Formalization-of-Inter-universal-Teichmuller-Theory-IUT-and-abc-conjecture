import tmp.sheaf.xif.paper.S2858Z2GroupActual
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2859CoherentActual
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2858Z2GroupActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))

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
      simp [sMap, hgg, mul_one, one_mul]
      simp [sMapCompC, sMapCompGroup, sMapIdC,
        SingleObj.comp_as_mul, SingleObj.id_as_one]
      case inl.inl.inr =>
        bicategory_coherence
      case inl.inr.inr =>
        rw [invSq.inv_hom_id]
        simp)
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

end LeanFormal.IUT.XiFPaper.S2859CoherentActual