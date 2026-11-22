import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual

set_option backward.isDefEq.respectTransparency false

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open Multiplicative

namespace LeanFormal.IUT.XiFPaper.S3121SignDataActual

variable {l : PrimeGeFive}

noncomputable abbrev S3121Obj :
    SingleObj Iut.SignGroup → Iut.EtaleStackPseudofunctor (S1280Arithmetic l).F :=
  fun _ => S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l)

theorem S3121Fiber_eq_YS :
    (S1536XF (l := l)).stack.fiber =
      S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l) := rfl

noncomputable def S3121AtBase :
    Bicategory.Equivalence (S3121Obj (l := l) (Quiver.SingleObj.star Iut.SignGroup))
      (S1536XF (l := l)).stack.fiber :=
  Bicategory.Equivalence.id _

noncomputable def S3121MapFixed (x : Iut.SignGroup) :
    S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l) ⟶
      S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l) := by
  classical
  exact if x = (1 : Iut.SignGroup) then 𝟙 _
  else S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
    (S3119NegOverHom (l := l))

noncomputable abbrev S3121Map {b b' : SingleObj Iut.SignGroup}
    (f : b ⟶ b') : S3121Obj (l := l) b ⟶ S3121Obj (l := l) b' :=
  S3121MapFixed (l := l) (f : Iut.SignGroup)

noncomputable def S3121MapId (b : SingleObj Iut.SignGroup) :
    S3121Map (l := l) (𝟙 b) ≅ 𝟙 (S3121Obj (l := l) b) := by
  change S3121MapFixed (l := l) (1 : Iut.SignGroup) ≅ 𝟙 _
  dsimp only [S3121MapFixed]
  rw [if_pos rfl]

lemma S3121SignGroup_eq_one_or_generator (x : Iut.SignGroup) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  have hx : ofAdd (toAdd x) = x := ofAdd_toAdd x
  rw [← hx]
  let n : ZMod 2 := toAdd x
  have hlt : n.val < 2 := ZMod.val_lt n
  interval_cases h : n.val
  · left
    have hn : n = 0 := (ZMod.val_eq_zero (n := 2) (a := n)).mp h
    rw [show toAdd x = n from rfl, hn]
    rfl
  · right
    have hn : n = 1 := (ZMod.val_eq_one (by norm_num : 1 < 2) n).mp h
    rw [show toAdd x = n from rfl, hn]

noncomputable def S3121MapComp
    {b₀ b₁ b₂ : SingleObj Iut.SignGroup}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    S3121Map (l := l) (f ≫ g) ≅ S3121Map (l := l) f ≫ S3121Map (l := l) g := by
  change S3121MapFixed (l := l) ((f ≫ g : Iut.SignGroup)) ≅
    S3121MapFixed (l := l) (f : Iut.SignGroup) ≫
      S3121MapFixed (l := l) (g : Iut.SignGroup)
  dsimp only [S3121MapFixed]
  have hb0 : b₀ = b₂ := Subsingleton.elim _ _
  have hb1 : b₁ = b₂ := Subsingleton.elim _ _
  subst hb0
  subst hb1
  by_cases hf : (f : Iut.SignGroup) = (1 : Iut.SignGroup)
  · by_cases hg : (g : Iut.SignGroup) = (1 : Iut.SignGroup)
    · have hfg : ((f ≫ g : Iut.SignGroup)) = (1 : Iut.SignGroup) := by
        rw [SingleObj.comp_as_mul, hg, hf]
        rfl
      rw [if_pos hfg, if_pos hf, if_pos hg]
      exact (Pseudofunctor.StrongTrans.leftUnitor
        (𝟙 (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l)))).symm
    · have hfg : ¬ ((f ≫ g : Iut.SignGroup) = (1 : Iut.SignGroup)) := by
        intro h
        rw [hf] at h
        rw [← SingleObj.id_as_one (x := b₁)] at h
        rw [Category.id_comp] at h
        exact hg (by simpa [SingleObj.id_as_one] using h)
      rw [if_neg hfg, if_pos hf, if_neg hg]
      exact (Pseudofunctor.StrongTrans.leftUnitor
        (S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
          (S3119NegOverHom (l := l)))).symm
  · by_cases hg : (g : Iut.SignGroup) = (1 : Iut.SignGroup)
    · have hfg : ¬ ((f ≫ g : Iut.SignGroup) = (1 : Iut.SignGroup)) := by
        intro h
        rw [hg] at h
        rw [← SingleObj.id_as_one (x := b₁)] at h
        rw [Category.comp_id] at h
        exact hf (by simpa [SingleObj.id_as_one] using h)
      rw [if_neg hfg, if_neg hf, if_pos hg]
      exact (Pseudofunctor.StrongTrans.rightUnitor
        (S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
          (S3119NegOverHom (l := l)))).symm
    · have hf' : f = Multiplicative.ofAdd (1 : ZMod 2) := by
        rcases S3121SignGroup_eq_one_or_generator f with h | h
        · exact absurd h hf
        · exact h
      have hg' : g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rcases S3121SignGroup_eq_one_or_generator g with h | h
        · exact absurd h hg
        · exact h
      have hfg : ((f ≫ g : Iut.SignGroup)) = (1 : Iut.SignGroup) := by
        rw [SingleObj.comp_as_mul, hf', hg']
        change (Multiplicative.ofAdd ((1 : ZMod 2) + (1 : ZMod 2)) :
          Iut.SignGroup) = 1
        rw [show (1 : ZMod 2) + (1 : ZMod 2) = 0 from by
          rw [show (1 : ZMod 2) + (1 : ZMod 2) = (2 : ZMod 2) by norm_num]
          exact ZMod.natCast_self 2]
        rfl
      rw [if_pos hfg, if_neg hf, if_neg hg]
      change 𝟙 (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l)) ≅
        Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
            (S3119NegOverHom (l := l)))
          (S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
            (S3119NegOverHom (l := l)))
      rw [S3121StrongTransOfHom_vcomp, S3119NegOverHom_sq,
        S3121StrongTransOfHom_id]
      exact Iso.refl _

#check S3121Obj
#check S3121AtBase
#check S3121Map
#check S3121MapId
#check S3121MapComp

end LeanFormal.IUT.XiFPaper.S3121SignDataActual
end
