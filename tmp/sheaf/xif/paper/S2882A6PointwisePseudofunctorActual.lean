import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2876NontrivialAlphaActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S2857GlobalAlphaCompatActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual

theorem signGroup_cases (g : SignGroup) :
    g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, g = Multiplicative.ofAdd a :=
    ⟨g.toAdd, (ofAdd_toAdd g).symm⟩
  rw [ha]
  fin_cases a
  · left; rfl
  · right; rfl

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq K := Classical.decEq _

abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X

/-- The A6 sign automorphism on the representing scheme. -/
noncomputable def S2882A6Aut (g : SignGroup) : X ⟶ X :=
  if g = 1 then 𝟙 X else alphaOverS2844

theorem S2882A6Aut_one : S2882A6Aut 1 = 𝟙 X := by
  simp [S2882A6Aut]

theorem S2882A6Aut_ne {g : SignGroup} (hg : g ≠ 1) :
    S2882A6Aut g = alphaOverS2844 := by
  simp [S2882A6Aut, hg]

theorem S2882A6Aut_gen :
    S2882A6Aut (Multiplicative.ofAdd (1 : ZMod 2)) = alphaOverS2844 := by
  apply S2882A6Aut_ne
  decide

/-- Multiplication law for the A6 sign action on X. -/
theorem S2882A6Aut_mul (g h : SignGroup) :
    S2882A6Aut (g * h) = S2882A6Aut h ≫ S2882A6Aut g := by
  by_cases hg : g = 1
  · subst g
    simp [S2882A6Aut]
  · by_cases hh : h = 1
    · subst h
      simp [S2882A6Aut]
    · have hgh : g * h = 1 := by
        have hg' : g = Multiplicative.ofAdd 1 := by
          rcases signGroup_cases g with h | h
          · exact absurd h hg
          · exact h
        have hh' : h = Multiplicative.ofAdd 1 := by
          rcases signGroup_cases h with h | h
          · exact absurd h hh
          · exact h
        rw [hg', hh']
        decide
      rw [hgh, S2882A6Aut_one, S2882A6Aut_ne hg, S2882A6Aut_ne hh]
      exact alphaOverS2844_square.symm

instance S2882A6PointSMul (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    SMul SignGroup (Opposite.unop U.as ⟶ X) where
  smul g P := P ≫ S2882A6Aut g

instance S2882A6PointMulAction (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    MulAction SignGroup (Opposite.unop U.as ⟶ X) where
  one_smul P := by
    change P ≫ S2882A6Aut 1 = P
    rw [S2882A6Aut_one, Category.comp_id]
  mul_smul g h P := by
    change P ≫ S2882A6Aut (g * h) = (P ≫ S2882A6Aut h) ≫ S2882A6Aut g
    rw [S2882A6Aut_mul, Category.assoc]

noncomputable def S2882A6PointwiseQuotient
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) : Cat :=
  Cat.of (ActionCategory SignGroup (Opposite.unop U.as ⟶ X))

noncomputable def S2882A6PrecompFunctor
    {U V : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ} (f : U ⟶ V) :
    S2882A6PointwiseQuotient U ⥤ S2882A6PointwiseQuotient V := by
  letI := S2882A6PointMulAction U
  letI := S2882A6PointMulAction V
  exact S1971ActionMap (M := SignGroup)
    (X := Opposite.unop U.as ⟶ X)
    (Y := Opposite.unop V.as ⟶ X)
    (fun P => f.as.unop ≫ P) (by
      intro g P
      change (f.as.unop ≫ P) ≫ S2882A6Aut g =
        f.as.unop ≫ (P ≫ S2882A6Aut g)
      rw [Category.assoc])

noncomputable def S2882A6PFunctor :
    (Iut.SchemeOverField K)ᵒᵖ ⥤ Cat where
  obj U := S2882A6PointwiseQuotient (LocallyDiscrete.mk U)
  map f := (S2882A6PrecompFunctor (Discrete.mk f)).toCatHom
  map_id U := rfl
  map_comp f g := rfl

noncomputable def S2882A6Q : Iut.EtaleStackPseudofunctor K :=
  S2882A6PFunctor.toPseudofunctor'

#check S2882A6Aut_mul
#check S2882A6PointwiseQuotient
#check S2882A6Q
#print axioms S2882A6Aut_mul

end LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
end
