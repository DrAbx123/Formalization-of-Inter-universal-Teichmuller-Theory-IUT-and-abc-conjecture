import tmp.sheaf.xif.paper.S1932BuildB2

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open scoped CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

/-! ## 4. The pseudofunctor of the sign action -/

/-- The two nontrivial elements of the sign group are distinct. -/
theorem S1932SignGroup_generator_ne :
    (Multiplicative.ofAdd (1 : ZMod 2) : SignGroup) ≠ 1 := by
  decide

/-- Every element of the sign group has square one. -/
theorem S1932SignGroup_mul_self (x : SignGroup) : x * x = (1 : SignGroup) := by
  revert x
  decide

/-- The product of the two nontrivial elements of the sign group is the
identity. -/
theorem S1932SignGroup_mul_eq_one {x y : SignGroup} (hx : x ≠ (1 : SignGroup)) (hy : y ≠ (1 : SignGroup)) :
    x * y = (1 : SignGroup) := by
  revert x y
  decide

/-- The value of the sign diagram on a group element: the identity or the
actual elliptic involution. -/
noncomputable def S1932SigMapOf (x : SignGroup) : S1898Stack ⟶ S1898Stack :=
  if h : x = 1 then 𝟙 S1898Stack else S1932Sigma

theorem S1932SigMapOf_one : S1932SigMapOf 1 = 𝟙 S1898Stack := dif_pos rfl

theorem S1932SigMapOf_ne {x : SignGroup} (h : x ≠ (1 : SignGroup)) :
    S1932SigMapOf x = S1932Sigma := dif_neg h

theorem S1932SigMapOf_congr {x y : SignGroup} (h : x = y) :
    S1932SigMapOf x = S1932SigMapOf y := by rw [h]

/-- The value of the sign diagram on a morphism of the index groupoid. -/
noncomputable def S1932SigMap {a b : SignActionIndex} (f : a ⟶ b) :
    S1898Stack ⟶ S1898Stack :=
  S1932SigMapOf f.as

theorem S1932SigMap_as {a b : SignActionIndex} (f : a ⟶ b) :
    S1932SigMap f = S1932SigMapOf (f.as : SignGroup) := rfl

theorem S1932SigMap_of_eq {a b : SignActionIndex} {f : a ⟶ b}
    (h : (f.as : SignGroup) = (1 : SignGroup)) : S1932SigMap f = 𝟙 S1898Stack := dif_pos h

theorem S1932SigMap_of_ne {a b : SignActionIndex} {f : a ⟶ b}
    (h : (f.as : SignGroup) ≠ (1 : SignGroup)) : S1932SigMap f = S1932Sigma := dif_neg h

theorem S1932SigMap_id (a : SignActionIndex) : S1932SigMap (𝟙 a) = 𝟙 S1898Stack := by
  apply S1932SigMap_of_eq
  rfl

theorem S1932SigMap_comp_as {a b c : SignActionIndex} (f : a ⟶ b) (g : b ⟶ c) :
    ((f ≫ g).as : SignGroup) = (f.as : SignGroup) * (g.as : SignGroup) := by
  rw [LocallyDiscrete.comp_as]
  rfl

theorem S1932SigMap_comp_one_left {a b c : SignActionIndex} (f : a ⟶ b) (g : b ⟶ c)
    (hf : (f.as : SignGroup) = (1 : SignGroup)) : S1932SigMap (f ≫ g) = S1932SigMap g := by
  rw [S1932SigMap_as, S1932SigMap_as]
  apply S1932SigMapOf_congr
  rw [S1932SigMap_comp_as, hf]
  exact one_mul (g.as : SignGroup)

theorem S1932SigMap_comp_one_right {a b c : SignActionIndex} (f : a ⟶ b) (g : b ⟶ c)
    (hg : (g.as : SignGroup) = (1 : SignGroup)) : S1932SigMap (f ≫ g) = S1932SigMap f := by
  rw [S1932SigMap_as, S1932SigMap_as]
  apply S1932SigMapOf_congr
  rw [S1932SigMap_comp_as, hg]
  exact mul_one (f.as : SignGroup)

theorem S1932SigMap_comp_ne {a b c : SignActionIndex} (f : a ⟶ b) (g : b ⟶ c)
    (hf : (f.as : SignGroup) ≠ (1 : SignGroup)) (hg : (g.as : SignGroup) ≠ (1 : SignGroup)) :
    S1932SigMap (f ≫ g) = 𝟙 S1898Stack := by
  rw [S1932SigMap_as, ← S1932SigMapOf_one]
  apply S1932SigMapOf_congr
  rw [S1932SigMap_comp_as, S1932SignGroup_mul_eq_one hf hg]

/-- The coherence 2-cell of the sign diagram on composable arrows. -/
noncomputable def S1932SigMap_mapComp {a b c : SignActionIndex} (f : a ⟶ b) (g : b ⟶ c) :
    S1932SigMap (f ≫ g) ≅ S1932SigMap f ≫ S1932SigMap g := by
  by_cases hf : (f.as : SignGroup) = (1 : SignGroup)
  · by_cases hg : (g.as : SignGroup) = (1 : SignGroup)
    · rw [S1932SigMap_comp_one_left f g hf, S1932SigMap_of_eq hf, S1932SigMap_of_eq hg]
      exact (λ_ (𝟙 S1898Stack)).symm
    · rw [S1932SigMap_comp_one_left f g hf, S1932SigMap_of_eq hf, S1932SigMap_of_ne hg]
      exact (λ_ S1932Sigma).symm
  · by_cases hg : (g.as : SignGroup) = (1 : SignGroup)
    · rw [S1932SigMap_comp_one_right f g hg, S1932SigMap_of_ne hf, S1932SigMap_of_eq hg]
      exact (ρ_ S1932Sigma).symm
    · rw [S1932SigMap_comp_ne f g hf hg, S1932SigMap_of_ne hf, S1932SigMap_of_ne hg]
      exact S1932SigmaSqIso.symm
/-- **The pseudofunctor of the sign action on the actual S1726 stack.**  Its
value on the generator is the actual elliptic involution. -/
noncomputable def S1932Diagram :
    SignActionIndex ⥤ᵖ Iut.EtaleStackPseudofunctor S1726K where
  obj := fun _ => S1898Stack
  map := fun {a b} f => S1932SigMap f
  map₂ := fun {a b} {f g} η => eqToHom (congrArg S1932SigMap (LocallyDiscrete.eq_of_hom η))
  map₂_id := fun f => (S1932StrongTransSubsingleton _ _).elim _ _
  map₂_comp := fun η θ => (S1932StrongTransSubsingleton _ _).elim _ _
  mapId := fun a => eqToIso (S1932SigMap_id a)
  mapComp := fun f g => S1932SigMap_mapComp f g
  map₂_whisker_left := fun f g h η => (S1932StrongTransSubsingleton _ _).elim _ _
  map₂_whisker_right := fun η h => (S1932StrongTransSubsingleton _ _).elim _ _
  map₂_associator := fun f g h => (S1932StrongTransSubsingleton _ _).elim _ _
  map₂_left_unitor := fun f => (S1932StrongTransSubsingleton _ _).elim _ _
  map₂_right_unitor := fun f => (S1932StrongTransSubsingleton _ _).elim _ _

theorem S1932SigMap_generator : S1932SigMap signActionGenerator = S1932Sigma :=
  S1932SigMap_of_ne S1932SignGroup_generator_ne

example : S1932Diagram.obj signActionObject = S1898Stack := rfl

example : (S1932Diagram.map signActionGenerator : S1898Stack ⟶ S1898Stack) = S1932Sigma :=
  S1932SigMap_generator

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
