import tmp.sheaf.xif.paper.S2858Z2MapCompActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2865SMapFinActual
open Iut
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)

/-- inv 作为 1-morphism。 -/
noncomputable def invM : X.stack.fiber ⟶ X.stack.fiber := inv

/-- 用 Fin 2 表示的 sign map。 -/
def sMapFin (inv : X.Hom X) (i : Fin 2) : X.stack.fiber ⟶ X.stack.fiber :=
  if i = 0 then 𝟙 X.stack.fiber else invM X inv

def signGroupToFin (g : SignGroup) : Fin 2 :=
  ⟨g.toAdd.val, ZMod.val_lt g.toAdd⟩

def sMapZ (inv : X.Hom X) (g : SignGroup) : X.stack.fiber ⟶ X.stack.fiber :=
  sMapFin X inv (signGroupToFin g)

theorem sMapFin_zero : sMapFin X inv (0 : Fin 2) = 𝟙 X.stack.fiber := by
  simp [sMapFin]

theorem sMapFin_one : sMapFin X inv (1 : Fin 2) = invM X inv := by
  simp [sMapFin]

theorem signGroupToFin_one : signGroupToFin (1 : SignGroup) = 0 := by
  apply Fin.ext
  simp [signGroupToFin]

theorem signGroupToFin_gen :
    signGroupToFin (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  apply Fin.ext
  simp [signGroupToFin]
  decide

theorem sMapZ_one : sMapZ X inv 1 = 𝟙 X.stack.fiber := by
  simp [sMapZ, signGroupToFin_one, sMapFin_zero]

theorem sMapZ_gen :
    sMapZ X inv (Multiplicative.ofAdd (1 : ZMod 2)) = invM X inv := by
  simp [sMapZ, signGroupToFin_gen, sMapFin_one]

#check sMapFin
#check sMapZ_one
#check sMapZ_gen
#print axioms sMapZ_one
#print axioms sMapZ_gen
end LeanFormal.IUT.XiFPaper.S2865SMapFinActual
