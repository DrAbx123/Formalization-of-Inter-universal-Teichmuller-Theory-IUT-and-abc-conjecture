import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Data.Bool.Basic

noncomputable section
open CategoryTheory
universe v u

namespace LeanFormal.IUT.XiFPaper.S2501StrictifiedFiberActual

/-- The strictified fiber is C x Bool. -/
abbrev S2501StrictFiber (C : Type u) [Category.{v} C] :=
  C × Discrete Bool

/-- The swap functor on the Bool factor. -/
def S2501BoolSwap : Discrete Bool ⥤ Discrete Bool :=
  Discrete.functor (fun b => Discrete.mk (!b))

/-- The strictified sign endofunctor: swap the Bool factor, leave C fixed. -/
def S2501Sigma (C : Type u) [Category.{v} C] :
    S2501StrictFiber C ⥤ S2501StrictFiber C where
  obj p := (p.1, S2501BoolSwap.obj p.2)
  map f := (f.1, S2501BoolSwap.map f.2)

/-- The strictified endofunctor squares to the identity. -/
theorem S2501Sigma_sq (C : Type u) [Category.{v} C] :
    S2501Sigma C ⋙ S2501Sigma C = 𝟭 (S2501StrictFiber C) := by
  apply Functor.ext
  case h_obj =>
    rintro ⟨x, ⟨b⟩⟩
    cases b <;> rfl
  case h_map =>
    rintro ⟨x, ⟨b⟩⟩ ⟨y, ⟨c⟩⟩ ⟨f, g⟩
    cases b <;> cases c <;> ext
    all_goals dsimp [S2501Sigma, S2501BoolSwap]
    all_goals try apply Subsingleton.elim
    all_goals simp only [eqToHom_fst]
    all_goals convert eq_conj_eqToHom f using 2 <;> rfl

#check S2501Sigma_sq

end LeanFormal.IUT.XiFPaper.S2501StrictifiedFiberActual
end
