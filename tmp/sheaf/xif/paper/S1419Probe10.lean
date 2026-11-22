import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe10

universe v u

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type v) (Y : C)

example (a : (discretePseudo P).obj (LocallyDiscrete.mk (Opposite.op Y))) : True := by
  let b := a
  #check a
  #check a.as
  #check (a ⟶ b)
  #check (Discrete.instSubsingletonDiscreteHom a b)
  trivial

end S1419Probe10

end
