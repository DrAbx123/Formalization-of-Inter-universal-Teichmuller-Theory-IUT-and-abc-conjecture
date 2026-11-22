
import Mathlib.CategoryTheory.Sites.Descent.DescentData

noncomputable section
open CategoryTheory Opposite Bicategory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace ProbeBase
universe v u v' u'

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {S : C}

example (D : F.DescentData (fun (_ : Unit) => (𝟙 S : S ⟶ S))) :
    ((F.toDescentData (fun (_ : Unit) => (𝟙 S : S ⟶ S))).obj (D.obj ())) ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (fun i => ?_) ?_
  · obtain rfl : i = () := Subsingleton.elim i ()
    exact (Cat.Hom.toNatIso (F.mapId (.mk (op S)))).app (D.obj ())
  · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
    have h₁ : f₁ = q := by simpa using hf₁
    have h₂ : f₂ = q := by simpa using hf₂
    subst h₁
    subst h₂
    simp [Pseudofunctor.DescentData.hom_self]

end ProbeBase