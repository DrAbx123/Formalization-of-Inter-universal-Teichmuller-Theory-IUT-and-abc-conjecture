import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

namespace ProbeS1914i

universe u v

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

example {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f] : Mono f.hom := by
  have h : Mono (P.ι.map f) := by
    simpa using (inferInstance : Mono f)
  exact Functor.mono_of_mono_map P.ι h

end ProbeS1914i
