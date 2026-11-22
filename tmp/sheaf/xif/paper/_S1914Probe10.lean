import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

namespace ProbeS1914j

universe u v

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

#check Functor.map_mono
#check Functor.mono_of_mono_map

example : P.ι.PreservesMonomorphisms := inferInstance
example : P.ι.ReflectsMonomorphisms := inferInstance

example {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f] : Mono (P.ι.map f) :=
  Functor.map_mono P.ι f

example {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f] : Mono f.hom := by
  have h : Mono (P.ι.map f) := Functor.map_mono P.ι f
  simpa using h

end ProbeS1914j
