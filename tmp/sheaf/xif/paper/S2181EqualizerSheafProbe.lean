import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TestEqualizerSheaf

theorem isSheaf_equalizer {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {P R : Cᵒᵖ ⥤ Type v} (hP : Presheaf.IsSheaf J P) (hR : Presheaf.IsSheaf J R)
    (f g : P ⟶ R) : Presheaf.IsSheaf J (Limits.equalizer f g) := by
  let F : WalkingParallelPair ⥤ (Cᵒᵖ ⥤ Type v) := Limits.parallelPair f g
  have hF : ∀ j : WalkingParallelPair, Presheaf.IsSheaf J (F.obj j) := by
    intro j
    cases j with
    | zero => exact hP
    | one => exact hR
  have hlim := ObjectProperty.prop_limit (P := Presheaf.IsSheaf J) F hF
  simpa [Limits.equalizer] using hlim

end TestEqualizerSheaf
