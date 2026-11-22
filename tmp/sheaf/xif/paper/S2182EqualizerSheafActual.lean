import tmp.sheaf.xif.paper.S2168QHomSheafEqualizerActual
import Mathlib.CategoryTheory.Sites.Limits

noncomputable section
open CategoryTheory Opposite Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual

universe v

/-- The pointwise equalizer of two morphisms of sheaves of types is a sheaf. -/
theorem s2168EqualizerSheafLemma_holds (C : Type 1) [Category.{v} C]
    (J : GrothendieckTopology C) : S2168EqualizerSheafLemma C J := by
  intro P R hP hR f g
  let F : WalkingParallelPair ⥤ (Cᵒᵖ ⥤ Type) := Limits.parallelPair f g
  have hF : ∀ j : WalkingParallelPair, Presheaf.IsSheaf J (F.obj j) := by
    intro j
    cases j with
    | zero => exact hP
    | one => exact hR
  have hlim := ObjectProperty.prop_limit (P := Presheaf.IsSheaf J) F hF
  simpa [Limits.equalizer] using hlim

#print axioms s2168EqualizerSheafLemma_holds

end LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual
