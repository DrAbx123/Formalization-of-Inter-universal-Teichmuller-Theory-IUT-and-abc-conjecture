import tmp.sheaf.xif.paper.S2619ActionGroupoidFiberSkeleton

noncomputable section
open CategoryTheory
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2662D9StackGoalReductionActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton

universe u
variable (l : PrimeGeFive) (F : Type u) [CommRing F]

/-- Exact reduction of the S2619 prestack goal to the hom-presheaf sheaf
conditions. -/
theorem S2662PrestackGoal_iff
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}) :
    S2619PrestackGoal F fib ↔
      ∀ {S : Iut.SchemeOverField F}
        (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))),
        S2619PresheafHomSheafGoal F fib M N := by
  constructor
  · intro h S M N
    exact h.isSheaf M N
  · intro h
    exact ⟨fun {S} M N => h M N⟩

theorem S2662PrestackGoal_iff_isSheaf
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}) :
    S2619PrestackGoal F fib ↔
      ∀ {S : Iut.SchemeOverField F}
        (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))),
        Presheaf.IsSheaf
          ((Iut.SchemeOverField.etaleTopology F).over S)
          (fib.presheafHom M N) := by
  rw [S2662PrestackGoal_iff]
  rfl

#print axioms S2662PrestackGoal_iff
#print axioms S2662PrestackGoal_iff_isSheaf

end LeanFormal.IUT.XiFPaper.S2662D9StackGoalReductionActual
end