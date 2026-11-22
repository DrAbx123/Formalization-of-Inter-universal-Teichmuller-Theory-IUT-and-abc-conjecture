import tmp.sheaf.xif.paper.S2662D9StackGoalReductionActual
import tmp.sheaf.xif.paper.S2663D9IsStackReductionActual
import tmp.sheaf.xif.paper.S2665TorsorSheafActual

noncomputable section
open CategoryTheory
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2668D9ReductionActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2662D9StackGoalReductionActual
open LeanFormal.IUT.XiFPaper.S2663D9IsStackReductionActual

universe u
variable {l : PrimeGeFive} {F : Type u} [CommRing F]
variable (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u})

/-- Exact D9 reduction: IsStack = hom-presheaf sheaf conditions + effectivity
(EssSurj) for every covering sieve. -/
theorem S2668D9IsStack_iff :
    fib.IsStack (Iut.SchemeOverField.etaleTopology F) ↔
      (∀ {S : Iut.SchemeOverField F}
        (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))),
        Presheaf.IsSheaf
          ((Iut.SchemeOverField.etaleTopology F).over S)
          (fib.presheafHom M N)) ∧
      (∀ {S : Iut.SchemeOverField F} (R : Sieve S)
        (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
        (fib.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj) := by
  rw [S2663IsStack_iff]
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨(S2662PrestackGoal_iff_isSheaf F fib).mp hp, he⟩
  · rintro ⟨hsheaf, he⟩
    exact ⟨(S2662PrestackGoal_iff_isSheaf F fib).mpr hsheaf, he⟩

#check S2668D9IsStack_iff
#print axioms S2668D9IsStack_iff
end LeanFormal.IUT.XiFPaper.S2668D9ReductionActual
end
