import tmp.sheaf.xif.paper.S2388PostcompCancellationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2388PostcompCancellationActual
namespace LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual

variable {F : Type} [Field F]
variable {S T U : SchemeOverField F}

/-- Representable composition equation: the underlying scheme map of the
vertical composite of the two representable strong transformations is the
composite scheme map. -/
theorem S2398HomOfStrongTrans_vcomp
    (a0 : S ⟶ T) (g0 : T ⟶ U) :
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom a0)
        (S1742StrongTransOfHom g0)) = a0 ≫ g0 := by
  rw [← S1742HomOfStrongTrans_def]
  change (((S1742App g0 (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
    ((S1742App a0 (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S)))).as) = a0 ≫ g0
  rw [S1742App_obj, S1742App_obj]
  simp only [Discrete.mk_as, Category.id_comp, Category.comp_id]

/-- The scheme-level comparison needed for local postcomposition cancellation
follows from 2-isomorphism invariance of the underlying scheme map plus the
representable composition equation. -/
theorem S2398HomEqOfIso (g0 : T ⟶ U) :
    S2388HomEqOfIso (S := S) g0 := by
  intro a0 b0 e
  have h := S1742HomOfStrongTrans_congr e
  rw [S2398HomOfStrongTrans_vcomp, S2398HomOfStrongTrans_vcomp] at h
  exact h

/-- Local postcomposition cancellation for a representable monic map. -/
noncomputable def S2398PostcompRequired [Mono g0] :
    S2388PostcompRequired (S := S) g0 :=
  S2388Postcomp_of_homEq (S := S) (S2398HomEqOfIso g0)

end LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
end
