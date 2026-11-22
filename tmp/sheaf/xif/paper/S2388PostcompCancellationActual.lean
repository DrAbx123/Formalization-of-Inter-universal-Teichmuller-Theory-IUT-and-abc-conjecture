import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2380PresentationCancellationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S2388PostcompCancellationActual

variable {F : Type} [Field F]
variable {S T U : SchemeOverField F}

/-- Scheme-level consequence needed to cancel postcomposition: a 2-isomorphism
after postcomposition by the representable map of g0 gives equality of the
underlying scheme maps.  This is the precise local lemma not supplied by
S1742. -/
def S2388HomEqOfIso (g0 : T ⟶ U) : Prop :=
  forall {a0 b0 : S ⟶ T},
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom a0)
        (S1742StrongTransOfHom g0))
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom b0)
        (S1742StrongTransOfHom g0)) ->
    a0 ≫ g0 = b0 ≫ g0

/-- Local postcomposition cancellation for representable maps. -/
def S2388PostcompRequired (g0 : T ⟶ U) : Type 1 :=
  forall {a0 b0 : S ⟶ T},
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom a0)
        (S1742StrongTransOfHom g0))
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom b0)
        (S1742StrongTransOfHom g0)) ->
    Iso (S1742StrongTransOfHom a0) (S1742StrongTransOfHom b0)

/-- If the scheme-level comparison is available and g0 is monic, local
postcomposition cancellation follows. -/
noncomputable def S2388Postcomp_of_homEq [Mono g0]
    (h : S2388HomEqOfIso (S := S) g0) :
    S2388PostcompRequired (S := S) g0 := by
  intro a0 b0 e
  have hg := h e
  have hab : a0 = b0 := (cancel_mono g0).mp hg
  exact eqToIso (congrArg S1742StrongTransOfHom hab)

end LeanFormal.IUT.XiFPaper.S2388PostcompCancellationActual
end