import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S3119StrongTransEqActual
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.RepresentableEtaleCoverCategoryAttempt

variable {F : Type} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- A finite-etale cover whose source fiber is a representable etale stack. -/
def RepresentableFiniteEtaleCover : Type 1 :=
  { cover : OrbicurveFiniteEtaleCover X //
    exists S : SchemeOverField F,
      cover.source.fiber = schemeRepresentableEtalePseudofunctor F S }

/-- Between representable fiber pseudofunctors, a 2-isomorphism is equivalent
to equality of underlying scheme morphisms. -/
theorem S1742IsoIffHomEq
    {S T : SchemeOverField F}
    (eta theta : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S) (S1742YS (F := F) T)) :
    Nonempty (eta ≅ theta) <->
      S1742HomOfStrongTrans (F := F) eta =
        S1742HomOfStrongTrans (F := F) theta := by
  constructor
  · rintro ⟨e⟩
    exact S1742HomOfStrongTrans_congr (F := F) e
  · intro h
    refine ⟨(S1742StrongTransIsoOfHom (F := F) eta).symm.trans ?_⟩
    refine (eqToIso ?_).trans (S1742StrongTransIsoOfHom (F := F) theta)
    rw [h]


/-- On representable fibers, every inhabited 2-isomorphism class is a
singleton: 2-isomorphic strong transformations are equal. -/
theorem S3126IsoEq
    {S T : SchemeOverField F}
    (eta theta : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S) (S1742YS (F := F) T))
    (h : Nonempty (eta ≅ theta)) : eta = theta := by
  rcases h with ⟨e⟩
  exact S3119StrongTrans_eq_of_hom_eq F eta theta
    (S1742HomOfStrongTrans_congr (F := F) e)


/-- Target: a raw category on representable covers. -/
def S3126RepresentableRawCategoryTarget : Prop :=
  Nonempty (Category.{1, 1} (RepresentableFiniteEtaleCover (F := F) (X := X)))

#check RepresentableFiniteEtaleCover
#check S1742IsoIffHomEq
#check S3126IsoEq
#check S3126RepresentableRawCategoryTarget

end LeanFormal.IUT.XiFPaper.RepresentableEtaleCoverCategoryAttempt
end