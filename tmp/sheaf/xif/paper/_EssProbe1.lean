/-
Probe for _EssSurjPreimageIsoAgent: basic unfoldings and casts.
-/
import tmp.sheaf.xif.paper.S2519InvEquivalenceGoalActual
import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual
import tmp.sheaf.xif.paper.S1761DMStackSmallnessActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
open LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.EssSurjPreimageIsoAgent

/-- The identity-point base-change presentation of a cover. -/
noncomputable def S2519BC (X : OrbicurveFiniteEtaleCover S2482Orbicurve) :=
  X.finiteEtale.baseChange S2482AffineOver S2519BasePoint

lemma S2519PreimageCover_eq_S2517Obj (X : OrbicurveFiniteEtaleCover S2482Orbicurve) :
    S2519PreimageCover X = S2517Obj X := rfl

lemma S2519CScheme_preimage_eq (X : OrbicurveFiniteEtaleCover S2482Orbicurve) :
    S2517CScheme (S2519PreimageCover X) = (S2519BC X).pullbackScheme := by
  change Over.mk (Over.Hom.left (S2519BC X).projection ≫ Over.hom S2482AffineOver) =
    (S2519BC X).pullbackScheme
  rw [(S2519BC X).projection.w]
  rfl

#check S2519CScheme_preimage_eq

end LeanFormal.IUT.XiFPaper.EssSurjPreimageIsoAgent
end