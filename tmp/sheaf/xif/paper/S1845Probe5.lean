import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1845AlgEndActual

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual

variable {F : Type} [Field F]
variable {W : EtaleStackPseudofunctor F} {S : SchemeOverField F}

theorem S1845NonemptyIsoOfAppEq
    {L L' : Pseudofunctor.StrongTrans W (S1742YS (F := F) S)}
    (h : ∀ a, L.app a = L'.app a) : Nonempty (L ≅ L') := by
  refine ⟨Pseudofunctor.StrongTrans.isoMk (fun a => eqToIso (h a)) ?_⟩
  intro a b f
  haveI : Subsingleton ((W.map f ≫ L.app b) ⟶ (L'.app a ≫ (S1742YS S).map f)) := by
    constructor
    intro alpha beta
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  exact Subsingleton.elim _ _

end LeanFormal.IUT.XiFPaper.S1845AlgEndActual
