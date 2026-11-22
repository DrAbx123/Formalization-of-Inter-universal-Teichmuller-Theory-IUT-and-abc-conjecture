import tmp.sheaf.xif.paper.S2539FaithfulActual
import tmp.sheaf.xif.paper.S2534CoverHomMapActual
import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2534CoverHomMapActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2540FullGoalActual

/-- Exact missing full-lift: every map between inverse objects is the quotient
map of a map of affine covers. -/
def S2540FullLift : Prop :=
  ∀ {C D : FiniteEtaleCover S2482AffineScheme}
    (h : Iut.OrbicurveFiniteEtaleCoverMap (S2517InvObj C) (S2517InvObj D)),
    ∃ f : C ⟶ D, S1728CoverMapRel (S2518InvCoverMap f) h

theorem S2540Full_of_lift (h : S2540FullLift) :
    ∀ {C D : FiniteEtaleCover S2482AffineScheme},
      Function.Surjective (fun f : C ⟶ D => S2519InvFunctor.map f) := by
  intro C D y
  refine Quot.inductionOn y ?_
  intro h0
  rcases h (C := C) (D := D) h0 with ⟨f, hf⟩
  exact ⟨f, Quot.sound hf⟩

#check S2540Full_of_lift
#print axioms S2540Full_of_lift
end LeanFormal.IUT.XiFPaper.S2540FullGoalActual
end