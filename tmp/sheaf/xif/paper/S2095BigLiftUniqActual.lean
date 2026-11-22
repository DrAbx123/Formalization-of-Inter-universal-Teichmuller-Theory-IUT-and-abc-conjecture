import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual

/-! # S2095: lift uniqueness for the iso-comma witness

S1827EssSurjOf for the iso-comma square is exactly the statement that any
strong transformation into the square whose two projections are isomorphic to
those of a cone is isomorphic to the witness lift of that cone.  This is the
missing lift-uniqueness lemma for S2076Witness.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual

universe u

/-- Exact lift-uniqueness statement for the iso-comma square. -/
def S2095BigLiftUniq : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map
      (commutes f g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g)),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX) →
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY) →
    Nonempty (Iso h
      ((S2076Witness (f := f) (g := g)).lift W c))

/-- Lift uniqueness gives the full big-square essential surjectivity. -/
theorem S2095BigEssSurj_of_liftUniq
    (h : S2095BigLiftUniq) : S2094BigSquareEssSurj := by
  intro A B C f g
  exact h A B C f g

#print axioms S2095BigEssSurj_of_liftUniq

end LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual

end
