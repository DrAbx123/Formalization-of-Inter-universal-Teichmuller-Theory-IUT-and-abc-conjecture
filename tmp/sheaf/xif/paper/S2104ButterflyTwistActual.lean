import tmp.sheaf.xif.paper.S2099BigSquareEssSurjActual
import tmp.sheaf.xif.paper.S2095DirectStructureMapActual

/-! # S2104: canonical twist in the actual butterfly configuration

S2099SiteFirstMissing asks the twist for *arbitrary* h and projection isos;
this is not implied by the weak witness.  But for the actual butterfly lift
used in S2095 path B, h is the witness lift and the two projection isos are
the witness comparisons, so the twist is the canonical one already proved in
S2099TwistAt_canonical.  This file records that actual compatibility datum.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2095DirectStructureMapActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual

universe u

/-- The canonical twist holds for the actual butterfly cone and its S2076
lift/comparisons. -/
theorem S2104ToBButterflyCanonicalTwist {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (x : ↑((schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme).obj U)) :
    S2099TwistAt f g (S2095ToBCone f g T ptB Pf)
      ((S2076Witness (f := f) (g := g)).lift
        (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
        (S2095ToBCone f g T ptB Pf))
      ((S2076Witness (f := f) (g := g)).liftToX
        (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
        (S2095ToBCone f g T ptB Pf))
      ((S2076Witness (f := f) (g := g)).liftToY
        (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
        (S2095ToBCone f g T ptB Pf)) U x :=
  S2099TwistAt_canonical f g (S2095ToBCone f g T ptB Pf) U x

#print axioms S2104ToBButterflyCanonicalTwist

end LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual

end
