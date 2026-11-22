import tmp.sheaf.xif.paper.S2121ChoiceFreeLowerWitnessActual
import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

/-! # S2128: concrete S1850Doubled probe for the two D6 inputs

Instantiates S2094BigSquareEssSurj and S2121ComparisonTwist on the
S1850Doubled cover with the identity cover map.  No counterexample is
asserted here; the file records the concrete data and checks the instances.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2128DoubledProbeActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2121ChoiceFreeLowerWitnessActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

universe u

abbrev S2128A : S1728Cover := S1850DoubledCover
abbrev S2128T : SchemeOverField S1726K := S1850T
abbrev S2128Pt : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K S2128T) S2128A.source.fiber :=
  S1733BasePoint
abbrev S2128F : S1728CoverMap S2128A S2128A := S1641CoverMapId S2128A
abbrev S2128G : S1728CoverMap S2128A S2128A := S1641CoverMapId S2128A

/-- The concrete presentation of the identity cover map on the doubled cover. -/
def S2128Pg : EtaleStackBaseChangePresentation S2128G.map S2128T
    (S2086PointC S2128F S2128Pt) :=
  S1850Doubled S2128T S2128Pt

#check S2121ComparisonTwist S2128F S2128G S2128T S2128Pt S2128Pg
#check S2094BigSquareEssSurj
#print axioms S2128Pg
#print axioms S2128F

end LeanFormal.IUT.XiFPaper.S2128DoubledProbeActual

end
