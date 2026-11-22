import tmp.sheaf.xif.paper.S2252ConeTransportActual
import tmp.sheaf.xif.paper.S2151UnpastingActual
import tmp.sheaf.xif.paper.S2097BaseChangeButterflyActual

/-! # S2254: unpasting/lift API audit

Audit result: the tree has no inhabitant of the 2-categorical unpasting API.
The available statements are:

* `S2151UnpastingOfFull`: full `S1827EssSurjOf` of the two presentations
  gives the weak witness of `S2096VertexSquare` -- recorded as a Type with no
  inhabitant;
* `S2097RightCancelStatement`: reverse pasting -- recorded, not proved;
* `S2107CanonicalLiftTwoCell`: reduces right-cancel further, not proved.

Consequently no lift `W -> schemeRep (S2165Apex)` can be constructed from the
available API.  The exact missing input is recorded below; nothing is faked.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2254UnpastingLiftActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2151UnpastingActual
open LeanFormal.IUT.XiFPaper.S2252ConeTransportActual

universe u

/-- Exact first missing API for the step-(2) lift: the 2-categorical
unpasting statement of S2151. -/
def S2254UnpastingAPI : Type 1 :=
  S2151UnpastingOfFull

/-- Alternative exact missing bundle: reverse pasting plus the big-square full
property; S2097 reduces the butterfly to these. -/
structure S2254RightCancelInputs where
  rightCancel : S2097RightCancelStatement
  bigSquare : S2094BigSquareEssSurj

#check S2254UnpastingAPI
#check S2254RightCancelInputs
#check S2097RightCancelStatement
#check S2151UnpastingOfFull

end LeanFormal.IUT.XiFPaper.S2254UnpastingLiftActual

end
