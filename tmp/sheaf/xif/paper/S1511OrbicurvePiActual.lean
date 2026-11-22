import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

-- S1511: actual nonterminal orbicurve X from S1419; exact first
-- missing field is the certified OrbicurveFundamentalGroupData over the
-- absolute Galois group.  The l-torsion sequence is NOT used as Pi.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1511OrbicurvePiActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

universe u

variable (l : PrimeGeFive)

/-- The actual S1419 nonterminal hyperbolic orbicurve. -/
noncomputable abbrev S1511Orbicurve : Iut.HyperbolicOrbicurve (S1348K l) :=
  S1419Orbicurve l

/-- The absolute Galois group. -/
abbrev S1511Galois : ProfiniteGrp := Iut.AbsoluteGaloisProfinite (S1348K l)

/-- Exact first missing field: certified orbifold fundamental-group data. -/
abbrev S1511OrbicurvePiExactFirstField : Type 1 :=
  Iut.OrbicurveFundamentalGroupData (S1511Orbicurve (l := l))
    (S1511Galois (l := l))

/-- Actual non-group prefix: nonterminal, once-punctured signature. -/
theorem S1511Orbicurve_signature :
    (S1511Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1419Orbicurve_signature l

theorem S1511Orbicurve_nonterminal :
    S1319NonterminalFiber (S1511Orbicurve (l := l)) :=
  S1419NonterminalFiber l

/-- Conditional actual first field: with certified group data, the S1348 D6
first missing field is obtained. -/
noncomputable def S1511FirstFieldOfGroups
    (groups : S1511OrbicurvePiExactFirstField (l := l)) :
    S1348D6FirstMissingField l :=
  S1419D6FirstMissingFieldOfGroups l groups

/-- No inhabitant of the group data is asserted. -/
def S1511GroupDataRequired : Type 1 := S1511OrbicurvePiExactFirstField (l := l)

#check S1511Orbicurve
#check S1511Galois
#check S1511OrbicurvePiExactFirstField
#check S1511Orbicurve_signature
#check S1511Orbicurve_nonterminal
#check S1511FirstFieldOfGroups
#check S1511GroupDataRequired

end LeanFormal.IUT.XiFPaper.S1511OrbicurvePiActual

end