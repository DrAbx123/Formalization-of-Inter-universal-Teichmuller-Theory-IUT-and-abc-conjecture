import tmp.sheaf.xif.paper.Mzk1G1FermatProjClosedSubscheme4Actual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProperFinal2Actual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubscheme4Actual
/-- Final properness of the Fermat curve immersion. -/
theorem fermatCurve_proper (n : Nat) :
    IsProper (fermatCurveImmersion n) :=
  fermatCurveImmersion_isProper n
/-- The Fermat curve closed immersion is closed. -/
theorem fermatCurve_closedImmersion (n : Nat) :
    IsClosedImmersion (fermatCurveImmersion n) :=
  fermatCurveImmersion_isClosedImmersion n
#print axioms fermatCurve_proper
#print axioms fermatCurve_closedImmersion
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProperFinal2Actual
end