import tmp.sheaf.xif.paper.S2448ResidueFrobeniusAPI
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
namespace LeanFormal.IUT.XiFPaper.S2449ResidueAlgClosedAPI
variable (p : Nat) [Fact (Nat.Prime p)]
/-- Choice of a lift of a residue-field element to the valuation ring. -/
noncomputable def S2449LiftCoeff (c : PadicResidueField p) :
    PadicValuationSubring p :=
  Classical.choose (IsLocalRing.residue_surjective c)
theorem S2449LiftCoeff_spec (c : PadicResidueField p) :
    IsLocalRing.residue (PadicValuationSubring p) (S2449LiftCoeff p c) = c :=
  Classical.choose_spec (IsLocalRing.residue_surjective c)
/-- Coefficientwise lift of a residue-field polynomial to the valuation ring. -/
noncomputable def S2449LiftPoly (f : Polynomial (PadicResidueField p)) :
    Polynomial (PadicValuationSubring p) :=
  Polynomial.sum f fun n c =>
    Polynomial.C (S2449LiftCoeff p c) * Polynomial.X ^ n
#check S2449LiftCoeff
#check S2449LiftCoeff_spec
end LeanFormal.IUT.XiFPaper.S2449ResidueAlgClosedAPI
end
