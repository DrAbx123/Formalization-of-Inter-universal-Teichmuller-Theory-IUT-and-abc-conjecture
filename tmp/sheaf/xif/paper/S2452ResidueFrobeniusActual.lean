import tmp.sheaf.xif.paper.S2451ResidueCharPActual
import tmp.sheaf.xif.paper.S2448ResidueFrobeniusAPI
import Mathlib.FieldTheory.Perfect
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
open LeanFormal.IUT.XiFPaper.S2448ResidueFrobeniusAPI
namespace LeanFormal.IUT.XiFPaper.S2452ResidueFrobeniusActual
variable (p : Nat) [Fact (Nat.Prime p)]
local instance S2452CharP : CharP (PadicResidueField p) p :=
  LeanFormal.IUT.XiFPaper.S2451ResidueCharPActual.S2451_residue_charP p
local instance S2452AlgClosed : IsAlgClosed (PadicResidueField p) :=
  LeanFormal.IUT.XiFPaper.S2450ResidueIsAlgClosedActual.S2450_residue_isAlgClosed p
/-- The Frobenius ring automorphism x |-> x^p of the residue field. -/
noncomputable def S2452FrobeniusAut : RingAut (PadicResidueField p) :=
  frobeniusEquiv (PadicResidueField p) p
theorem S2452FrobeniusAut_apply (x : PadicResidueField p) :
    S2452FrobeniusAut p x = x ^ p := by
  simp [S2452FrobeniusAut, frobeniusEquiv, frobenius]
/-- The corrected S2448 Frobenius data, now actual. -/
noncomputable def S2452FrobeniusData : S2448FrobeniusData p where
  frob := S2452FrobeniusAut p
  frob_apply := S2452FrobeniusAut_apply p
#check S2452FrobeniusAut
#check S2452FrobeniusAut_apply
#check S2452FrobeniusData
end LeanFormal.IUT.XiFPaper.S2452ResidueFrobeniusActual
end
