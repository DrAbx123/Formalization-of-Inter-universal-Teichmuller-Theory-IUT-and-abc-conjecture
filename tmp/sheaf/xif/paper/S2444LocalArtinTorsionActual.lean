import tmp.sheaf.xif.paper.S2116CommutatorClosedActual
import tmp.sheaf.xif.paper.S2048TransferCompatActual
import tmp.sheaf.xif.paper.S2113M2bTransferActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2116CommutatorClosedActual
open LeanFormal.IUT.XiFPaper.S2048TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2113M2bTransferActual
namespace LeanFormal.IUT.XiFPaper.S2444LocalArtinTorsionActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The exact missing width input for the M2c/local Artin torsion branch. -/
def S2444CommutatorWidthInputRequired : Prop :=
  CommutatorWidthInput (p := p)
/-- The actual canonical torsion comparison at every level, from the width input. -/
theorem S2444CanonicalTorsionComparison
    (h : CommutatorWidthInput (p := p)) (U : Index p) :
    canonicalTorsionComparison p U :=
  S2116CommutatorClosedActual.canonicalTorsionComparison_forall_of_widthInput
    (p := p) h U
/-- The actual local Artin torsion map, from the width input. -/
noncomputable def S2444LocalArtinTorsionMap
    (h : CommutatorWidthInput (p := p)) :
    LocalArtinTorsionMap p where
  artin U := (canonicalEquiv (p := p) U
    (S2444CanonicalTorsionComparison p h U)).symm
/-- Exact first missing: the commutator-width input. -/
theorem S2444LocalArtinTorsionMap_of_width
    (h : CommutatorWidthInput (p := p)) :
    Nonempty (LocalArtinTorsionMap p) :=
  ⟨S2444LocalArtinTorsionMap p h⟩
#check S2444CommutatorWidthInputRequired
#check S2444CanonicalTorsionComparison
#check S2444LocalArtinTorsionMap
#check S2444LocalArtinTorsionMap_of_width
end LeanFormal.IUT.XiFPaper.S2444LocalArtinTorsionActual
end
