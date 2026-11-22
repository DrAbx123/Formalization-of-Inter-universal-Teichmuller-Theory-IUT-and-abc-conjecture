import tmp.sheaf.xif.paper.S2444LocalArtinTorsionActual
import tmp.sheaf.xif.paper.S2117TopFGActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2116CommutatorClosedActual
open LeanFormal.IUT.XiFPaper.S2117TopFGActual
open LeanFormal.IUT.XiFPaper.S2048TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2444LocalArtinTorsionActual
namespace LeanFormal.IUT.XiFPaper.S2445M2cExactMissingActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- Exact missing input 1: finite generation of the absolute Galois group of Q_p. -/
def S2445PadicFGRequired : Prop :=
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated (p := p)
/-- Exact missing input 2: Nikolov-Segal bounded commutator width. -/
def S2445NikolovSegalRequired : Prop :=
  NikolovSegalCommutatorWidth.{0}
/-- The two deep inputs give the S2116 width input. -/
theorem S2445CommutatorWidthInput_of_inputs
    (hNS : S2445NikolovSegalRequired)
    (hQp : S2445PadicFGRequired (p := p)) :
    CommutatorWidthInput (p := p) := by
  intro U
  exact commutatorWidthBounded_of_nikolovSegal hNS U
    (topologicallyFinitelyGenerated_forall (p := p) hQp U)
/-- The two deep inputs give canonicalTorsionComparison at every level. -/
theorem S2445CanonicalTorsionComparison_of_inputs
    (hNS : S2445NikolovSegalRequired)
    (hQp : S2445PadicFGRequired (p := p)) (U : Index p) :
    S2027LocalArtinActual.canonicalTorsionComparison p U :=
  S2444CanonicalTorsionComparison p
    (S2445CommutatorWidthInput_of_inputs p hNS hQp) U
/-- The two deep inputs give the actual local Artin torsion map. -/
noncomputable def S2445LocalArtinTorsionMap_of_inputs
    (hNS : S2445NikolovSegalRequired)
    (hQp : S2445PadicFGRequired (p := p)) :
    LocalArtinTorsionMap p :=
  S2444LocalArtinTorsionMap p
    (S2445CommutatorWidthInput_of_inputs p hNS hQp)
#check S2445PadicFGRequired
#check S2445NikolovSegalRequired
#check S2445CommutatorWidthInput_of_inputs
#check S2445CanonicalTorsionComparison_of_inputs
#check S2445LocalArtinTorsionMap_of_inputs
end LeanFormal.IUT.XiFPaper.S2445M2cExactMissingActual
end
