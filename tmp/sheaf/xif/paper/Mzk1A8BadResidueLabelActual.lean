import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.NativeSourceReductionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A8BadResidueLabelActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual residue-characteristic signed label of a bad place.  This is a total
function from the actual bad set; it is NOT asserted to be the paper theta
label. -/
noncomputable def badResidueSignedLabel (b : Bad (nativePlaceSelection T)) :
    SignedLabel l.value :=
  SignedLabel.representative l
    ((badResidueLabel (nativePlaceSelection T) b : Nat) : ZMod l.value)

theorem badResidueSignedLabel_apply (b : Bad (nativePlaceSelection T)) :
    badResidueSignedLabel T b =
      SignedLabel.representative l
        ((badResidueLabel (nativePlaceSelection T) b : Nat) : ZMod l.value) := rfl

/-- The residue label is the actual residue characteristic of the bad place. -/
theorem badResidueSignedLabel_nat (b : Bad (nativePlaceSelection T)) :
    badResidueLabel (nativePlaceSelection T) b =
      NumberFieldFinitePlace.residueCharacteristic b.1 := rfl

#print axioms badResidueSignedLabel_nat
end LeanFormal.IUT.XiFPaper.Mzk1A8BadResidueLabelActual