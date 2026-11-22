import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
/-! # S789: mu_{2l} automorphisms of the root-stack section carrier
Left multiplication by zeta on the extension unit is NOT a MulEquiv automorphism
unless zeta=1.  The actual MulAut action is conjugation by zeta; the paper's
left multiplication action is only an Equiv/MulAction, and this exact mismatch
is recorded. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S789StackMuActionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Exact obstruction: left multiplication by a nontrivial zeta is not a
MulAut automorphism. -/
theorem leftMul_not_mulAut
    (ζ : rootsOfUnity (2 * l.value) (rootStackExtension T b)) (hζ : ζ ≠ 1) :
    ¬ ∃ F : MulAut (StackSectionCarrier T b),
      ∀ u : StackSectionCarrier T b, F u = ((ζ : (rootStackExtension T b)ˣ) * u.1, u.2) := by
  rintro ⟨F, hF⟩
  have h1 := hF (1 : StackSectionCarrier T b)
  have hone : F 1 = 1 := map_one F
  rw [hone] at h1
  have hζ' : (ζ : (rootStackExtension T b)ˣ) = 1 := by
    simpa using (congrArg Prod.fst h1).symm
  exact hζ (Subtype.ext hζ')
end LeanFormal.IUT.XiFPaper.S789StackMuActionActual
