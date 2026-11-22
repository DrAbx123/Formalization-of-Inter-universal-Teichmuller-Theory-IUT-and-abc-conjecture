import tmp.sheaf.xif.paper.S879RootStackNormFormulaInputsActual
import tmp.sheaf.xif.paper.S861RootCharacterNormComparisonActual

/-! # S887: additive-Haar/determinant route via S861 on E and L

The determinant `det(lsmul L L E u) = u^dStack` is actual in S870/S879.
To convert it into `dHC_E(algebraMap u) = dHC_L(u)^dStack` we use the
character/norm comparison on the fields E and L (S861's formula):

* E: log dHC_E(lam) = dQpFactor * log ||lam||_E;
* L: log dHC_L(u) = nL * log ||u||_L;
* norm extension: ||algebraMap u||_E = ||u||_L;
* determinant/degree: dQpFactor = nL * dStack.

The exact minimal new input is the E-instance of S861, recorded below.  No
fake analytic formula is asserted.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S866RootStackCharacterNormLiftActual
open LeanFormal.IUT.XiFPaper.S870RootStackRestrictionBridgeActual
open LeanFormal.IUT.XiFPaper.S879RootStackNormFormulaInputsActual
open LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- S861 analogue on E = rootStackExtension: log dHC_E = n * log norm. -/
def RootStackCharacterNormComparisonAt (n : Nat) : Prop :=
  ∀ lam : (rootStackExtension T b)ˣ,
    Real.log (distribHaarChar (rootStackExtension T b) lam : Real) =
      (n : Real) * Real.log ‖(lam : rootStackExtension T b)‖

/-- The only new analytic input: the E-instance at n = dQpFactor. -/
def RootStackCharacterNormComparisonAtDQp : Prop :=
  RootStackCharacterNormComparisonAt (l := l) T b (dQpFactor (l := l) T b)

/-- Exact norm-extension input, repeated from S879. -/
def RootStackNormExtensionFormula : Prop :=
  ∀ u : (rootNormedExtension T b)ˣ,
    ‖(rootStackAlgebraMapUnits (l := l) T b u : rootStackExtension T b)‖ =
      ‖(u : rootNormedExtension T b)‖

/-- Positive reduction: S861 on E + S861 on L + norm extension + determinant
degree identity imply S866's restriction bridge. -/
theorem rootStackHaarCharRestrictionBridge_of_S861E_S861L_norm
    (nL : Nat)
    (hn : nL = dK (l := l) T b * dLK (l := l) T b)
    (hE : RootStackCharacterNormComparisonAtDQp (l := l) T b)
    (hL : RootNormedCharacterNormComparison (l := l) T b nL)
    (hnorm : RootStackNormExtensionFormula (l := l) T b) :
    RootStackHaarCharRestrictionBridge (l := l) T b 0 := by
  intro u
  let lam : (rootStackExtension T b)ˣ := rootStackAlgebraMapUnits (l := l) T b u
  have hElog := hE lam
  have hLlog := hL u
  have hnormu := hnorm u
  have hd := dQpFactor_eq_n_mul_dStack (l := l) T b nL hn
  rw [hElog, hnormu, hLlog, hd]
  ring

end LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual

end
