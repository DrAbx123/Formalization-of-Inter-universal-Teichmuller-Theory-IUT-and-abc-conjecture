import tmp.sheaf.xif.paper.S861RootCharacterNormComparisonActual
import tmp.sheaf.xif.paper.S831StackHaarDimensionActual

/-! # S866: lifting S861 character/norm comparison to rootStackExtension

`rootStackExtension = L(mu_2l)` is a finite-dimensional L-vector space of
degree `dStack`.  The exact lift needs two inputs:

* S861's comparison on L: log dHC_L(u) = n * log ||u||;
* the restriction/induction Haar-character bridge on E/L:
  log dHC_E(algebraMap u) = dStack * log dHC_L(u).

Combining them gives log dHC_E(algebraMap u) = dQpFactor * log ||u|| when
`dQpFactor = n * dStack`.  This file records the exact bridge; the
restriction bridge is not asserted.  No fake analytic norm formula.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S866RootStackCharacterNormLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Units map L^* -> E^* along the intermediate-field inclusion. -/
noncomputable def rootStackAlgebraMapUnits :
    (rootNormedExtension T b)ˣ →* (rootStackExtension T b)ˣ :=
  Units.map (algebraMap (rootNormedExtension T b) (rootStackExtension T b)).toMonoidHom

/-- Exact restriction/induction bridge for the distributive Haar character:
the E-character of an L-unit is the dStack-th power of its L-character. -/
def RootStackHaarCharRestrictionBridge (n : Nat) : Prop :=
  ∀ u : (rootNormedExtension T b)ˣ,
    Real.log (distribHaarChar (rootStackExtension T b)
        (rootStackAlgebraMapUnits (l := l) T b u) : Real) =
      (dStack (l := l) T b : Real) *
        Real.log (distribHaarChar (rootNormedExtension T b) u : Real)

/-- Exact minimal bridge: the restriction formula at the S861 exponent n. -/
def RootStackHaarCharRestrictionBridgeRequired (n : Nat) : Prop :=
  RootStackHaarCharRestrictionBridge (l := l) T b n

/-- Lifted target: log dHC_E(algebraMap u) = dQpFactor * log ||u||. -/
def RootStackCharacterNormComparisonLift : Prop :=
  ∀ u : (rootNormedExtension T b)ˣ,
    Real.log (distribHaarChar (rootStackExtension T b)
        (rootStackAlgebraMapUnits (l := l) T b u) : Real) =
      (dQpFactor (l := l) T b : Real) *
        Real.log ‖(u : rootNormedExtension T b)‖

/-- Exact dQpFactor equality with n * dStack. -/
theorem dQpFactor_eq_n_mul_dStack (n : Nat)
    (hn : n = dK (l := l) T b * dLK (l := l) T b) :
    (dQpFactor (l := l) T b : Real) =
      (n : Real) * (dStack (l := l) T b : Real) := by
  rw [hn]
  unfold dQpFactor
  push_cast
  ring

/-- Conditional actual lift from S861 and the restriction bridge. -/
theorem rootStackCharacterNormComparisonLift_of_s861_and_restriction
    (n : Nat)
    (hn : n = dK (l := l) T b * dLK (l := l) T b)
    (hS : RootNormedCharacterNormComparison (l := l) T b n)
    (hR : RootStackHaarCharRestrictionBridge (l := l) T b n) :
    RootStackCharacterNormComparisonLift (l := l) T b := by
  intro u
  rw [hR u, hS u]
  have hd := dQpFactor_eq_n_mul_dStack (l := l) T b n hn
  rw [hd]
  ring

end LeanFormal.IUT.XiFPaper.S866RootStackCharacterNormLiftActual

end
