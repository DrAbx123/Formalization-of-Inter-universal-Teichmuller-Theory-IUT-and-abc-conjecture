import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S811StackMuPermActionActual
import tmp.sheaf.xif.paper.S813PaperInterfaceHub

/-! # S816: StackyHullLogInterface from S793 least hull and S811 mu2l action

The hull and qPilot region are S793's actual least lambda-O hull / paper
region.  stackyVolume is the action-groupoid count normalized by 1/(2l).
Only the identification hullLog = stackyVolume is left exact.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S816StackyHullInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S811StackMuPermActionActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual least hull from S793. -/
noncomputable def hull : Set (qVFamTensorBlock T b) :=
  paperLeastLambdaOHull (l := l) T b

/-- The paper qPilot region = paper lambda-O region at c_root. -/
noncomputable def qPilotRegion : Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b)

/-- S793 gives equality of the qPilot region and least hull. -/
theorem qPilotRegion_eq_hull :
    qPilotRegion (l := l) T b = hull (l := l) T b := by
  unfold qPilotRegion hull
  exact (paperLeastLambdaOHull_eq_minimal (l := l) T b).symm

theorem qPilotRegion_subset_hull :
    qPilotRegion (l := l) T b ⊆ hull (l := l) T b := by
  rw [qPilotRegion_eq_hull]

/-- Actual normalized log of the hull. -/
noncomputable def hullLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (hull (l := l) T b)

/-- The qPilot log is the same actual region log (regions are equal). -/
noncomputable def qPilotLog : Real :=
  hullLog (l := l) T b mu

/-- Action groupoid count normalized by card(mu_2l) = 2l.  The group is the
actual S811 mu_2l permutation-action group. -/
noncomputable def stackyVolume : Real :=
  (1 / (2 * (l.value : Real))) *
    (Nat.card (StackMuGroup T b) : Real) * hullLog (l := l) T b mu

/-- Exact remaining bridge. -/
def HullLogEqStacky : Prop :=
  hullLog (l := l) T b mu = stackyVolume (l := l) T b mu

/-- Conditional inhabitant of the S813 StackyHullLogInterface. -/
noncomputable def stackyHullLogInterfaceOfBridge
    (h : HullLogEqStacky (l := l) T b mu) :
    StackyHullLogInterface (qVFamTensorBlock T b) where
  hull := hull (l := l) T b
  qPilotRegion := qPilotRegion (l := l) T b
  containment := qPilotRegion_subset_hull (l := l) T b
  qPilotLog := qPilotLog (l := l) T b mu
  hullLog := hullLog (l := l) T b mu
  log_le := le_rfl
  stackyVolume := stackyVolume (l := l) T b mu
  hullLog_eq_stacky := h

def StackyHullLogInterfaceRequired : Prop :=
  Nonempty (StackyHullLogInterface (qVFamTensorBlock T b))


/-- The primitive root-stack unit is primitive in the root-stack extension. -/
theorem stackMuUnit_isPrimitiveRoot :
    IsPrimitiveRoot ((stackMuUnit (l := l) T b : rootStackExtension T b))
      (2 * l.value) := by
  apply IsPrimitiveRoot.of_map_of_injective
    (f := algebraMap (rootStackExtension T b) (rootNormedAmbient T b))
  · change IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value)
    unfold stackMuRoot
    exact Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
      (rootNormedAmbient T b) (2 * l.value))
  · exact Subtype.coe_injective

/-- The S811 mu_2l action group has cardinal 2l. -/
theorem stackMuGroup_card :
    Nat.card (StackMuGroup (l := l) T b) = 2 * l.value := by
  haveI : NeZero (2 * l.value) :=
    ⟨Nat.mul_ne_zero (by norm_num) l.prime.ne_zero⟩
  exact stackMuUnit_isPrimitiveRoot (l := l) T b |>.card_rootsOfUnity

/-- The S816 exact bridge is actual. -/
theorem hullLogEqStacky_actual :
    HullLogEqStacky (l := l) T b mu := by
  unfold HullLogEqStacky stackyVolume
  rw [stackMuGroup_card (l := l) T b]
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by norm_num : (2:Nat) ≠ 0)
      l.prime.ne_zero)
  have hlv : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [hl, hlv]
  push_cast
  ring

/-- Actual inhabitant of the S813 stacky interface. -/
noncomputable def stackyHullLogInterface :
    StackyHullLogInterface (qVFamTensorBlock T b) :=
  stackyHullLogInterfaceOfBridge (l := l) T b mu
    (hullLogEqStacky_actual (l := l) T b mu)

end LeanFormal.IUT.XiFPaper.S816StackyHullInterfaceActual
end
