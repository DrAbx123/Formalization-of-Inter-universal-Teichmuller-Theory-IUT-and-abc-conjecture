import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # qPilotRootRegion containment and monotonicity

No root normalized-log equality is needed.  On the actual per-b root tensor
block, the q-pilot root region is the minimal root theta region (label 1,
gauss exponent 1), hence it is contained in the closure hull of the root theta
union.  arithmeticTupleNormalizedLogVolume_mono then gives

  qPilotRootLog <= rootThetaHullLog.

If the actual scaling data for the q-pilot side is missing, only the monotone
inequality is asserted; the equality/lower-bound formula is recorded as an exact
gap, not faked.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootQPilotContainmentActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual label 1 in SignedLabel, with gauss exponent one. -/
noncomputable def oneRootLabel : SignedLabel l.value :=
  ⟨1, by
    have hstar := two_mul_lStar_add_one l.value l.odd
    constructor <;> omega⟩

theorem oneRootLabel_gauss :
    (gaussExponent (oneRootLabel (l := l)).1).toNat = 1 := by
  unfold oneRootLabel gaussExponent
  norm_num

/-- The actual root q-pilot region: minimal root theta region. -/
noncomputable def qPilotRootRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (fun _ => qVFamPaperRootCoefficient T b)

/-- The actual root theta region at label j. -/
noncomputable def rootThetaRegion (j : SignedLabel l.value) :
    Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (fun _ => qVFamPaperThetaTensorCoefficient T b j)

/-- The root theta union. -/
noncomputable def rootThetaImageSet : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, rootThetaRegion T b j

/-- The root theta closure hull. -/
noncomputable def rootThetaHull : Set (qVFamTensorBlock T b) :=
  closure (rootThetaImageSet T b)

/-- Root q-pilot region is the minimal root theta region. -/
theorem qPilotRootRegion_eq_theta_one :
    qPilotRootRegion T b = rootThetaRegion T b (oneRootLabel (l := l)) := by
  unfold qPilotRootRegion rootThetaRegion
  congr 1
  funext i
  unfold qVFamPaperThetaTensorCoefficient oneRootLabel
  simp [gaussExponent]

/-- Root q-pilot region is contained in the root theta hull. -/
theorem qPilotRootRegion_subset_hull :
    qPilotRootRegion T b ⊆ rootThetaHull T b := by
  intro x hx
  apply subset_closure
  rw [qPilotRootRegion_eq_theta_one] at hx
  exact Set.mem_iUnion.mpr ⟨oneRootLabel (l := l), hx⟩

/-- Actual q-pilot root normalized log. -/
noncomputable def qPilotRootLog
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple mu (qPilotRootRegion T b)

/-- Actual root theta hull normalized log. -/
noncomputable def rootThetaHullLog
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple mu (rootThetaHull T b)

/-- The monotone inequality qPilotRootLog <= rootThetaHullLog. -/
theorem qPilotRootLog_le_rootThetaHullLog
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    (hpos : 0 < mu (qPilotRootRegion T b))
    (hfin : mu (rootThetaHull T b) < ⊤) :
    qPilotRootLog (l := l) T b mu <= rootThetaHullLog (l := l) T b mu :=
  arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qPilotRootRegion_subset_hull (l := l) T b) hpos hfin

/-- Exact gap for the q-pilot side formula: the actual scaling data for the
qPilotRootRegion.  No equality is asserted without it. -/
def QPilotRootScalingDataGap : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (fun _ => qVFamPaperRootCoefficient T b))

/-- Conditional exact formula for the q-pilot root normalized log from the
actual scaling data. -/
theorem qPilotRootLog_eq_formula
    [MeasurableSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b))
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun _ => qVFamPaperRootCoefficient T b)) :
    qPilotRootLog (l := l) T b mu =
      -((∑ _ : qVFamTensorV, qVFamPaperRootCoefficient T b) *
        Real.log (qVFamP T b : Real)) := by
  unfold qPilotRootLog qPilotRootRegion
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu data

end LeanFormal.IUT.XiFPaper.RootQPilotContainmentActualAdapted

end
