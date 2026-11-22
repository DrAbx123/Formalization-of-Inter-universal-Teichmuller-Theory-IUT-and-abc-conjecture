import tmp.sheaf.xif.paper.QVFamRootCoefficientActual
import tmp.sheaf.xif.paper.QVPilotThetaHullNestingActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual

/-! # Corrected root coefficient c_root = qVFamilyLatticeCoefficient/(2l)

The root coefficient is the full qVFamily lattice coefficient divided by 2l,
not order/(2l).  The old full coefficient is exactly 2l times the corrected root
coefficient.  Root theta regions use j^2 c_root; the root hull is their closure.

Compactness/closedness and Haar positivity/finiteness of the root hull are
recorded as exact topology/measure requirements; no fake compactness is
asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootCoefficientCorrectedActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootCoefficientActual
open LeanFormal.IUT.XiFPaper.QVPilotThetaHullNestingActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Corrected root coefficient = full lattice coefficient / (2l). -/
noncomputable def rootCoeffCorrected : Real :=
  qVFamilyLatticeCoefficient (l := l) T b / (2 * (l.value : Real))

/-- The old full coefficient is 2l times the corrected root coefficient. -/
theorem oldCoeff_eq_twoL_mul_rootCoeff :
    qVFamilyLatticeCoefficient (l := l) T b =
      (2 * (l.value : Real)) * rootCoeffCorrected (l := l) T b := by
  unfold rootCoeffCorrected
  have htwo : (2 * (l.value : Real)) ≠ 0 := by positivity
  field_simp [htwo]

/-- Corrected root theta coefficient at label j. -/
noncomputable def rootThetaCoefficientCorrected
    (j : SignedLabel l.value) : qVFamTensorV -> Real :=
  fun _ => (gaussExponent j.1).toNat * rootCoeffCorrected (l := l) T b

/-- Actual corrected root theta region. -/
noncomputable def rootThetaRegionCorrected
    (j : SignedLabel l.value) : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (rootThetaCoefficientCorrected (l := l) T b j)

/-- Actual corrected root image union. -/
noncomputable def rootThetaImageSetCorrected : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, rootThetaRegionCorrected (l := l) T b j

/-- Actual corrected root closure hull. -/
noncomputable def rootThetaHullCorrected : Set (qVFamTensorBlock T b) :=
  closure (rootThetaImageSetCorrected (l := l) T b)

/-- Exact topology/measure requirements for the corrected root hull. -/
structure RootThetaHullTopologyGap
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] : Prop where
  hull_closed : IsClosed (rootThetaHullCorrected (l := l) T b)
  hull_compact : IsCompact (rootThetaHullCorrected (l := l) T b)
  hull_haar_pos : 0 < μ (rootThetaHullCorrected (l := l) T b)
  hull_haar_finite : μ (rootThetaHullCorrected (l := l) T b) < ⊤

/-- The exact topology/measure gap requirement; no inhabitant is asserted. -/
def RootThetaHullTopologyGapRequired
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] : Prop :=
  Nonempty (RootThetaHullTopologyGap (l := l) T b μ)

end LeanFormal.IUT.XiFPaper.RootCoefficientCorrectedActualAdapted

end
