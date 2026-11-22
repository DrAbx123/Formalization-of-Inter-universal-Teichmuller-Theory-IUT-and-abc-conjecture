import tmp.sheaf.xif.paper.QVPilotThetaHullNestingActual

-- Local per-b Theta-hull normalized log from the volumedet QV nesting
--
-- Local theta hull = thetaHullCandidate with hullRegion = qPilotRegion.
-- Local log = arithmeticTupleNormalizedLogVolume places tuple μ hullRegion,
-- which already normalizes by arithmeticTupleCanonicalUnitReference.
-- No old paperBadThetaPilotHullVolume/constant-tuple Haar/ENNReal zero is
-- used. WRITE-ONLY; local compile after write.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LocalPerBHullNormalizedLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVPilotThetaHullNestingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open MeasureTheory

universe uK uI uV u

variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {l : PrimeGeFive}
variable {ι : Type uI} [Fintype ι]
variable {V : ι -> Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Paper root coefficient c_root = qVFamilyLatticeCoefficient/(2l), constant over coordinates.
noncomputable def localCoeff (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (i : ι) : Real :=
  qVFamilyLatticeCoefficient (l := l) T b / (2 * (l.value : Real))

/-- The root coefficient is the full coefficient divided by 2l. -/
theorem localCoeff_eq_root (i : ι) :
    localCoeff (l := l) T b i =
      qVFamilyLatticeCoefficient (l := l) T b / (2 * (l.value : Real)) := rfl

theorem localOldCoeff_eq_two_l_mul_localCoeff (i : ι) :
    qVFamilyLatticeCoefficient (l := l) T b =
      (2 * (l.value : Real)) * localCoeff (l := l) T b i := by
  unfold localCoeff
  field_simp [show (2 * (l.value : Real)) ≠ 0 by positivity]

theorem localCoeff_nonneg
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    ∀ i : ι, 0 ≤ localCoeff T b i := by
  intro i
  unfold localCoeff
  apply div_nonneg
  · exact qVFamilyLatticeCoefficient_nonneg (l := l) T b
  · positivity

-- The actual local hull candidate: hullRegion = qPilotRegion.
noncomputable def localHullCandidate :
    ThetaHullCandidateData (l := l) places tuple (localCoeff T b) :=
  thetaHullCandidate (l := l) places tuple
    (localCoeff T b) (localCoeff_nonneg T b)

noncomputable abbrev localHullRegion :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  (localHullCandidate (l := l) places tuple T b).hullRegion

theorem localHullRegion_eq_qPilot :
    localHullRegion (l := l) places tuple T b =
      qPilotRegion places tuple (localCoeff T b) :=
  (localHullCandidate (l := l) places tuple T b).hullRegion_eq

-- The actual local normalized log, with the canonical unit reference already
-- built into arithmeticTupleNormalizedLogVolume.
noncomputable def localNormalizedHullLog : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (localHullRegion (l := l) places tuple T b)

theorem localNormalizedHullLog_eq :
    localNormalizedHullLog (l := l) places tuple μ T b =
      arithmeticTupleNormalizedLogVolume places tuple μ
        (thetaHullCandidate (l := l) places tuple
          (localCoeff T b) (localCoeff_nonneg T b)).hullRegion :=
  rfl

-- Unit normalization: the same normalized log-volume vanishes on
-- arithmeticTupleCanonicalUnitReference.
theorem localUnitNormalization :
    arithmeticTupleNormalizedLogVolume places tuple μ
      (arithmeticTupleCanonicalUnitReference places tuple) = 0 :=
  arithmeticTupleNormalizedLogVolume_canonicalUnitReference places tuple μ

/-- Actual root-coefficient formula for the local normalized hull log. -/
theorem localNormalizedHullLog_eq_neg_sum
    (data : ArithmeticTuplePureFractionalScalingData places tuple (localCoeff (l := l) T b)) :
    localNormalizedHullLog (l := l) places tuple μ T b =
      -((∑ i, localCoeff (l := l) T b i) * Real.log (p : Real)) := by
  unfold localNormalizedHullLog
  rw [localHullRegion_eq_qPilot]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data

-- Actual local per-b normalized hull-log object. Contents: the actual hull
-- region, its log, and the canonical unit-reference normalization. No
-- Frobenioid/LGP field is consumed.
structure LocalPerBHullNormalizedLogData where
  hullRegion : Set (ArithmeticTensorTupleBlock places tuple)
  hullRegion_eq : hullRegion =
    (thetaHullCandidate (l := l) places tuple
      (localCoeff T b) (localCoeff_nonneg T b)).hullRegion
  hullLog : Real
  hullLog_eq : hullLog =
    arithmeticTupleNormalizedLogVolume places tuple μ hullRegion
  unitReference : Set (ArithmeticTensorTupleBlock places tuple)
  unitReference_eq : unitReference =
    arithmeticTupleCanonicalUnitReference places tuple
  unitLog_eq :
    arithmeticTupleNormalizedLogVolume places tuple μ unitReference = 0

noncomputable def localPerBHullNormalizedLogData :
    LocalPerBHullNormalizedLogData (l := l) places tuple μ T b where
  hullRegion := localHullRegion (l := l) places tuple T b
  hullRegion_eq := rfl
  hullLog := localNormalizedHullLog (l := l) places tuple μ T b
  hullLog_eq := rfl
  unitReference := arithmeticTupleCanonicalUnitReference places tuple
  unitReference_eq := rfl
  unitLog_eq := localUnitNormalization places tuple μ

#check localCoeff
#check localCoeff_nonneg
#check localHullCandidate
#check localHullRegion_eq_qPilot
#check localNormalizedHullLog
#check localUnitNormalization
#check LocalPerBHullNormalizedLogData
#check localPerBHullNormalizedLogData

end LeanFormal.IUT.XiFPaper.LocalPerBHullNormalizedLogActual

end