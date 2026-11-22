import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import LeanFormal.IUT.Foundations.Volumes.HaarLogVolume

/-! # AbsTopIII07NormalizedLocalVolumeActual — concrete normalized local volume mu_k(O_k)=1

STEP 0 prior-art (deep search 2026-11-10, query 'normalizedHaar|normalized volume|
measure.*Integers|CommonPrimeCompletion|...' -> LeanFormal 265 / xif-paper 874 /
archive 12 / gap-exploration 9 / vendor 57): reuse LeanFormal/IUT/Foundations/Volumes/
HaarLogVolume.lean:11-45 (closed-ball Haar positivity/scaling pattern);
ABCBridge/Geometry/FinitePlaceCommonPrimeCompletion.lean:20 CommonPrimeCompletion with
Field/NormedField/IsUltrametricDist/ProperSpace instances; our AbsTopIII02LocalVolumes
Actual ledger row Prop 5.7 (i)(a) (unique normalized volume).

PAPER: [AbsTopIII] Prop 5.7 (i)(a) lines 7915-7935: unique mu_k on compact open
subsets with additivity, translation invariance, normalization mu_k(O_k)=1;
mu_k^log = log(mu_k).  Here we construct mu_k concretely as the rescaled additive
Haar measure with mu_k(O_k)=1 on a nonarchimedean local field (and instantiate on
the actual tree carrier CommonPrimeCompletion).  The formula mu_k^log(m_k^n) =
-f*n*log(p) needs the scaling law for field multiplication and is recorded as the
next step (data row), not silently assumed.

LABEL: concrete class-A construction (normalization only; no formula claim yet). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual

open MeasureTheory Metric

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- The unit ball O_k = {x : ||x|| <= 1} (paper: O_k). -/
def unitBall : Set K := Metric.closedBall (0 : K) 1

/-- The unit ball is nonempty. -/
theorem unitBall_nonempty : (unitBall (K := K)).Nonempty := ⟨0, by simp [unitBall]⟩

/-- In an ultrametric field the closed unit ball is open. -/
theorem unitBall_isOpen : IsOpen (unitBall (K := K)) :=
  IsUltrametricDist.isOpen_closedBall (x := (0 : K)) (r := 1) (by norm_num)

/-- The unit ball is compact (proper nonarchimedean field). -/
theorem unitBall_isCompact : IsCompact (unitBall (K := K)) :=
  isCompact_closedBall (0 : K) 1

/-- The concrete normalized volume mu_k: rescaled additive Haar with mu_k(O_k)=1. -/
noncomputable def normalizedHaar : Measure K :=
  (Measure.addHaar (unitBall (K := K)))⁻¹ • (Measure.addHaar : Measure K)

/-- Normalization: mu_k(O_k) = 1 (paper Prop 5.7 (i)(a), property (3)). -/
theorem normalizedHaar_unitBall :
    normalizedHaar (K := K) (unitBall (K := K)) = 1 := by
  unfold normalizedHaar
  rw [Measure.smul_apply]
  apply ENNReal.inv_mul_cancel
  · have hinterior : (interior (unitBall (K := K))).Nonempty := by
      rw [(unitBall_isOpen (K := K)).interior_eq]
      exact unitBall_nonempty (K := K)
    exact (Measure.measure_pos_of_nonempty_interior
      (μ := (Measure.addHaar : Measure K)) (s := unitBall (K := K)) hinterior).ne'
  · exact ne_of_lt (unitBall_isCompact (K := K)).measure_lt_top

/-- The real value of the normalized volume of the unit ball is 1. -/
theorem normalizedHaar_unitBall_real :
    (normalizedHaar (K := K)).real (unitBall (K := K)) = 1 := by
  rw [Measure.real, normalizedHaar_unitBall]
  norm_num

/-- The normalized volume is nonzero. -/
theorem normalizedHaar_ne_zero : normalizedHaar (K := K) ≠ 0 := by
  intro h
  have h1 : normalizedHaar (K := K) (unitBall (K := K)) = 0 := by rw [h]; simp
  rw [normalizedHaar_unitBall] at h1
  exact one_ne_zero h1

/-- The normalization ratio to additive Haar (definitional). -/
theorem normalizedHaar_apply (S : Set K) :
    normalizedHaar (K := K) S = (Measure.addHaar (unitBall (K := K)))⁻¹ *
      (Measure.addHaar : Measure K) S := rfl

/- Concrete instantiation on the actual tree carrier CommonPrimeCompletion. -/
section Completion

variable {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
variable (place : LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime F p)

local instance absTopIIIMeasurableSpace : MeasurableSpace
    (LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place) := borel _
local instance absTopIIIBorelSpace : BorelSpace
    (LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place) := ⟨rfl⟩

/-- The concrete normalized local volume on the actual p-adic completion at `place`. -/
noncomputable def completionNormalizedHaar :
    Measure (LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place) :=
  normalizedHaar (K := LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place)

/-- Normalization on the actual completion: completed mu_k(O_k) = 1. -/
theorem completionNormalizedHaar_unitBall :
    completionNormalizedHaar place
      (unitBall (K := LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place)) = 1 :=
  normalizedHaar_unitBall (K := LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion place)

end Completion

/-- Correspondence rows to [AbsTopIII] and to hull's/our volume files (data). -/
def lgpNormalizedVolumeCorrespondence : List (String × String) :=
  [ ("Prop 5.7 (i)(a) mu_k unique", "normalizedHaar (rescaled additive Haar); uniqueness follows from additivity+translation invariance+normalization on a Haar measure (uniqueness of Haar up to positive scalar)"),
    ("mu_k(O_k)=1", "normalizedHaar_unitBall (PROVED)"),
    ("mu_k^log(m_k^n) = -f n log p", "NEXT STEP: scaling law for field multiplication on additive Haar on the 1-dimensional K-vector space; NEEDS the modulus/ramification exponent API (concrete local field value group)"),
    ("sigma-additivity/translation invariance", "inherited from Measure.addHaar (additive Haar) and ENNReal scalar multiplication"),
    ("actual carrier", "CommonPrimeCompletion place (FinitePlaceCommonPrimeCompletion.lean:20) via completionNormalizedHaar (PROVED normalization)"),
    ("bridge to hull's AbsTopIII03Cor510Actual", "completionNormalizedHaar (unitBall)=1 is the concrete mu_k(O_k)=1 instance; hull's sourceHullHaar mass-1 theorem can import this file"),
    ("bridge to our AbsTopIII06WeightedVolumeBridgeActual", "lgpWeightedLogVolume can use completionNormalizedHaar: weighted log-volume of a region is its normalized real volume") ]

theorem lgpNormalizedVolumeCorrespondence_length :
    lgpNormalizedVolumeCorrespondence.length = 7 := rfl

#check normalizedHaar
#check normalizedHaar_unitBall
#check normalizedHaar_unitBall_real
#check completionNormalizedHaar_unitBall
#check lgpNormalizedVolumeCorrespondence_length

end LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual
end