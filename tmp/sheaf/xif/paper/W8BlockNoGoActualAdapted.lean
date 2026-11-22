import tmp.sheaf.xif.paper.S822PadicDetHullActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open MeasureTheory

/-! # W8: the actual tensor-block instance of the topological no-go

Companion to W8ConfigurationSpaceNoGoActual.lean (the Q_p model).  This file
works on the actual paper carrier: the one-factor tensor block of
QVFamTensorCoefficientActual with its finite-dimensional Q_p topology
(FinitePadicTensorTopology), the canonical unit reference O, and the prime
scalar unit pU of FinitePlaceNormalizedUnitScalingLogVolume.

The theorem says: no functional of the region that is invariant under ambient
homeomorphisms can equal the actual degree-normalized Haar log on both O and
pU • O.  The two regions are homeomorphic (the homeomorphism is
multiplication by pU), while their actual normalized logs are 0 and -log p
(S822: arithmeticTupleNormalizedLogVolume_primeScalar_zpow, k = 0 and k = 1).
Hence every topological invariant of the hull is blind to the exponent, which
is exactly the quantity the paper comparison needs.

No fake hull, no surrogate target, no new axiom. -/

namespace LeanFormal.IUT.XiFPaper.W8BlockNoGoActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S822PadicDetHullActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]
variable (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)] [BorelSpace (qVFamTensorBlock T b)]

/-- The canonical unit reference of the actual paper tensor block. -/
abbrev blockO : Set (qVFamTensorBlock T b) :=
  arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The prime scalar unit of the actual block. -/
abbrev blockPU : (qVFamTensorBlock T b)ˣ :=
  arithmeticTuplePrimeScalarUnit (qVFamTensorPlaces T b) qVFamTensorTuple

/-- Units act continuously on the actual tensor block. -/
local instance blockUnitsContinuousConstSMul :
    ContinuousConstSMul (qVFamTensorBlock T b)ˣ (qVFamTensorBlock T b) := by
  refine ⟨fun u => ?_⟩
  change Continuous (fun x : qVFamTensorBlock T b =>
    (u : qVFamTensorBlock T b) * x)
  exact (LinearMap.mulLeft ℚ_[qVFamTensorP T b]
    (u : qVFamTensorBlock T b)).continuous_of_finiteDimensional

/-- The actual normalized log of the canonical region is zero. -/
theorem normLog_blockO
    (mu : Measure (qVFamTensorBlock T b)) [mu.IsAddHaarMeasure] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
      (blockO (l := l) T b) = 0 := by
  have h := arithmeticTupleNormalizedLogVolume_primeScalar_zpow
    (p := qVFamTensorP T b) (places := qVFamTensorPlaces T b)
    (tuple := qVFamTensorTuple) mu (k := 0)
  have hset : ((↑(blockPU (l := l) T b ^ (0 : ℤ)) :
      qVFamTensorBlock T b) • blockO (l := l) T b) = blockO (l := l) T b := by
    rw [zpow_zero, Units.val_one, one_smul]
  rw [hset] at h
  simpa using h

/-- The actual normalized log of the prime-scalar region is -log p. -/
theorem normLog_blockPU
    (mu : Measure (qVFamTensorBlock T b)) [mu.IsAddHaarMeasure] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
      (blockPU (l := l) T b • blockO (l := l) T b) =
      -Real.log (qVFamTensorP T b : ℝ) := by
  have h := arithmeticTupleNormalizedLogVolume_primeScalar_zpow
    (p := qVFamTensorP T b) (places := qVFamTensorPlaces T b)
    (tuple := qVFamTensorTuple) mu (k := 1)
  have hset : ((↑(blockPU (l := l) T b ^ (1 : ℤ)) :
      qVFamTensorBlock T b) • blockO (l := l) T b) =
      blockPU (l := l) T b • blockO (l := l) T b := by
    rw [zpow_one]
    rfl
  rw [hset] at h
  simpa using h

/-- The prime scalar homeomorphism carries O onto pU • O. -/
theorem image_blockO_blockPU :
    (Homeomorph.smul (blockPU (l := l) T b)) '' blockO (l := l) T b =
      blockPU (l := l) T b • blockO (l := l) T b := by
  rw [show (Homeomorph.smul (blockPU (l := l) T b) :
      qVFamTensorBlock T b → qVFamTensorBlock T b) =
      fun x => blockPU (l := l) T b • x from rfl]
  rfl

/-- Block-level no-go.  No ambient-homeomorphism-invariant functional of
the region equals the actual normalized Haar log on both canonical regions
O and pU • O, although the two regions are homeomorphic. -/
theorem no_homeomorphism_invariant_block_log
    (mu : Measure (qVFamTensorBlock T b)) [mu.IsAddHaarMeasure]
    (F : Set (qVFamTensorBlock T b) → ℝ)
    (hinv : ∀ (h : qVFamTensorBlock T b ≃ₜ qVFamTensorBlock T b)
      (S : Set (qVFamTensorBlock T b)), F (h '' S) = F S) :
    ¬ (F (blockO (l := l) T b) =
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
          qVFamTensorTuple mu (blockO (l := l) T b) ∧
       F (blockPU (l := l) T b • blockO (l := l) T b) =
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
          qVFamTensorTuple mu (blockPU (l := l) T b • blockO (l := l) T b)) := by
  rintro ⟨h0, h1⟩
  have heq : F (blockPU (l := l) T b • blockO (l := l) T b) =
      F (blockO (l := l) T b) := by
    rw [← image_blockO_blockPU (l := l) T b]
    exact hinv _ _
  rw [h0, h1, normLog_blockO (l := l) T b mu,
    normLog_blockPU (l := l) T b mu] at heq
  have hlog : Real.log (qVFamTensorP T b : ℝ) = 0 := by linarith
  exact (Real.log_pos (by
    have h1 : 1 < qVFamTensorP T b :=
      (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
    exact_mod_cast h1)).ne' hlog

#print axioms no_homeomorphism_invariant_block_log

end LeanFormal.IUT.XiFPaper.W8BlockNoGoActualAdapted

end
