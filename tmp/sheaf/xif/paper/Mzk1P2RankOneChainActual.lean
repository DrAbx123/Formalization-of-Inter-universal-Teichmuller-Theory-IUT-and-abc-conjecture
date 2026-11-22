import tmp.sheaf.xif.paper.S757QVFamBlockIsometryActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
import tmp.sheaf.xif.paper.Mzk1P2R12WeightBridgeActual
import tmp.sheaf.xif.paper.Mzk1P2ArchLogSourceActual
import tmp.sheaf.xif.paper.Mzk1P2TensorDetFactorActual
import Mathlib.Tactic

/-! # P2 rank-one chain

The qVFam tensor block is one-factor.  Its actual one-factor linear equivalence
to rootBase is qVFamBlockLinearEquiv; conditional on QVFamBlockNormPreserving it
is an isometry, so there is no determinant factor in this rank-one block.

The P2 coefficient c_b, R1.3 nonnegativity and the arch-log source criterion
are then combined into one first-label rank-one comparison candidate.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2RankOneChainActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeTensorConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P2R12WeightBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2ArchLogSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual one-factor linear equivalence of the qVFam tensor block to rootBase. -/
noncomputable def p2RankOneBlockEquiv :
    qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootBase T b :=
  qVFamBlockLinearEquiv T b

/-- Conditional rank-one isometry; det factor is absent for this block. -/
noncomputable def p2RankOneBlockIsometry
    (hpres : QVFamBlockNormPreserving (l := l) T b) :
    qVFamTensorBlock T b ≃ₗᵢ[ℚ_[qVFamTensorP T b]] rootBase T b :=
  qVFamBlockLinearIsometryEquiv T b hpres

/-- Rank-one isometry preserves the norm. -/
theorem p2RankOneBlockIsometry_norm
    (hpres : QVFamBlockNormPreserving (l := l) T b)
    (x : qVFamTensorBlock T b) :
    ‖(p2RankOneBlockIsometry T b hpres) x‖ = ‖x‖ :=
  (p2RankOneBlockIsometry T b hpres).norm_map x

/-- The rank-one block is exactly the native tensor block at the qVFam data. -/
theorem p2RankOneBlock_eq_nativeBlock :
    qVFamTensorBlock T b =
      ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple :=
  rfl

/-- Rank-one native log-volume is the native theta readout. -/
theorem p2RankOne_logVolume_eq_nativeThetaReadout :
    nativeTensorLogVolume (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple =
      nativeThetaReadout T b := rfl

/-- R1.3 rank-one mass difference is nonnegative. -/
theorem p2RankOne_R13_nonneg : 0 ≤ p2R13Exact T :=
  p2R13Exact_nonneg T

/-- Rank-one weighted determinant log is nonpositive. -/
theorem p2RankOne_weightedDetLog_nonpos : p2WeightedDetLog T ≤ 0 :=
  p2WeightedDetLog_nonpos T

/-- Rank-one arch exact criterion, re-exported. -/
theorem p2RankOne_arch_criterion (f : (T.arithmetic.K)ˣ) :
    archDetMetricWeight (F := T.arithmetic.K) f =
        archCK (T.arithmetic.K) * p2R13Exact T ↔
      archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
        p2WeightedDetLog T :=
  p2ArchMetric_eq_archCK_mul_p2R13Exact_iff T f

/-- First-label rank-one comparison candidate: all actual data except the
explicitly named one-factor norm-preservation. -/
structure RankOneComparisonCandidate where
  hpres : QVFamBlockNormPreserving (l := l) T b
  blockIso : qVFamTensorBlock T b ≃ₗᵢ[ℚ_[qVFamTensorP T b]] rootBase T b
  nativeLogVolume_eq : nativeTensorLogVolume (p := qVFamTensorP T b)
      (qVFamTensorPlaces T b) qVFamTensorTuple = nativeThetaReadout T b
  r13_nonneg : 0 ≤ p2R13Exact T

/-- Build the candidate from the one actual missing norm-preservation. -/
noncomputable def rankOneComparisonCandidate
    (hpres : QVFamBlockNormPreserving (l := l) T b) :
    RankOneComparisonCandidate T b where
  hpres := hpres
  blockIso := p2RankOneBlockIsometry T b hpres
  nativeLogVolume_eq := p2RankOne_logVolume_eq_nativeThetaReadout T b
  r13_nonneg := p2RankOne_R13_nonneg T

/-- Exact remaining rank-one gaps. -/
def p2RankOneMissing : List String :=
  [ "QVFamBlockNormPreserving (one-factor norm instance equality)",
    "global element f with archimedeanLogNorm f = p2WeightedDetLog T",
    "multi-factor det factor / p-adic Haar det law (not needed in rank one)" ]

theorem p2RankOneMissing_length : p2RankOneMissing.length = 3 := rfl

#check p2RankOneBlockEquiv
#check p2RankOneBlockIsometry
#check p2RankOneBlockIsometry_norm
#check p2RankOneBlock_eq_nativeBlock
#check p2RankOne_R13_nonneg
#check rankOneComparisonCandidate
#check p2RankOneMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2RankOneChainActual
end
