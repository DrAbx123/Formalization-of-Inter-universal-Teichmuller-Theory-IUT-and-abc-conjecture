/- U-R C2 (P): K-side theta/packet objects (kurt).

Carrier per Lead/david carrier map: theta reading and H_pkt packet both live on
K-completions (paper IUT IV L1626-1650: k_i := K_{v_i}); q/M stay F-side
scalars (qVFamNormalizedCoefficient / qVFamTensorP, actualQPilotMagnitudeClassical
unchanged); the inner lambda/d_mod slot stays F-side.  Outer weight is
normDegreeWeight = paperDifferentWeight (david, Mzk1HT82PaperWeightDiffActual).
K-side place/prime/different data come from sophie's Mzk1ULKSideLettersActual
(ksP/ksPlace/ksD/ksLogP/normDegreeWeight).

THIS FILE provides the K-side definitions only (no free parameters, no retained
fields): theta coefficient family, nz theta region/image/hull/log/root, and the
actual per-bad-place packet value urPacketV_K.  Volume/bound lemmas are the next
batch (generic proofs re-instantiated on K-side).

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level elaboration budget). -/
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullUpperActual
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The rational prime of the bad K-place is prime. -/
noncomputable instance ksPFact : Fact (Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val)) :=
  completionRationalPrime_fact (nativeBadToKPlace T b)

/-- K-side places: the bad K-place at the unique (Unit) tensor factor. -/
noncomputable def ksPlaces :
    (i : qVFamTensorV) → Unit → FinitePlaceAtPrime T.arithmetic.K ((completionRationalPrime (nativeBadToKPlace T b)).val) :=
  fun _ _ => ksPlace T b

/-- K-side tuple: the unique point. -/
def ksTuple : qVFamTensorV → Unit := fun _ => ()

/-- K-side tensor block at the bad K-place. -/
abbrev ksBlock : Type := ArithmeticTensorTupleBlock (places := ksPlaces T b) (ksTuple)

/-- The K-side theta coefficient vector at a signed label. -/
noncomputable def ksThetaCoeff (j : SignedLabel l.value) : qVFamTensorV → ℝ :=
  fun _ => ((gaussExponent j.1).toNat : ℝ) * actualRootCoeff (l := l) T b ()

/-- The K-side theta region at a signed label (same coefficient family, K-side carrier). -/
noncomputable def ksThetaRegion (j : SignedLabel l.value) : Set (ksBlock T b) :=
  thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
    (ksThetaCoeff (l := l) T b j)

/-- Nonzero signed labels (paper theta labels are nonzero). -/
abbrev ksNonzeroLabel : Type := {j : SignedLabel l.value // j.1 ≠ 0}

/-- The K-side nonzero-label theta image set. -/
noncomputable def ksThetaImageSet : Set (ksBlock T b) :=
  ⋃ j : ksNonzeroLabel (l := l), ksThetaRegion (l := l) T b j.1

/-- The K-side nonzero-label theta hull (route theta object on the K carrier). -/
noncomputable def ksThetaHull : Set (ksBlock T b) :=
  closure (ksThetaImageSet (l := l) T b)

/-- The K-side value-group ceiling exponent of the half root coefficient. -/
noncomputable def ksGaussK : ℤ :=
  Int.ceil (actualRootCoeff (l := l) T b () *
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (ksPlace T b)) (p := (completionRationalPrime (nativeBadToKPlace T b)).val) : ℝ))

/-- The K-side value-group ceiling of the half root coefficient. -/
noncomputable def ksCeilC : ℝ :=
  (ksGaussK (l := l) T b : ℝ) /
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (ksPlace T b)) (p := (completionRationalPrime (nativeBadToKPlace T b)).val) : ℝ)

/-- The K-side bad-place different order (localNormOrder of the local different generator). -/
noncomputable def ksDifferentOrder : ℝ :=
  localNormOrder ((completionRationalPrime (nativeBadToKPlace T b)).val)
    ((LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentGenerator
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val) (L := CommonPrimeCompletion (ksPlace T b))) :
      CommonPrimeCompletion (ksPlace T b))

/-- The K-side exceptional set (paper I*). -/
noncomputable def ksExceptional : Finset qVFamTensorV :=
  Finset.univ.filter (fun _ : qVFamTensorV =>
    (completionRationalPrime (nativeBadToKPlace T b)).val - 2 <
      logShellRamificationExponent
        (K := CommonPrimeCompletion (ksPlace T b)) (p := (completionRationalPrime (nativeBadToKPlace T b)).val))

/-- The K-side exceptional sum sum_{i in I*} (3 + log e_i). -/
noncomputable def ksExceptionalSum : ℝ :=
  ∑ _i ∈ ksExceptional (l := l) T b,
    (3 + Real.log
      (logShellRamificationExponent
        (K := CommonPrimeCompletion (ksPlace T b)) (p := (completionRationalPrime (nativeBadToKPlace T b)).val) : ℝ))

/-- The actual per-bad-place paper Step(v) bound on the K carrier
(packet value V_b, no free parameters). -/
noncomputable def urPacketV_K : ℝ :=
  (-(ksCeilC (l := l) T b) + ksDifferentOrder (l := l) T b + 1) * ksLogP T b +
    ksExceptionalSum (l := l) T b

/-- The K-side theta hull log volume. -/
noncomputable def ksThetaHullLog
    [MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)] : ℝ :=
  arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple Measure.addHaar
    (ksThetaHull (l := l) T b)

/-- LEGACY-KSIDE: K-side weighted theta hull log root with normDegreeWeight (f/[K:Q]).
Superseded by ksThetaHullLogRoot_lam (paper lambda/d_mod weights, Lead ruling (A));
kept only for historical comparison. -/
noncomputable def ksThetaHullLogRoot
    [∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [∀ b : Bad (nativePlaceSelection T),
      BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)] : ℝ :=
  ∑ b' : Bad (nativePlaceSelection T),
    normDegreeWeight T b' * ksThetaHullLog (l := l) T b'

/-- The paper-weighted q-pilot magnitude Q_paper = sum_b normDegreeWeight_b · c_norm_b · log p_b. -/
noncomputable def qPilotMagnitudePaper : ℝ :=
  ∑ b' : Bad (nativePlaceSelection T),
    normDegreeWeight T b' * (qVFamNormalizedCoefficient T b' * ksLogP T b')

/-- M_paper = Q_paper / (2l). -/
noncomputable def M_paper : ℝ :=
  qPilotMagnitudePaper (l := l) T / (2 * (l.value : ℝ))

/-- The norm-degree weight f_P/[K:Q] is nonnegative. -/
theorem normDegreeWeight_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ normDegreeWeight T b := by
  unfold normDegreeWeight
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- K-side weighted theta upper bound with the paper fiber-normalized weight
normDegreeWeight (the Lead-ruled hstepVIII outer weight). -/
theorem ksThetaHullLogRoot_le_ucWeightedHpkt
    [∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [∀ b : Bad (nativePlaceSelection T),
      BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    ksThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (normDegreeWeight T) packetV := by
  unfold ksThetaHullLogRoot
  unfold LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
  exact Finset.sum_le_sum
    (fun b _ => mul_le_mul_of_nonneg_left (hperB b) (normDegreeWeight_nonneg (l := l) T b))

#print axioms normDegreeWeight_nonneg
#print axioms ksThetaHullLogRoot_le_ucWeightedHpkt

/-! ## Paper lambda weights for H_pkt / theta_P5 (Lead ruling (A)) -/

/-- paper lambda_v = [Fmod_v : Q_p] = e_v f_v (local degree at the Fmod place). -/
noncomputable def lamWeight (b : Bad (nativePlaceSelection T)) : ℝ := by
  letI : Fact (Nat.Prime ((completionRationalPrime b.1).val)) :=
    completionRationalPrime_fact b.1
  exact (Module.finrank ℚ_[(completionRationalPrime b.1).val]
    (NormalizedCompletion b.1) : ℝ)

/-- paper d_mod = [Fmod : Q]. -/
noncomputable def dModF : ℝ :=
  (Module.finrank ℚ T.arithmetic.Fmod : ℝ)

/-- The paper H_pkt weight lambda_v / d_mod. -/
noncomputable def thetaLamWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  lamWeight T b / dModF T

theorem lamWeight_nonneg (b : Bad (nativePlaceSelection T)) : 0 ≤ lamWeight T b := by
  unfold lamWeight
  exact Nat.cast_nonneg _

theorem dModF_pos : 0 < dModF T := by
  unfold dModF
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.Fmod)

theorem thetaLamWeight_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ thetaLamWeight T b :=
  div_nonneg (lamWeight_nonneg T b) (dModF_pos T).le

/-- theta_P5 hull log root with the paper lambda/d_mod weights. -/
noncomputable def ksThetaHullLogRoot_lam
    [∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [∀ b : Bad (nativePlaceSelection T),
      BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)] : ℝ :=
  ∑ b' : Bad (nativePlaceSelection T),
    thetaLamWeight T b' * ksThetaHullLog (l := l) T b'

/-- The lambda-weighted theta upper bound: hPkt with the paper lambda weights. -/
theorem ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam
    [∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [∀ b : Bad (nativePlaceSelection T),
      BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ packetV b) :
    ksThetaHullLogRoot_lam (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (thetaLamWeight T) packetV := by
  unfold ksThetaHullLogRoot_lam
  unfold LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
  exact Finset.sum_le_sum
    (fun b _ => mul_le_mul_of_nonneg_left (hperB b) (thetaLamWeight_nonneg T b))


/-- A nonzero signed label has Gauss exponent at least one. -/
theorem one_le_gaussExponent_toNat {z : ℤ} (hz : z ≠ 0) :
    1 ≤ (LeanFormal.IUT.gaussExponent z).toNat := by
  have hpos : 0 < z ^ 2 := sq_pos_of_ne_zero hz
  unfold LeanFormal.IUT.gaussExponent
  omega

/-- The label-1 theta region lies in the nonzero-label theta hull. -/
theorem ksOneLabelRegion_subset_hull (b : Bad (nativePlaceSelection T)) :
    ksThetaRegion (l := l) T b (oneLabel l) ⊆ ksThetaHull (l := l) T b := by
  unfold ksThetaHull
  intro x hx
  exact subset_closure (s := ksThetaImageSet (l := l) T b)
    (Set.mem_iUnion.mpr ⟨⟨oneLabel l, by
      show (oneLabel l).1 ≠ 0
      simp [oneLabel]⟩, hx⟩)

#print axioms one_le_gaussExponent_toNat
#print axioms ksOneLabelRegion_subset_hull

#print axioms lamWeight_nonneg
#print axioms dModF_pos
#print axioms thetaLamWeight_nonneg
#print axioms ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam

#print axioms ksPlaces
#print axioms ksBlock
#print axioms ksThetaRegion
#print axioms ksThetaHull
#print axioms ksCeilC
#print axioms ksDifferentOrder
#print axioms urPacketV_K
#print axioms ksThetaHullLogRoot
#print axioms qPilotMagnitudePaper
#print axioms M_paper

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
end