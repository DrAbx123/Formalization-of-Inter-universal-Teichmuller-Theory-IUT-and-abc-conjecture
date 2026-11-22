import tmp.sheaf.xif.paper.S1269UniformizerFactorActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1337GeneralFactorNormPowActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual
open LeanFormal.IUT.XiFPaper.S1207EUniformizerActual
open LeanFormal.IUT.XiFPaper.S1216EUniformizerDecompositionActual
open LeanFormal.IUT.XiFPaper.S1269UniformizerFactorActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Integer powers of the E Haar factor. -/
theorem s1337HaarFactor_zpow (u : (rootStackExtension T b)ˣ) (n : Int) :
    rootStackHaarFactor T b (u ^ n) = rootStackHaarFactor T b u ^ n := by
  unfold rootStackHaarFactor
  rw [map_zpow]
  rw [ENNReal.coe_zpow (by
    exact_mod_cast (MeasureTheory.distribHaarChar_pos
      (A := rootStackExtension T b) (g := u)).ne') n]

/-- Pure ENNReal power identity used by the general factor formula. -/
lemma s1337_ofReal_pow_zpow_eq (a : Real) (ha : 0 < a) (d : Nat) (n : Int) :
    (ENNReal.ofReal (a ^ d)) ^ n = ENNReal.ofReal ((a ^ n) ^ d) := by
  let c : NNReal := Real.toNNReal a
  have hc : (c : Real) = a := Real.coe_toNNReal a ha.le
  have hcpos : 0 < c := Real.toNNReal_pos.mpr ha
  have hpow : ENNReal.ofReal (a ^ d) = ((c ^ d : NNReal) : ENNReal) := by
    rw [show ENNReal.ofReal (a ^ d) = ((Real.toNNReal (a ^ d) : NNReal) : ENNReal) from rfl,
      Real.toNNReal_pow ha.le]
  have hnn : (((c ^ d : NNReal) ^ n)) = (((c ^ n) : NNReal) ^ d) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_zpow, NNReal.coe_pow, NNReal.coe_pow, NNReal.coe_zpow]
    rw [hc]
    rw [← zpow_natCast]
    conv_rhs => rw [← zpow_natCast]
    rw [zpow_comm]
  calc
    (ENNReal.ofReal (a ^ d)) ^ n = ((c ^ d : NNReal) : ENNReal) ^ n := by rw [hpow]
    _ = (((((c ^ d : NNReal) ^ n)) : NNReal) : ENNReal) :=
      (ENNReal.coe_zpow (r := (c ^ d : NNReal)) (pow_ne_zero d hcpos.ne') n).symm
    _ = (((((c ^ n : NNReal) ^ d)) : NNReal) : ENNReal) := by rw [hnn]
    _ = ((ENNReal.ofReal (a ^ n)) ^ d) := by
      rw [ENNReal.coe_pow]
      rw [show (((c ^ n : NNReal) : ENNReal)) = ENNReal.ofReal (a ^ n) by
        rw [show (c : NNReal) = Real.toNNReal a from rfl,
          ← Real.toNNReal_zpow ha.le n]
        rw [ENNReal.ofReal]]
    _ = ENNReal.ofReal ((a ^ n) ^ d) := by
      rw [ENNReal.ofReal_pow (zpow_nonneg ha.le n)]

/-- Actual general E factor-norm power formula, from the S1269 uniformizer
factor and the actual DVR decomposition. -/
theorem s1337RootStackHaarFactorNormPow_actual :
    RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b) := by
  intro u
  obtain ⟨n, eps, hu, hnormeps⟩ := s1216DVRDecomposition_actual (l := l) T b u
  rw [hu, s1269HaarFactor_mul (l := l) T b,
    s1124UnitFactorOne_actual (l := l) T b eps hnormeps, one_mul,
    s1337HaarFactor_zpow (l := l) T b,
    s1269UniformizerFactor (l := l) T b]
  rw [Units.val_mul, norm_mul, hnormeps, one_mul,
    Units.val_zpow_eq_zpow_val, norm_zpow]
  exact s1337_ofReal_pow_zpow_eq
    (‖(rootStackUniformizerField (l := l) T b :
      rootStackExtension T b)‖)
    (norm_pos_iff.mpr (Units.ne_zero (rootStackUniformizerField (l := l) T b)))
    (dQpFactor (l := l) T b) n

/-- Fully actual S885 E uniformizer data: all five fields are now theorems. -/
noncomputable def s1337UniformizerData_actual :
    S885UniformizerData (l := l) T b where
  pi := rootStackUniformizerField (l := l) T b
  pi_norm_lt_one := rootStackUniformizer_norm_lt_one (l := l) T b
  unit_factor_one := s1124UnitFactorOne_actual (l := l) T b
  decomposition := s1216DVRDecomposition_actual (l := l) T b
  uniformizer_factor := s1269UniformizerFactor (l := l) T b
  factor_norm_pow := s1337RootStackHaarFactorNormPow_actual (l := l) T b

end LeanFormal.IUT.XiFPaper.S1337GeneralFactorNormPowActual

end
