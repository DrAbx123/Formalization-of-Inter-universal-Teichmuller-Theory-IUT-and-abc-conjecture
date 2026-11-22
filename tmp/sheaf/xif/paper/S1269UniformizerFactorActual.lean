import tmp.sheaf.xif.paper.S1216EUniformizerDecompositionActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-! # S1269: actual E uniformizer Haar factor

The E-instance of the uniformizer factor formula
`rootStackHaarFactor pi = ofReal (||pi|| ^ dQpFactor)` for the actual DVR
uniformizer of the finite root stack.

The proof has two actual inputs:

* `FinitePadicHaarScaling.measure_prime_smul_finiteDimensional` gives the
  dQpFactor-dimensional p-scaling of the additive Haar measure on E;
* the actual DVR decomposition of the rational prime `p` with respect to the
  S1116 uniformizer `rootStackUniformizer` (exponent e > 0, unit part of
  norm one).

Combining them with multiplicativity of `distribHaarChar` and the actual unit
factor (S1124) yields the uniformizer factor.  No formula is assumed. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1269UniformizerFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual
open LeanFormal.IUT.XiFPaper.S1207EUniformizerActual
open LeanFormal.IUT.XiFPaper.S1216EUniformizerDecompositionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-! ## 0. The Qp structures on E -/

theorem s1269IsScalarTowerQp :
    IsScalarTower ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (rootStackExtension T b) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance s1269FiniteDimensionalQp :
    FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootStackExtension T b) := by
  haveI hST : IsScalarTower ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (rootStackExtension T b) := s1269IsScalarTowerQp (l := l) T b
  letI : FiniteDimensional (rootNormedExtension T b) (rootStackExtension T b) :=
    rootStackExtension_finiteDimensional (l := l) T b
  exact FiniteDimensional.trans ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
    (rootStackExtension T b)

/-! ## 1. The Qp degree of E is `dQpFactor` -/

theorem s1269_dQpFactor_eq_finrank :
    dQpFactor (l := l) T b =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootStackExtension T b) := by
  unfold dQpFactor dK dLK dStack
  haveI hST : IsScalarTower ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (rootStackExtension T b) := s1269IsScalarTowerQp (l := l) T b
  haveI hfree1 : Module.Free ℚ_[(qVFamTensorP T b)] (rootBase T b) :=
    Module.Free.of_divisionRing _ _
  haveI hfree2 : Module.Free (rootBase T b) (rootNormedExtension T b) :=
    Module.Free.of_divisionRing _ _
  haveI hfree3 : Module.Free ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    Module.Free.of_divisionRing _ _
  haveI hfree4 : Module.Free (rootNormedExtension T b) (rootStackExtension T b) :=
    Module.Free.of_divisionRing _ _
  have h2 : Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) *
        Module.finrank (rootBase T b) (rootNormedExtension T b) :=
    (Module.finrank_mul_finrank ℚ_[(qVFamTensorP T b)] (rootBase T b)
      (rootNormedExtension T b)).symm
  have h1 : Module.finrank ℚ_[(qVFamTensorP T b)] (rootStackExtension T b) =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) *
        Module.finrank (rootNormedExtension T b) (rootStackExtension T b) :=
    (Module.finrank_mul_finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (rootStackExtension T b)).symm
  rw [h1, h2]

/-! ## 2. The rational prime as an actual element of E -/

theorem s1269_norm_algebraMap_prime :
    ‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      (qVFamTensorP T b) : rootStackExtension T b)‖ =
      ‖(qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])‖ := by
  haveI hST : IsScalarTower ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (rootStackExtension T b) := s1269IsScalarTowerQp (l := l) T b
  rw [IsScalarTower.algebraMap_eq ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
    (rootStackExtension T b)]
  simp only [RingHom.comp_apply]
  rw [show ‖(algebraMap (rootNormedExtension T b) (rootStackExtension T b)
        (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
          (qVFamTensorP T b)) : rootStackExtension T b)‖ =
      ‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b) : rootNormedExtension T b)‖ from rfl]
  letI : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp (T := T) (b := b)
  letI : IsBoundedSMul ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    NormedSpace.toIsBoundedSMul
  letI : NormSMulClass ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    NormedDivisionRing.toNormSMulClass
  rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]

theorem s1269_prime_mem_integers :
    (algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      (qVFamTensorP T b) : rootStackExtension T b) ∈
      Integers (rootStackExtension T b) := by
  rw [mem_integers_iff, s1269_norm_algebraMap_prime (l := l) T b, Padic.norm_p]
  exact inv_le_one_of_one_le₀
    (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le)

noncomputable def s1269PrimeInteger : Integers (rootStackExtension T b) :=
  ⟨(algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      (qVFamTensorP T b) : rootStackExtension T b),
    s1269_prime_mem_integers (l := l) T b⟩

theorem s1269PrimeInteger_ne_zero : s1269PrimeInteger (l := l) T b ≠ 0 := by
  intro hzero
  have hval : (algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      (qVFamTensorP T b) : rootStackExtension T b) = 0 := by
    simpa [s1269PrimeInteger] using congrArg Subtype.val hzero
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero)
    ((algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)).injective
      (by simpa using hval))

/-! ## 3. The actual DVR decomposition p = unit * pi^e -/

/-- Actual prime/uniformizer decomposition in the integer ring of E. -/
structure RootStackPrimeUniformizerDecomposition where
  exponent : Nat
  unit : (Integers (rootStackExtension T b))ˣ
  eq : s1269PrimeInteger (l := l) T b =
    (unit : Integers (rootStackExtension T b)) *
      rootStackUniformizer (l := l) T b ^ exponent

noncomputable def s1269PrimeUniformizerDecomposition :
    RootStackPrimeUniformizerDecomposition (l := l) T b :=
  let h := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := s1269PrimeInteger (l := l) T b)
    (s1269PrimeInteger_ne_zero (l := l) T b)
    (rootStackUniformizer_irreducible (l := l) T b)
  { exponent := Classical.choose h
    unit := Classical.choose (Classical.choose_spec h)
    eq := Classical.choose_spec (Classical.choose_spec h) }

/-- The actual ramification exponent of p relative to the S1116 uniformizer. -/
def s1269PrimeRamificationExponent : Nat :=
  (s1269PrimeUniformizerDecomposition (l := l) T b).exponent

/-- The prime-unit part. -/
noncomputable def s1269PrimeUnit :
    (Integers (rootStackExtension T b))ˣ :=
  (s1269PrimeUniformizerDecomposition (l := l) T b).unit

theorem s1269Prime_eq_unit_mul_uniformizer_pow :
    s1269PrimeInteger (l := l) T b =
      (s1269PrimeUnit (l := l) T b : Integers (rootStackExtension T b)) *
        rootStackUniformizer (l := l) T b ^
          s1269PrimeRamificationExponent (l := l) T b :=
  (s1269PrimeUniformizerDecomposition (l := l) T b).eq

/-! ## 4. Field-unit form and norm relations -/

noncomputable def s1269PrimeUnitField : (rootStackExtension T b)ˣ :=
  Units.mk0 (((s1269PrimeUnit (l := l) T b : Integers (rootStackExtension T b)) :
    rootStackExtension T b)) (by
      intro h
      exact Units.ne_zero (s1269PrimeUnit (l := l) T b) (Subtype.ext h))

noncomputable def s1269PrimeFieldUnit : (rootStackExtension T b)ˣ :=
  Units.mk0 ((algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
    (qVFamTensorP T b) : rootStackExtension T b)) (by
      intro h
      have hp0 : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) = 0 :=
        (algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)).injective
          (by simpa using h)
      exact (Nat.cast_ne_zero.mpr
        (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero) hp0)

theorem s1269PrimeUnitField_norm :
    ‖(s1269PrimeUnitField (l := l) T b : rootStackExtension T b)‖ = 1 :=
  norm_unit_eq_one (s1269PrimeUnit (l := l) T b)

theorem s1269PrimeFieldUnit_eq_unit_mul_uniformizer_pow :
    s1269PrimeFieldUnit (l := l) T b =
      s1269PrimeUnitField (l := l) T b *
        rootStackUniformizerField (l := l) T b ^
          s1269PrimeRamificationExponent (l := l) T b := by
  apply Units.ext
  change ((s1269PrimeInteger (l := l) T b : Integers (rootStackExtension T b)) :
    rootStackExtension T b) =
    ((s1269PrimeUnit (l := l) T b : Integers (rootStackExtension T b)) :
      rootStackExtension T b) *
      (((rootStackUniformizer (l := l) T b : Integers (rootStackExtension T b)) :
        rootStackExtension T b) ^ s1269PrimeRamificationExponent (l := l) T b)
  simpa using congrArg (fun x : Integers (rootStackExtension T b) =>
    (x : rootStackExtension T b))
    (s1269Prime_eq_unit_mul_uniformizer_pow (l := l) T b)

theorem s1269PrimeFieldUnit_norm_eq_uniformizer_pow :
    ‖(s1269PrimeFieldUnit (l := l) T b : rootStackExtension T b)‖ =
      ‖(rootStackUniformizerField (l := l) T b : rootStackExtension T b)‖ ^
        s1269PrimeRamificationExponent (l := l) T b := by
  conv_lhs => rw [s1269PrimeFieldUnit_eq_unit_mul_uniformizer_pow (l := l) T b]
  rw [Units.val_mul, norm_mul, Units.val_pow_eq_pow_val, norm_pow,
    s1269PrimeUnitField_norm (l := l) T b, one_mul]

theorem s1269PrimeFieldUnit_norm_lt_one :
    ‖(s1269PrimeFieldUnit (l := l) T b : rootStackExtension T b)‖ < 1 := by
  rw [show (s1269PrimeFieldUnit (l := l) T b : rootStackExtension T b) =
    (algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      (qVFamTensorP T b) : rootStackExtension T b) from rfl]
  rw [s1269_norm_algebraMap_prime (l := l) T b, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀
    (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)

theorem s1269PrimeRamificationExponent_pos :
    0 < s1269PrimeRamificationExponent (l := l) T b := by
  by_contra h
  have h0 : s1269PrimeRamificationExponent (l := l) T b = 0 := by omega
  have hn : ‖(s1269PrimeFieldUnit (l := l) T b : rootStackExtension T b)‖ = 1 := by
    rw [s1269PrimeFieldUnit_norm_eq_uniformizer_pow (l := l) T b, h0, pow_zero]
  have hlt := s1269PrimeFieldUnit_norm_lt_one (l := l) T b
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/-! ## 5. dQpFactor-dimensional p-scaling of the stack Haar -/

theorem s1269Prime_smul_measure (S : Set (rootStackExtension T b)) :
    rootStackHaar (l := l) T b ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • S) =
      ENNReal.ofReal
        (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
          (qVFamTensorP T b) : rootStackExtension T b)‖ ^
            dQpFactor (l := l) T b) *
        rootStackHaar (l := l) T b S := by
  haveI hhaar : Measure.IsAddHaarMeasure (rootStackHaar (l := l) T b) :=
    Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)
  have h := LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := qVFamTensorP T b) (M := rootStackExtension T b)
    (rootStackHaar (l := l) T b) S
  calc
    rootStackHaar (l := l) T b ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • S)
        = ((qVFamTensorP T b : ENNReal) ^ Module.finrank
            ℚ_[(qVFamTensorP T b)] (rootStackExtension T b))⁻¹ *
            rootStackHaar (l := l) T b S := h
    _ = ENNReal.ofReal
          (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
            (qVFamTensorP T b) : rootStackExtension T b)‖ ^
              dQpFactor (l := l) T b) *
          rootStackHaar (l := l) T b S := by
      congr 1
      rw [s1269_dQpFactor_eq_finrank (l := l) T b]
      rw [s1269_norm_algebraMap_prime (l := l) T b, Padic.norm_p]
      rw [ENNReal.ofReal_pow (by positivity)]
      rw [ENNReal.ofReal_inv_of_pos
        (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos),
        ENNReal.ofReal_natCast]
      rw [ENNReal.inv_pow]

/-! ## 6. The Haar factor of the rational prime unit -/

theorem s1269HaarFactor_prime_eq_norm_pow :
    rootStackHaarFactor (l := l) T b (s1269PrimeFieldUnit (l := l) T b) =
      ENNReal.ofReal
        (‖(s1269PrimeFieldUnit (l := l) T b : rootStackExtension T b)‖ ^
          dQpFactor (l := l) T b) := by
  haveI hhaar : Measure.IsAddHaarMeasure (rootStackHaar (l := l) T b) :=
    Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)
  haveI hreg : (rootStackHaar (l := l) T b).Regular :=
    Measure.regular_addHaarMeasure (K₀ := Classical.arbitrary _)
  have hpos := unitBall_pos (l := l) T b (rootStackHaar (l := l) T b)
  have hfin := unitBall_fin (l := l) T b (rootStackHaar (l := l) T b)
  have hsmul : (s1269PrimeFieldUnit (l := l) T b) • stackUnitBall (l := l) T b =
      ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • stackUnitBall (l := l) T b) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      change (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • y =
        ((s1269PrimeFieldUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b) * y
      rw [Algebra.smul_def]
      rfl
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      change ((s1269PrimeFieldUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b) * y =
        (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) • y
      rw [Algebra.smul_def]
      rfl
  have hscale := s1269Prime_smul_measure (l := l) T b
    (S := stackUnitBall (l := l) T b)
  have hchar : distribHaarChar (rootStackExtension T b)
      (s1269PrimeFieldUnit (l := l) T b) =
      Real.toNNReal (‖(s1269PrimeFieldUnit (l := l) T b :
        rootStackExtension T b)‖ ^ dQpFactor (l := l) T b) := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul
      (μ := rootStackHaar (l := l) T b)
      (g := s1269PrimeFieldUnit (l := l) T b)
      (s := stackUnitBall (l := l) T b)
      (r := Real.toNNReal (‖(s1269PrimeFieldUnit (l := l) T b :
        rootStackExtension T b)‖ ^ dQpFactor (l := l) T b))
      hpos.ne' hfin.ne
    rw [hsmul, hscale]
    rfl
  unfold rootStackHaarFactor
  rw [hchar]
  rfl

/-! ## 7. The uniformizer bootstrap -/

theorem s1269HaarFactor_mul (u v : (rootStackExtension T b)ˣ) :
    rootStackHaarFactor (l := l) T b (u * v) =
      rootStackHaarFactor (l := l) T b u * rootStackHaarFactor (l := l) T b v := by
  unfold rootStackHaarFactor
  rw [map_mul, ENNReal.coe_mul]

theorem s1269HaarFactor_pow (u : (rootStackExtension T b)ˣ) (n : Nat) :
    rootStackHaarFactor (l := l) T b (u ^ n) =
      rootStackHaarFactor (l := l) T b u ^ n := by
  unfold rootStackHaarFactor
  rw [map_pow, ENNReal.coe_pow]

theorem s1269HaarFactor_uniformizer_pow_eq_prime :
    rootStackHaarFactor (l := l) T b
        (rootStackUniformizerField (l := l) T b ^
          s1269PrimeRamificationExponent (l := l) T b) =
      rootStackHaarFactor (l := l) T b (s1269PrimeFieldUnit (l := l) T b) := by
  conv_rhs => rw [s1269PrimeFieldUnit_eq_unit_mul_uniformizer_pow (l := l) T b]
  rw [s1269HaarFactor_mul,
    s1124UnitFactorOne_actual (l := l) T b (s1269PrimeUnitField (l := l) T b)
      (s1269PrimeUnitField_norm (l := l) T b),
    one_mul]

theorem s1269HaarFactor_prime_eq_ofReal_uniformizer_pow :
    rootStackHaarFactor (l := l) T b (s1269PrimeFieldUnit (l := l) T b) =
      ENNReal.ofReal
        ((‖(rootStackUniformizerField (l := l) T b :
          rootStackExtension T b)‖ ^ dQpFactor (l := l) T b) ^
          s1269PrimeRamificationExponent (l := l) T b) := by
  rw [s1269HaarFactor_prime_eq_norm_pow (l := l) T b]
  rw [s1269PrimeFieldUnit_norm_eq_uniformizer_pow (l := l) T b]
  congr 1
  rw [← pow_mul, ← pow_mul]
  rw [mul_comm]

theorem s1269UniformizerFactor :
    S1207UniformizerFactor (l := l) T b := by
  unfold S1207UniformizerFactor
  let e := s1269PrimeRamificationExponent (l := l) T b
  have hepos : 0 < e := s1269PrimeRamificationExponent_pos (l := l) T b
  have hpow := s1269HaarFactor_pow (l := l) T b
    (rootStackUniformizerField (l := l) T b) e
  have hprime := s1269HaarFactor_uniformizer_pow_eq_prime (l := l) T b
  have hval := s1269HaarFactor_prime_eq_ofReal_uniformizer_pow (l := l) T b
  have hE : (rootStackHaarFactor (l := l) T b
      (rootStackUniformizerField (l := l) T b)) ^ e =
      ENNReal.ofReal
        (((‖(rootStackUniformizerField (l := l) T b :
          rootStackExtension T b)‖ ^ dQpFactor (l := l) T b)) ^ e) := by
    rw [← hpow, hprime, hval]
  have hne_top : rootStackHaarFactor (l := l) T b
      (rootStackUniformizerField (l := l) T b) ≠ ⊤ := by
    unfold rootStackHaarFactor
    exact ENNReal.coe_ne_top
  have hpos : 0 < (rootStackHaarFactor (l := l) T b
      (rootStackUniformizerField (l := l) T b)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    refine ⟨?_, lt_top_iff_ne_top.mpr hne_top⟩
    unfold rootStackHaarFactor
    exact_mod_cast (distribHaarChar_pos (A := rootStackExtension T b)
      (g := rootStackUniformizerField (l := l) T b))
  have hEreal : ((rootStackHaarFactor (l := l) T b
        (rootStackUniformizerField (l := l) T b)).toReal) ^ e =
      (((‖(rootStackUniformizerField (l := l) T b :
        rootStackExtension T b)‖ ^ dQpFactor (l := l) T b)) ^ e) := by
    have h := congrArg ENNReal.toReal hE
    have hnonneg : (0 : ℝ) ≤ ((‖(rootStackUniformizerField (l := l) T b :
        rootStackExtension T b)‖ ^ dQpFactor (l := l) T b)) ^ e := by positivity
    simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnonneg, hne_top] using h
  have hnonneg : 0 ≤ ((rootStackHaarFactor (l := l) T b
      (rootStackUniformizerField (l := l) T b)).toReal) := le_of_lt hpos
  have hbase_nonneg : 0 ≤ (‖(rootStackUniformizerField (l := l) T b :
      rootStackExtension T b)‖ ^ dQpFactor (l := l) T b) := by positivity
  have hbase := pow_left_inj₀ hnonneg hbase_nonneg (ne_of_gt hepos) |>.mp hEreal
  calc
    rootStackHaarFactor (l := l) T b (rootStackUniformizerField (l := l) T b)
        = ENNReal.ofReal (rootStackHaarFactor (l := l) T b
            (rootStackUniformizerField (l := l) T b)).toReal :=
          (ENNReal.ofReal_toReal hne_top).symm
    _ = ENNReal.ofReal (‖(rootStackUniformizerField (l := l) T b :
          rootStackExtension T b)‖ ^ dQpFactor (l := l) T b) := by rw [hbase]

/-- The S1216 exact first gap is exactly the S1207 uniformizer factor. -/
theorem s1269UniformizerFactorGap :
    S1216UniformizerFactorGap (l := l) T b :=
  s1269UniformizerFactor (l := l) T b

end LeanFormal.IUT.XiFPaper.S1269UniformizerFactorActual

end