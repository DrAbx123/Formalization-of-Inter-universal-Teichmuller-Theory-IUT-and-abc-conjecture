/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-! # A655/A660 hull: INVERSE bad-prime scaling law (product measure)

Uses green `PaperRootExtensionHaarFactorActual.rootHaarFactor` (multiplicative,
unit-trivial; prime factor = norm^d) and the one-dimensional inverse
prime-scaling formulas.

* `prime_inv_smul_measure`, `prime_pow_inv_smul_measure`: for ANY local set,
  `μ_b (((p_b)^e)⁻¹ • S) = ((ofReal primeFactor_b)^e)⁻¹ * μ_b S`;
* `localInvFactor` = Haar factor of the inverse scalar at a bad place;
* `badInvScale` = coordinatewise inverse scaling;
* `badInvScale_measure`: for a product region `Set.pi univ S`,
  `μ (badInvScale N '' pi S) = (∏_b localInvFactor_b) * μ (pi S)`.

Direction: inverse scaling increases the product Haar by the bad-support factor
`∏_b p_b^{e_b d_b}`; multiplication by `N` gives the opposite sign.  No canonical
object is changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators NNReal

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem prime_inv_smul_measure (b : Bad (nativePlaceSelection T))
    (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S) =
      (ENNReal.ofReal (primeFactor T b))⁻¹ * rootExtensionHaar T b S := by
  have hp_ne : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)
  have hsm := rootPrime_smul_measure (T := T) (b := b)
    (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S)
  rw [smul_inv_smul₀ hp_ne S] at hsm
  have hfac0 : ENNReal.ofReal (primeFactor T b) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (primeFactor_pos T b)
  have hfacT : ENNReal.ofReal (primeFactor T b) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfac_eq : ENNReal.ofReal (primeFactor T b) =
      ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
        (qVFamTensorP T b) : rootNormedExtension T b)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := rfl
  rw [hsm, ← hfac_eq]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hfac0 hfacT, one_mul]

theorem prime_pow_inv_smul_measure (b : Bad (nativePlaceSelection T)) (e : ℕ)
    (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        ((((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ e)⁻¹) • S) =
      ((ENNReal.ofReal (primeFactor T b)) ^ e)⁻¹ * rootExtensionHaar T b S := by
  induction e generalizing S with
  | zero => simp
  | succ n ih =>
      have hp_ne : (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)
      have hscalar : (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (n + 1))⁻¹) =
          ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ n)⁻¹ *
            ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) := by
        rw [pow_succ, mul_inv_rev, mul_comm]
      rw [hscalar, mul_smul]
      rw [ih (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S)]
      rw [prime_inv_smul_measure T b]
      have hf0 : ENNReal.ofReal (primeFactor T b) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le.mpr (primeFactor_pos T b)
      have hfT : ENNReal.ofReal (primeFactor T b) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hfacpow : ((ENNReal.ofReal (primeFactor T b)) ^ (n + 1))⁻¹ =
          ((ENNReal.ofReal (primeFactor T b)) ^ n)⁻¹ *
            (ENNReal.ofReal (primeFactor T b))⁻¹ := by
        rw [pow_succ,
          ENNReal.mul_inv (Or.inl (pow_ne_zero _ hf0)) (Or.inl (ENNReal.pow_ne_top hfT)),
          mul_comm]
      rw [hfacpow, mul_assoc]

/-! ## Local Haar factor of the inverse scalar at a bad place -/

noncomputable def invScalarElem {N : ℕ} (hN : 0 < N) (b : Bad (nativePlaceSelection T)) :
    rootNormedExtension T b :=
  (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
    (((N : ℕ) : ℚ_[(qVFamTensorP T b)])))⁻¹

noncomputable def invScalarUnit {N : ℕ} (hN : 0 < N) (b : Bad (nativePlaceSelection T)) :
    (rootNormedExtension T b)ˣ :=
  Units.mk0 (invScalarElem T hN b) (inv_ne_zero (by
    intro h
    exact (Nat.cast_ne_zero.mpr hN.ne')
      ((FaithfulSMul.algebraMap_injective ℚ_[(qVFamTensorP T b)]
        (rootNormedExtension T b)) (by simpa using h))))

noncomputable def localInvFactor {N : ℕ} (hN : 0 < N)
    (b : Bad (nativePlaceSelection T)) : ENNReal :=
  rootHaarFactor T b (invScalarUnit T hN b)

theorem localInv_smul_measure {N : ℕ} (hN : 0 < N)
    (b : Bad (nativePlaceSelection T)) (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b (invScalarElem T hN b • S) =
      localInvFactor T hN b * rootExtensionHaar T b S := by
  have h := distribHaarChar_mul (μ := rootExtensionHaar T b)
    (g := invScalarUnit T hN b) (s := S)
  unfold localInvFactor rootHaarFactor
  exact h.symm

/-! ## Coordinatewise inverse scaling on product regions -/

noncomputable def badInvScale {N : ℕ} (hN : 0 < N) : S1902Carrier T → S1902Carrier T :=
  fun x b => invScalarElem T hN b * x b

theorem badInvScale_image_pi {N : ℕ} (hN : 0 < N)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    badInvScale T hN '' Set.pi Set.univ S =
      Set.pi Set.univ (fun b => invScalarElem T hN b • S b) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro b _
    exact ⟨y b, hy b (Set.mem_univ b), rfl⟩
  · intro hx
    refine ⟨fun b => (invScalarElem T hN b)⁻¹ * x b, ?_, ?_⟩
    · intro b _
      rcases hx b (Set.mem_univ b) with ⟨z, hz, hz_eq⟩
      have hne : invScalarElem T hN b ≠ 0 := by
        unfold invScalarElem
        exact inv_ne_zero (by
          intro h
          exact (Nat.cast_ne_zero.mpr hN.ne')
            ((FaithfulSMul.algebraMap_injective ℚ_[(qVFamTensorP T b)]
              (rootNormedExtension T b)) (by simpa using h)))
      dsimp only
      rcases hx b (Set.mem_univ b) with ⟨z, hz, hz_eq⟩
      have hz_eq' : invScalarElem T hN b * z = x b := by
        simpa [smul_eq_mul] using hz_eq
      rw [← hz_eq']
      rw [show (invScalarElem T hN b)⁻¹ * (invScalarElem T hN b * z) = z from by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]]
      exact hz
    · funext b
      have hne : invScalarElem T hN b ≠ 0 := by
        unfold invScalarElem
        exact inv_ne_zero (by
          intro h
          exact (Nat.cast_ne_zero.mpr hN.ne')
            ((FaithfulSMul.algebraMap_injective ℚ_[(qVFamTensorP T b)]
              (rootNormedExtension T b)) (by simpa using h)))
      unfold badInvScale
      change invScalarElem T hN b * ((invScalarElem T hN b)⁻¹ * x b) = x b
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem badInvScale_measure {N : ℕ} (hN : 0 < N)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T hN '' Set.pi Set.univ S) =
      (∏ b : Bad (nativePlaceSelection T), localInvFactor T hN b) *
        rootExtensionProductHaar T (Set.pi Set.univ S) := by
  rw [badInvScale_image_pi T hN S]
  rw [rootExtensionProductHaar, Measure.pi_pi, Measure.pi_pi]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => localInv_smul_measure T hN b (S b)

/-- Real form of the product measure law. -/
theorem badInvScale_measure_toReal {N : ℕ} (hN : 0 < N)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    (rootExtensionProductHaar T
        (badInvScale T hN '' Set.pi Set.univ S)).toReal =
      (∏ b : Bad (nativePlaceSelection T), (localInvFactor T hN b).toReal) *
        (rootExtensionProductHaar T (Set.pi Set.univ S)).toReal := by
  rw [badInvScale_measure T hN S, ENNReal.toReal_mul, ENNReal.toReal_prod]

/-- Log form (bad-support): log-volume increases by the sum of the local factors' logs. -/
theorem badInvScale_log_measure {N : ℕ} (hN : 0 < N)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hpos : rootExtensionProductHaar T (Set.pi Set.univ S) ≠ 0)
    (hfin : rootExtensionProductHaar T (Set.pi Set.univ S) < ⊤) :
    Real.log (rootExtensionProductHaar T
        (badInvScale T hN '' Set.pi Set.univ S)).toReal =
      Real.log (rootExtensionProductHaar T (Set.pi Set.univ S)).toReal +
        ∑ b : Bad (nativePlaceSelection T), Real.log (localInvFactor T hN b).toReal := by
  have hfacpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (localInvFactor T hN b).toReal := by
    intro b
    unfold localInvFactor rootHaarFactor
    exact ENNReal.toReal_pos
      (ENNReal.coe_ne_zero.mpr (distribHaarChar_pos
        (A := rootNormedExtension T b) (g := invScalarUnit T hN b)).ne')
      ENNReal.coe_ne_top
  have hfac0 : (∏ b : Bad (nativePlaceSelection T),
      (localInvFactor T hN b).toReal) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => (hfacpos b).ne'
  have hmu0 : (rootExtensionProductHaar T (Set.pi Set.univ S)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos (ne_of_lt hfin)).ne'
  rw [badInvScale_measure_toReal T hN S]
  rw [Real.log_mul hfac0 hmu0]
  rw [Real.log_prod]
  · ring
  · intro b _
    exact (hfacpos b).ne'
def scalingDirectionRows : List (String × String × String) :=
  [ ("1D inverse prime measure", "prime_inv_smul_measure", "PROVED"),
    ("1D inverse prime power measure", "prime_pow_inv_smul_measure", "PROVED"),
    ("local inverse factor measure", "localInv_smul_measure", "PROVED (rootHaarFactor)"),
    ("product inverse measure", "badInvScale_measure", "PROVED (pi_pi)"),
    ("product inverse measure (real)", "badInvScale_measure_toReal", "PROVED"),
    ("log law (bad-support sum)", "badInvScale_log_measure", "PROVED"),
    ("direction", "inverse scaling increases volume; canonical tripleScale shrinks", "STRUCTURAL") ]

theorem scalingDirectionRows_length : scalingDirectionRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual.prime_inv_smul_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual.prime_pow_inv_smul_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual.badInvScale_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual.badInvScale_measure_toReal
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual.badInvScale_log_measure

end LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual

end