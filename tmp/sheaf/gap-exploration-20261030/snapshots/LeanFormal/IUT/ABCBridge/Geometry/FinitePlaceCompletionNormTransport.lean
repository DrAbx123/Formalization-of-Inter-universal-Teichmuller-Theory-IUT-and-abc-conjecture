import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Algebra.Group.Int.TypeTags

/-!
# Relative completion degrees and norm transport for q-pilot arithmetic

For an extension `k -> K` of number fields and a finite place `place` of `K`
above the contracted place of `k`, this file relates the two local completions
`k_v` and `K_w` of the actual completion embedding `completionMap`.

* `relativeRamificationIndex`, `relativeResidueDegree` and
  `relativeCompletionDegree` are the library ramification index `e`, residue
  degree `f` and their product `e * f` at the finite place extension, together
  with the identifications of `f` with the degree of the residue field
  extension and of `e` with Mathlib's `Ideal.ramificationIdx`.
* `completionAlgebra` is the algebra structure of `K_w` over `k_v` induced by
  `completionMap`, with its algebra-map and scalar-action coherences and the
  compatibility of the scalar tower `k -> k_v -> K_w` with the completion
  embedding.
* `span_finBasis_completionAlgebra_eq_top`, `moduleFinite_completionAlgebra`
  and `finrank_completionAlgebra_le_fieldDegree` prove that the `k_v`-span of
  the images of a `k`-basis of `K` is all of `K_w`, that the completion `K_w`
  is a finite module over `k_v`, and that its degree is at most `[K : k]`.
* `norm_completionMap_pow` and `norm_algebraMap_pow` are the norm-transport
  identities: the canonical completion norm of the image of a nonzero element
  is the lower canonical norm raised to the relative degree `e * f`, both for
  elements of the lower completion and for elements of the base number field.
* `logNorm_completionMap_eq_mul`, `logMagnitude_completionMap_eq_mul`,
  `logNorm_algebraMap_eq_mul` and `absoluteDegreeNormalizedLogNorm_completionMap`
  are the logarithmic and absolute-degree-normalized forms consumed by the
  q-pilot normalization chain.

Honest scope. Mathlib 4.32.2 supplies the ramification index `e` and residue
degree `f` at a finite place extension and the global identity summing `e * f`
over a full fiber to the relative degree. The exact equality
`Module.finrank k_v K_w = e * f` is now proved in this development by the
companion modules `AdicCompletionValuationUniqueness` (finiteness of the
completed valuation rings) and `RelativeCompletionFinrankReduction` (the
unconditional identity and the hypothesis-free restatements of the transports
of this file at the actual local degree), which import this file and therefore
cannot be imported back; the audit obligations below record the closure. This
file itself proves `Module.Finite k_v K_w` and `Module.finrank k_v K_w ≤ [K : k]`.
The transport statements are proved for arbitrary nonzero elements of the
actual completions, not only for q-candidates, and no Tate uniformization or
identification with the paper's global q-pilot weights is asserted.
-/

open scoped Valued

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## Relative degree data at a finite-place extension -/

/-- The relative ramification index `e` of an upper finite place over its
contraction, supplied by Mathlib's `ramificationIdx'`. -/
def relativeRamificationIndex (place : NumberField.FinitePlace K) : ℕ :=
  (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
    place.maximalIdeal.asIdeal

/-- The relative residue degree `f` of an upper finite place over its
contraction, supplied by Mathlib's `inertiaDeg'`. -/
def relativeResidueDegree (place : NumberField.FinitePlace K) : ℕ :=
  (comap (k := k) place).maximalIdeal.asIdeal.inertiaDeg'
    place.maximalIdeal.asIdeal

/-- The relative degree `e * f` of the finite place extension. -/
def relativeCompletionDegree (place : NumberField.FinitePlace K) : ℕ :=
  relativeRamificationIndex (k := k) place *
    relativeResidueDegree (k := k) place

theorem relativeRamificationIndex_ne_zero (place : NumberField.FinitePlace K) :
    relativeRamificationIndex (k := k) place ≠ 0 :=
  ramificationIdx_ne_zero (k := k) place

theorem relativeResidueDegree_ne_zero (place : NumberField.FinitePlace K) :
    relativeResidueDegree (k := k) place ≠ 0 := by
  intro residueDegreeZero
  have cardinality :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
      place.maximalIdeal.asIdeal (comap (k := k) place).maximalIdeal.asIdeal
      (comap (k := k) place).maximalIdeal.isPrime
      (comap (k := k) place).maximalIdeal.ne_bot
  rw [show (comap (k := k) place).maximalIdeal.asIdeal.inertiaDeg'
        place.maximalIdeal.asIdeal =
      relativeResidueDegree (k := k) place from rfl,
    residueDegreeZero, pow_zero] at cardinality
  exact (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal))
    cardinality

theorem relativeCompletionDegree_pos (place : NumberField.FinitePlace K) :
    0 < relativeCompletionDegree (k := k) place :=
  Nat.mul_pos
    (Nat.pos_of_ne_zero (relativeRamificationIndex_ne_zero (k := k) place))
    (Nat.pos_of_ne_zero (relativeResidueDegree_ne_zero (k := k) place))

/-- The residue-norm base of the upper place is the `f`-th power of the
residue-norm base of the contracted place. -/
theorem absNorm_eq_pow_relativeResidueDegree (place : NumberField.FinitePlace K) :
    (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) =
      (Ideal.absNorm (comap (k := k) place).maximalIdeal.asIdeal : ℝ) ^
        relativeResidueDegree (k := k) place := by
  have cardinality :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
      place.maximalIdeal.asIdeal (comap (k := k) place).maximalIdeal.asIdeal
      (comap (k := k) place).maximalIdeal.isPrime
      (comap (k := k) place).maximalIdeal.ne_bot
  rw [show (comap (k := k) place).maximalIdeal.asIdeal.inertiaDeg'
        place.maximalIdeal.asIdeal =
      relativeResidueDegree (k := k) place from rfl] at cardinality
  exact_mod_cast cardinality

/-- The library residue degree is the actual degree of the residue field
extension at the finite place. -/
theorem relativeResidueDegree_eq_finrank_residueField
    (place : NumberField.FinitePlace K) :
    relativeResidueDegree (k := k) place =
      Module.finrank
        (NumberField.RingOfIntegers k ⧸
          (comap (k := k) place).maximalIdeal.asIdeal)
        (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal) := by
  letI : (comap (k := k) place).maximalIdeal.asIdeal.IsMaximal :=
    (comap (k := k) place).maximalIdeal.isMaximal
  letI : place.maximalIdeal.asIdeal.IsMaximal := place.maximalIdeal.isMaximal
  unfold relativeResidueDegree
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact Ideal.inertiaDeg_eq_of_isMaximal _ _

/-- The library ramification index is Mathlib's `Ideal.ramificationIdx`. -/
theorem relativeRamificationIndex_eq_ramificationIdx
    (place : NumberField.FinitePlace K) :
    relativeRamificationIndex (k := k) place =
      place.maximalIdeal.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) := by
  unfold relativeRamificationIndex
  exact Ideal.ramificationIdx'_eq_ramificationIdx _ _
    (comap (k := k) place).maximalIdeal.ne_bot

/-! ## The upper completion as an algebra over the lower completion -/

/-- The upper completion as an algebra over the lower completion, through the
actual completion embedding. This is a plain structure value, not a global
instance; put it in scope with `letI := completionAlgebra place`. -/
noncomputable abbrev completionAlgebra (place : NumberField.FinitePlace K) :
    Algebra ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
  (completionMap (k := k) place).toAlgebra

theorem completionAlgebra_algebraMap (place : NumberField.FinitePlace K) :
    letI := completionAlgebra (k := k) place
    algebraMap ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) = completionMap (k := k) place :=
  rfl

theorem completionAlgebra_smul (place : NumberField.FinitePlace K)
    (a : (comap (k := k) place).maximalIdeal.adicCompletion k)
    (x : place.maximalIdeal.adicCompletion K) :
    letI := completionAlgebra (k := k) place
    a • x = completionMap (k := k) place a * x := by
  letI := completionAlgebra (k := k) place
  exact Algebra.smul_def a x

/-- The scalar tower `k -> k_v -> K_w` induced by `completionAlgebra` is
compatible with the completion embedding. -/
theorem isScalarTower_completionAlgebra (place : NumberField.FinitePlace K) :
    letI := completionAlgebra (k := k) place
    IsScalarTower k
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) := by
  letI := completionAlgebra (k := k) place
  refine ⟨fun a b c => ?_⟩
  simp only [Algebra.smul_def, map_mul]
  rw [completionAlgebra_algebraMap (k := k) place]
  rw [show (algebraMap k ((comap (k := k) place).maximalIdeal.adicCompletion k)) a =
      (a : (comap (k := k) place).maximalIdeal.adicCompletion k) from rfl]
  rw [completionMap_coe (k := k) place a]
  rw [show (algebraMap k (place.maximalIdeal.adicCompletion K)) a =
      (algebraMap k K a : place.maximalIdeal.adicCompletion K) from rfl]
  ring

/-! ## Finiteness of the completion extension -/

/-- The `k_v`-span of the images of a `k`-basis of `K` in `K_w` is everything:
a finite-dimensional subspace over the complete field `k_v` is closed, and it
contains the dense image of `K`. -/
theorem span_finBasis_completionAlgebra_eq_top (place : NumberField.FinitePlace K) :
    letI := completionAlgebra (k := k) place
    Submodule.span
        ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (Set.range fun index : Fin (Module.finrank k K) =>
          algebraMap K (place.maximalIdeal.adicCompletion K)
            ((Module.finBasis k K) index)) = ⊤ := by
  classical
  letI := completionAlgebra (k := k) place
  let basis := Module.finBasis k K
  let imageSpan : Submodule
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    Submodule.span ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (Set.range fun index : Fin (Module.finrank k K) =>
        algebraMap K (place.maximalIdeal.adicCompletion K) (basis index))
  haveI hsmul : ContinuousSMul
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    ⟨show Continuous fun p : (comap (k := k) place).maximalIdeal.adicCompletion k ×
          place.maximalIdeal.adicCompletion K => completionMap (k := k) place p.1 * p.2 from
        Continuous.mul
          ((continuous_completionMap (k := k) place).comp continuous_fst)
          continuous_snd⟩
  haveI hfin : FiniteDimensional
      ((comap (k := k) place).maximalIdeal.adicCompletion k) ↥imageSpan :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (imageSpan : Set (place.maximalIdeal.adicCompletion K)) :=
    Submodule.closed_of_finiteDimensional imageSpan
  have hdenseImage :
      Dense (Set.range (algebraMap K (place.maximalIdeal.adicCompletion K))) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K place.maximalIdeal
  have hsubset : Set.range (algebraMap K (place.maximalIdeal.adicCompletion K)) ⊆
      (imageSpan : Set (place.maximalIdeal.adicCompletion K)) := by
    rintro _ ⟨x, rfl⟩
    rw [(basis.sum_repr x).symm, map_sum]
    refine Submodule.sum_mem imageSpan fun index _ => ?_
    have hterm : algebraMap K (place.maximalIdeal.adicCompletion K)
          (basis.repr x index • basis index) =
        completionMap (k := k) place
            ((basis.repr x index : k) :
              (comap (k := k) place).maximalIdeal.adicCompletion k) *
          algebraMap K (place.maximalIdeal.adicCompletion K) (basis index) := by
      rw [Algebra.smul_def, map_mul, completionMap_coe]
      congr 1
    rw [hterm]
    exact Submodule.smul_mem imageSpan _
      (Submodule.subset_span ⟨index, rfl⟩)
  have hdense : Dense (imageSpan : Set (place.maximalIdeal.adicCompletion K)) :=
    Dense.mono hsubset hdenseImage
  have htop : imageSpan = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ closure (imageSpan : Set (place.maximalIdeal.adicCompletion K)) :=
      hdense x
    rwa [hclosed.closure_eq] at hx
  exact htop

/-- The upper completion is a finite module over the lower completion. -/
theorem moduleFinite_completionAlgebra (place : NumberField.FinitePlace K) :
    letI := completionAlgebra (k := k) place
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) := by
  classical
  letI := completionAlgebra (k := k) place
  have hspan := span_finBasis_completionAlgebra_eq_top (k := k) place
  have hfg : (Submodule.span
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (Set.range fun index : Fin (Module.finrank k K) =>
        algebraMap K (place.maximalIdeal.adicCompletion K)
          ((Module.finBasis k K) index))).FG :=
    Submodule.fg_span (Set.finite_range _)
  haveI hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      ↥(Submodule.span
        ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (Set.range fun index : Fin (Module.finrank k K) =>
          algebraMap K (place.maximalIdeal.adicCompletion K)
            ((Module.finBasis k K) index))) :=
    Module.Finite.iff_fg.mpr hfg
  refine Module.Finite.of_surjective
    (Submodule.subtype (Submodule.span
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (Set.range fun index : Fin (Module.finrank k K) =>
        algebraMap K (place.maximalIdeal.adicCompletion K)
          ((Module.finBasis k K) index)))) ?_
  intro x
  exact ⟨⟨x, by rw [hspan]; exact Submodule.mem_top⟩, rfl⟩

/-- The degree of the completion extension is at most the global degree. -/
theorem finrank_completionAlgebra_le_fieldDegree (place : NumberField.FinitePlace K) :
    letI := completionAlgebra (k := k) place
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) ≤ Module.finrank k K := by
  classical
  letI := completionAlgebra (k := k) place
  have hspan := span_finBasis_completionAlgebra_eq_top (k := k) place
  haveI : Fintype ↑(Set.range fun index : Fin (Module.finrank k K) =>
      algebraMap K (place.maximalIdeal.adicCompletion K)
        ((Module.finBasis k K) index)) :=
    Set.fintypeRange _
  have hcard : (Set.toFinset (Set.range fun index : Fin (Module.finrank k K) =>
      algebraMap K (place.maximalIdeal.adicCompletion K)
        ((Module.finBasis k K) index))).card ≤ Module.finrank k K := by
    rw [Set.toFinset_range]
    calc ((Finset.univ : Finset (Fin (Module.finrank k K))).image
          fun index : Fin (Module.finrank k K) =>
            algebraMap K (place.maximalIdeal.adicCompletion K)
              ((Module.finBasis k K) index)).card
        ≤ (Finset.univ : Finset (Fin (Module.finrank k K))).card := Finset.card_image_le
      _ = Module.finrank k K := by simp
  calc Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K)
      = Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          ↥(⊤ : Submodule
            ((comap (k := k) place).maximalIdeal.adicCompletion k)
            (place.maximalIdeal.adicCompletion K)) :=
        (finrank_top _ _).symm
      _ = Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          ↥(Submodule.span
            ((comap (k := k) place).maximalIdeal.adicCompletion k)
            (Set.range fun index : Fin (Module.finrank k K) =>
              algebraMap K (place.maximalIdeal.adicCompletion K)
                ((Module.finBasis k K) index))) := by
        rw [← hspan]
      _ ≤ (Set.toFinset (Set.range fun index : Fin (Module.finrank k K) =>
              algebraMap K (place.maximalIdeal.adicCompletion K)
                ((Module.finBasis k K) index))).card :=
        finrank_span_le_card _
      _ ≤ Module.finrank k K := hcard

/-! ## Norm and valuation transport along the completion embedding -/

/-- A nonzero element of a completed finite place has nonzero valuation. -/
theorem valuation_ne_zero_of_ne_zero {F : Type u} [Field F] [NumberField F]
    (P : NumberField.FinitePlace F) (x : P.maximalIdeal.adicCompletion F)
    (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative Int)) ≠ 0 :=
  fun h =>
    hx (((Valued.v :
      Valuation (P.maximalIdeal.adicCompletion F)
        (WithZero (Multiplicative Int))).map_eq_zero_iff).mp h)

/-- Base-field elements remain nonzero in the lower completion. -/
theorem algebraMap_completion_ne_zero (place : NumberField.FinitePlace K)
    (a : k) (ha : a ≠ 0) :
    (a : (comap (k := k) place).maximalIdeal.adicCompletion k) ≠ 0 :=
  fun hzero =>
    ha (FaithfulSMul.algebraMap_injective k
      ((comap (k := k) place).maximalIdeal.adicCompletion k) (by
        rw [map_zero]
        exact hzero))

/-- Additive valuation transport: the discrete exponent of the image of a
nonzero element is the lower exponent multiplied by the ramification index. -/
theorem toAdd_valuation_completionMap (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0)
    (hmap : completionMap (k := k) place x ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero
        (valuation_ne_zero_of_ne_zero place (completionMap (k := k) place x) hmap)) =
      relativeRamificationIndex (k := k) place *
        Multiplicative.toAdd (WithZero.unzero
          (valuation_ne_zero_of_ne_zero (comap (k := k) place) x hx)) := by
  have hunzero :
      WithZero.unzero (valuation_ne_zero_of_ne_zero place
          (completionMap (k := k) place x) hmap) =
        WithZero.unzero (valuation_ne_zero_of_ne_zero (comap (k := k) place) x hx) ^
          relativeRamificationIndex (k := k) place := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    exact (valuation_completionMap (k := k) place x).symm
  rw [hunzero, Int.toAdd_pow, mul_comm]

/-- The canonical completion norm is the residue-norm base raised to the
discrete valuation exponent. -/
theorem norm_eq_absNorm_zpow {F : Type u} [Field F] [NumberField F]
    (P : NumberField.FinitePlace F) (x : P.maximalIdeal.adicCompletion F)
    (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm P.maximalIdeal.asIdeal : ℝ) ^
      (Multiplicative.toAdd (WithZero.unzero
        (valuation_ne_zero_of_ne_zero P x hx))) := by
  rw [NumberField.FinitePlace.norm_def P.maximalIdeal,
    WithZeroMulInt.toNNReal_neg_apply _
      (valuation_ne_zero_of_ne_zero P x hx),
    NNReal.coe_zpow]
  simp

/-- Logarithmic form of the norm formula. -/
theorem logNorm_eq_absNorm_mul {F : Type u} [Field F] [NumberField F]
    (P : NumberField.FinitePlace F) (x : P.maximalIdeal.adicCompletion F)
    (hx : x ≠ 0) :
    Real.log ‖x‖ =
      (Multiplicative.toAdd (WithZero.unzero
          (valuation_ne_zero_of_ne_zero P x hx))) *
        Real.log (Ideal.absNorm P.maximalIdeal.asIdeal : ℝ) := by
  rw [norm_eq_absNorm_zpow P x hx, Real.log_zpow]

/-- Log of the upper residue-norm base is `f` times the lower one. -/
theorem log_absNorm_eq_relativeResidueDegree_mul (place : NumberField.FinitePlace K) :
    Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) =
      (relativeResidueDegree (k := k) place : ℝ) *
        Real.log (Ideal.absNorm (comap (k := k) place).maximalIdeal.asIdeal : ℝ) := by
  rw [absNorm_eq_pow_relativeResidueDegree (k := k) place, Real.log_pow]

/-- Logarithmic norm transport: the logarithmic norm of the image of a
nonzero element is the lower logarithmic norm scaled by `e * f`. -/
theorem logNorm_completionMap_eq_mul (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    Real.log ‖completionMap (k := k) place x‖ =
      (relativeCompletionDegree (k := k) place : ℝ) * Real.log ‖x‖ := by
  have hmap : completionMap (k := k) place x ≠ 0 :=
    fun h => hx (completionMap_injective (k := k) place (by simpa using h))
  rw [logNorm_eq_absNorm_mul place (completionMap (k := k) place x) hmap,
    logNorm_eq_absNorm_mul (comap (k := k) place) x hx,
    toAdd_valuation_completionMap (k := k) place x hx hmap,
    log_absNorm_eq_relativeResidueDegree_mul (k := k) place]
  have hdegree_cast : (relativeCompletionDegree (k := k) place : ℝ) =
      (relativeRamificationIndex (k := k) place : ℝ) *
        (relativeResidueDegree (k := k) place : ℝ) := by
    rw [relativeCompletionDegree, Nat.cast_mul]
  rw [hdegree_cast]
  push_cast
  ring

/-- Norm transport: the canonical completion norm of the image of a nonzero
element of the lower completion is the lower norm raised to `e * f`. -/
theorem norm_completionMap_pow (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    ‖completionMap (k := k) place x‖ =
      ‖x‖ ^ relativeCompletionDegree (k := k) place := by
  have hmap : completionMap (k := k) place x ≠ 0 :=
    fun h => hx (completionMap_injective (k := k) place (by simpa using h))
  calc ‖completionMap (k := k) place x‖
      = Real.exp (Real.log ‖completionMap (k := k) place x‖) :=
        (Real.exp_log (norm_pos_iff.mpr hmap)).symm
    _ = Real.exp ((relativeCompletionDegree (k := k) place : ℝ) * Real.log ‖x‖) := by
        rw [logNorm_completionMap_eq_mul (k := k) place x hx]
    _ = Real.exp (Real.log ‖x‖) ^ relativeCompletionDegree (k := k) place :=
        Real.exp_nat_mul (Real.log ‖x‖) (relativeCompletionDegree (k := k) place)
    _ = ‖x‖ ^ relativeCompletionDegree (k := k) place := by
        rw [Real.exp_log (norm_pos_iff.mpr hx)]

/-- Norm transport on elements of the base number field. -/
theorem norm_algebraMap_pow (place : NumberField.FinitePlace K) (a : k) (ha : a ≠ 0) :
    ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ ^
        relativeCompletionDegree (k := k) place := by
  rw [← completionMap_coe (k := k) place a]
  exact norm_completionMap_pow (k := k) place _
    (algebraMap_completion_ne_zero (k := k) place a ha)

/-- Logarithmic magnitude transport with the sign convention `-log‖-‖` of the
q-pilot normalization chain. -/
theorem logMagnitude_completionMap_eq_mul (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    -Real.log ‖completionMap (k := k) place x‖ =
      (relativeCompletionDegree (k := k) place : ℝ) * (-Real.log ‖x‖) := by
  rw [logNorm_completionMap_eq_mul (k := k) place x hx]
  ring

/-- Logarithmic norm transport on elements of the base number field. -/
theorem logNorm_algebraMap_eq_mul (place : NumberField.FinitePlace K)
    (a : k) (ha : a ≠ 0) :
    Real.log ‖(algebraMap k K a : place.maximalIdeal.adicCompletion K)‖ =
      (relativeCompletionDegree (k := k) place : ℝ) *
        Real.log ‖(a : (comap (k := k) place).maximalIdeal.adicCompletion k)‖ := by
  rw [norm_algebraMap_pow (k := k) place a ha, Real.log_pow]

/-- Absolute-degree-normalized logarithmic transport: dividing the upper
logarithmic norm by the absolute degree `[K : ℚ]` equals the lower
logarithmic norm divided by `[k : ℚ]`, scaled by the fraction
`e * f / [K : k]` of the relative degree. -/
theorem absoluteDegreeNormalizedLogNorm_completionMap (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    Real.log ‖completionMap (k := k) place x‖ / (Module.finrank ℚ K : ℝ) =
      ((relativeCompletionDegree (k := k) place : ℝ) / (Module.finrank k K : ℝ)) *
        (Real.log ‖x‖ / (Module.finrank ℚ k : ℝ)) := by
  have degree_eq_nat : Module.finrank ℚ K =
      Module.finrank k K * Module.finrank ℚ k :=
    (Module.finrank_mul_finrank ℚ k K).symm.trans (mul_comm _ _)
  have degree_eq : (Module.finrank ℚ K : ℝ) =
      (Module.finrank k K : ℝ) * (Module.finrank ℚ k : ℝ) := by
    rw [degree_eq_nat, Nat.cast_mul]
  have relative_ne_zero : (Module.finrank k K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k) (M := K)).ne'
  have absolute_ne_zero : (Module.finrank ℚ k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := k)).ne'
  rw [logNorm_completionMap_eq_mul (k := k) place x hx, degree_eq]
  field_simp

/-! ## The relative completion finrank identity: consumption is downstream

The companion module `FinitePlaceCompletionLocalInputs` proves the identity
`Module.finrank k_v K_w = relativeCompletionDegree` of this file, conditionally
on the unique-extension statement `IsIntegralClosure O_w O_v K_w`; the gap-A
finiteness input is now proved unconditionally in
`AdicCompletionValuationUniqueness` (`moduleFinite_adicCompletionIntegers`), and
the unconditional identity
`finrank_adicCompletion_eq_relativeCompletionDegree_unconditional` together
with the hypothesis-free restatements of the transports of this file at the
actual local degree `Module.finrank k_v K_w` are assembled in
`RelativeCompletionFinrankReduction`. Because those companion modules import
this file, the restatements cannot be imported back and live there, under the
same names as the conditional bridges that previously stood here. -/

end

end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finitePlaceCompletionNormTransport : Obligation :=
  { id := "Foundations.NumberField.finite-place-completion-norm-transport"
    source :=
      "Standard ramification and completion theory; IUT III q-pilot normalization prerequisites"
    status := VerificationStatus.proved
    note :=
      "The relative ramification index and residue degree of a finite-place " ++
        "extension are identified with Mathlib\'s Ideal.ramificationIdx and " ++
        "with the actual degree of the residue field extension. The upper " ++
        "completion is given its algebra structure over the lower completion " ++
        "through the actual completion embedding, with the scalar tower " ++
        "k -> k_v -> K_w shown compatible with the embedding. The image of a " ++
        "k-basis of K spans the upper completion over the lower completion, " ++
        "because a finite-dimensional subspace over the complete field k_v " ++
        "is closed and it contains the dense image of K; consequently the " ++
        "upper completion is a finite module over the lower completion with " ++
        "degree at most the global degree. The additive valuation exponent " ++
        "of a nonzero element is proved to scale by the ramification index. " ++
        "The canonical completion norm of the image of any nonzero element " ++
        "is proved to be the lower canonical norm raised to the relative " ++
        "degree e * f; the logarithmic, signed magnitude and " ++
        "absolute-degree-normalized forms of this identity are proved for " ++
        "arbitrary nonzero elements, refining the q-candidate statements of " ++
        "the IUT III files. No Tate uniformization or global q-pilot weight " ++
        "identification is asserted."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-extension",
        "Foundations.NumberField.local-q-parameter-extension" ] }

def relativeCompletionFinrank : Obligation :=
  { id := "Foundations.NumberField.relative-completion-finrank"
    source :=
      "Fundamental identity [L : K] = e * f for complete discretely valued fields " ++
        "(Serre, Local Fields, II.2)"
    status := VerificationStatus.proved
    note :=
      "The exact identity Module.finrank k_v K_w = e * f is proved in this " ++
        "development: the finiteness of the completed valuation rings over " ++
        "one another (Module.Finite for O_v -> O_w, equivalently " ++
        "IsIntegralClosure O_w O_v K_w) is proved unconditionally in " ++
        "AdicCompletionValuationUniqueness.moduleFinite_adicCompletionIntegers " ++
        "by the density/compactness argument, and together with the " ++
        "unconditional local data agreement " ++
        "localDataAgreesWithPlaceData_adicCompletion the identity is assembled " ++
        "in RelativeCompletionFinrankReduction as " ++
        "finrank_adicCompletion_eq_relativeCompletionDegree_unconditional and " ++
        "finrank_adicCompletion_eq_ramificationIndex_mul_residueDegree_" ++
        "unconditional. The implication used is Mathlib\'s " ++
        "Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing at the completed " ++
        "valuation rings. The identity is not assumed anywhere; it is consumed " ++
        "downstream of this file."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-completion-norm-transport" ] }

def relativeCompletionFinrankWiring : Obligation :=
  { id := "Foundations.NumberField.relative-completion-finrank-wiring"
    source :=
      "Unconditional consumption of the fundamental identity [K_w : k_v] = e * f " ++
        "(Serre, Local Fields, II.2) for the q-pilot normalization chain"
    status := VerificationStatus.proved
    note :=
      "The transport identities of this file are stated with the relative " ++
        "degree e * f of the finite-place extension. They are restated " ++
        "hypothesis-free at the actual local degree Module.finrank k_v K_w in " ++
        "RelativeCompletionFinrankReduction under the same names: " ++
        "norm_completionMap_pow_of_finrank_eq_relativeCompletionDegree, " ++
        "norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree, " ++
        "logNorm_completionMap_eq_mul_of_finrank_eq_relativeCompletionDegree, " ++
        "logMagnitude_completionMap_eq_mul_of_finrank_eq_" ++
        "relativeCompletionDegree, " ++
        "logNorm_algebraMap_eq_mul_of_finrank_eq_relativeCompletionDegree and " ++
        "absoluteDegreeNormalizedLogNorm_completionMap_of_finrank_eq_" ++
        "relativeCompletionDegree. Each proof rewrites by the proved identity " ++
        "finrank_adicCompletion_eq_relativeCompletionDegree_unconditional; gap A " ++
        "finiteness is AdicCompletionValuationUniqueness.moduleFinite_" ++
        "adicCompletionIntegers and the local data agreement is " ++
        "localDataAgreesWithPlaceData_adicCompletion. The conditional bridges " ++
        "previously stated in this file are replaced by these unconditional " ++
        "forms; the obligation relativeCompletionFinrank above is discharged."
    dependsOn :=
      [ "Foundations.NumberField.relative-completion-finrank" ] }

end LeanFormal.IUT.Audit
