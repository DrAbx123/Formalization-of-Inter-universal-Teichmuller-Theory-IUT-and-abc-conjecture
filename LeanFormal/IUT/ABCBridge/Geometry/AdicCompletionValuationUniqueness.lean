import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Attack on gap (A): finiteness of the completed valuation rings

The remaining input of the local fundamental identity `[K_w : k_v] = e * f` is the
finiteness of the completed upper valuation ring over the completed lower one,
equivalently that `𝒪_w` is the integral closure of `𝒪_v` in `K_w`. This file attacks
that input directly, without using uniqueness of the extension of the complete
valuation.

The strategy is the classical density argument, avoiding all circularity:

* `exists_ringOfIntegers_sub_valued_le`: for a Dedekind domain `R` with fraction
  field `F` and height-one prime `v`, the image of `R` in the completed valuation
  ring `𝒪_v` is dense modulo every power of the valuation ideal. The proof composes
  the density of `F` in the completion with the Mathlib density
  `exists_valuation_sub_lt_of_integer` of `R` in the valuation ring of `F`.
* `compactSpace_adicCompletionIntegers`: the completed valuation ring of a number
  field at a finite place is compact; via the criterion
  `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
  this reduces to completeness (closed in the complete completion), the discrete
  valuation ring instance, and finiteness of the residue field, the latter obtained
  from the number-ring quotient `𝓞 k ⧸ v` through the residue isomorphism of the
  adic completion.
* `isClosed_span_range_algebraMap_adicCompletion`: the `𝒪_v`-span of the images of
  any finite family of integral elements is closed in the completion, being the
  continuous image of the compact power of `𝒪_v`.
* `moduleFinite_adicCompletionIntegers`: the main theorem: if a generating family of
  `𝓞 K` over `ℤ` is chosen, the image span is simultaneously dense (by the density
  lemma) and closed (by the compactness argument) in `K_w`, inside the closed unit
  ball `𝒪_w`; hence the span equals `𝒪_w` and `𝒪_w` is a finite `𝒪_v`-module.
-/

set_option maxHeartbeats 3200000

open scoped Valued Topology
open WithZero

namespace LeanFormal.IUT.NumberFieldFinitePlace

universe u v

/-! ## Density of the number ring in a completed valuation ring -/

section RingOfIntegersDensity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The image of the number ring `R` is dense in the completed valuation ring
`𝒪_v` modulo every power of the valuation ideal: every element of `𝒪_v` can be
approximated by an element of `R` with error of valuation at most `exp (-n)`. -/
theorem exists_ringOfIntegers_sub_valued_le
    (v : IsDedekindDomain.HeightOneSpectrum R) (x : v.adicCompletionIntegers F) (n : ℕ) :
    ∃ a : R, Valued.v (((x - algebraMap R (v.adicCompletionIntegers F) a) :
        v.adicCompletionIntegers F) : v.adicCompletion F) ≤
      WithZero.exp (-(n : ℤ)) := by
  have hγpos : 0 < WithZero.exp (-((n : ℤ) + 1)) := WithZero.exp_pos
  obtain ⟨y, hy⟩ := exists_completion_sub_algebraMap_lt v (x : v.adicCompletion F) hγpos
  have hγle : WithZero.exp (-((n : ℤ) + 1)) ≤ 1 :=
    WithZero.exp_le_exp.mpr (by omega)
  have hy_int : v.valuation F y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (k := y)]
    have hx_le : Valued.v ((x : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R F v).mp x.2
    calc Valued.v (algebraMap F (v.adicCompletion F) y)
        = Valued.v ((algebraMap F (v.adicCompletion F) y - (x : v.adicCompletion F)) +
            (x : v.adicCompletion F)) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) y - (x : v.adicCompletion F)))
            (Valued.v ((x : v.adicCompletionIntegers F) : v.adicCompletion F)) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by
        refine max_le ?_ hx_le
        rw [Valuation.map_sub_swap]
        exact hy.le.trans hγle
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v
    hy_int (Units.mk0 (WithZero.exp (-((n : ℤ) + 1))) WithZero.exp_ne_zero)
  refine ⟨a, ?_⟩
  have ha' : v.valuation F (algebraMap R F a - y) < WithZero.exp (-((n : ℤ) + 1)) := by
    simpa only [Units.val_mk0] using ha
  have hcoea : ((algebraMap R (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) :
      v.adicCompletion F) = (algebraMap R F a : v.adicCompletion F) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  have hcoe : (((x - algebraMap R (v.adicCompletionIntegers F) a) :
        v.adicCompletionIntegers F) : v.adicCompletion F) =
      (x : v.adicCompletion F) - (algebraMap R F a : v.adicCompletion F) := by
    rw [← hcoea]
    rfl
  have hcoey : (algebraMap R F a : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap R F a) := rfl
  have hsplit : (x : v.adicCompletion F) - (algebraMap R F a : v.adicCompletion F) =
      ((x : v.adicCompletion F) - algebraMap F (v.adicCompletion F) y) +
        (algebraMap F (v.adicCompletion F) y -
          algebraMap F (v.adicCompletion F) (algebraMap R F a)) := by
    rw [hcoey]
    ring
  rw [hcoe, hsplit]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · exact hy.le.trans (WithZero.exp_le_exp.mpr (by omega))
  · have h2 : Valued.v (algebraMap F (v.adicCompletion F) y -
        algebraMap F (v.adicCompletion F) (algebraMap R F a)) =
        v.valuation F (algebraMap R F a - y) := by
      rw [← map_sub]
      rw [show algebraMap F (v.adicCompletion F) (y - algebraMap R F a) =
          ((y - algebraMap R F a : F) : v.adicCompletion F) from rfl]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
        (k := y - algebraMap R F a)]
      exact Valuation.map_sub_swap (v.valuation F) y (algebraMap R F a)
    rw [h2]
    exact ha'.le.trans (WithZero.exp_le_exp.mpr (by omega))

end RingOfIntegersDensity

/-! ## Compactness of the completed valuation ring -/

section Compactness

variable {k : Type u} [Field k] [NumberField k]
variable {K : Type v} [Field K] [NumberField K] [Algebra k K]

/-- The completed valuation ring of a number field at a finite place is compact:
it is complete (as a closed subring of the complete completion), a discrete
valuation ring, and its residue field is finite, being the residue field of the
number ring at the place. -/
theorem compactSpace_adicCompletionIntegers (place : NumberField.FinitePlace K) :
    CompactSpace ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) := by
  haveI hrank :
      (Valued.v : Valuation ((comap (k := k) place).maximalIdeal.adicCompletion k) ℤᵐ⁰).RankOne :=
    inferInstance
  change CompactSpace (𝒪[((comap (k := k) place).maximalIdeal.adicCompletion k)])
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, ?_⟩
  · rw [completeSpace_iff_isComplete_univ, Subtype.isComplete_iff]
    rw [Set.image_univ, Subtype.range_coe]
    exact (Valued.isClosed_integer ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (Γ₀ := ℤᵐ⁰)).isComplete
  · change IsDiscreteValuationRing
      ↥((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
    infer_instance
  · haveI hfin : Finite (NumberField.RingOfIntegers k ⧸
        (comap (k := k) place).maximalIdeal.asIdeal) :=
      (Ideal.absNorm_ne_zero_iff _).mp
        (Ideal.absNorm_eq_zero_iff.not.mpr (comap (k := k) place).maximalIdeal.ne_bot)
    exact Finite.of_equiv _ (residueEquivAdicCompletionIntegers_comap (k := k) place).toEquiv

end Compactness

/-! ## Closedness of the image span of a finite family of integral elements -/

section ImageSpan

variable {k : Type u} [Field k] [NumberField k]
variable {K : Type v} [Field K] [NumberField K] [Algebra k K]

/-- The `𝒪_v`-span of the images in `K_w` of a finite family of elements of `𝓞 K`
is closed in `K_w`: it is the image of the compact space `𝒪_v^r` under the
continuous multiplication map. -/
theorem isClosed_span_range_algebraMap_adicCompletion
    (place : NumberField.FinitePlace K) (r : ℕ) (b : Fin r → NumberField.RingOfIntegers K) :
    IsClosed ((Submodule.span
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (Set.range fun i => (algebraMap (NumberField.RingOfIntegers K) K (b i) :
        place.maximalIdeal.adicCompletion K)) :
          Set (place.maximalIdeal.adicCompletion K))) := by
  classical
  haveI hcompact := compactSpace_adicCompletionIntegers (k := k) place
  let m : Fin r → place.maximalIdeal.adicCompletion K := fun i =>
    (algebraMap (NumberField.RingOfIntegers K) K (b i) : place.maximalIdeal.adicCompletion K)
  let Ψ : (Fin r → (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) →
      place.maximalIdeal.adicCompletion K := fun u =>
    ∑ i, ((completionIntegersMap (k := k) place (u i) :
      place.maximalIdeal.adicCompletionIntegers K) : place.maximalIdeal.adicCompletion K) *
        m i
  have hcont : Continuous Ψ := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    refine Continuous.mul ?_ continuous_const
    have h₁ : Continuous fun u : Fin r →
        (comap (k := k) place).maximalIdeal.adicCompletionIntegers k =>
        completionMap (k := k) place
          (u i : (comap (k := k) place).maximalIdeal.adicCompletion k) :=
      (continuous_completionMap (k := k) place).comp
        (continuous_subtype_val.comp (continuous_apply i))
    refine h₁.congr fun u => ?_
    exact (coe_completionIntegersMap (k := k) place (u i)).symm
  have hsmul_m : ∀ (c : (comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (i : Fin r),
      ((completionIntegersMap (k := k) place c :
        place.maximalIdeal.adicCompletionIntegers K) :
        place.maximalIdeal.adicCompletion K) * m i = c • m i := by
    intro c i
    have h1 : (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletion K)) c =
        ((completionIntegersMap (k := k) place c :
          place.maximalIdeal.adicCompletionIntegers K) :
          place.maximalIdeal.adicCompletion K) := by
      rw [algebraMap_instAlgebraAdicCompletionIntegersCompletion]
      change completionMap (k := k) place
          (c : (comap (k := k) place).maximalIdeal.adicCompletion k) =
        ((completionIntegersMap (k := k) place c :
          place.maximalIdeal.adicCompletionIntegers K) :
          place.maximalIdeal.adicCompletion K)
      exact (coe_completionIntegersMap (k := k) place c).symm
    rw [Algebra.smul_def, h1]
  have hrange : Set.range Ψ = ↑(Submodule.span
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) (Set.range m)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul_m (u i) i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro z hz
      rw [SetLike.mem_coe] at hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)).mp hz
      refine Set.mem_range.mpr ⟨c, ?_⟩
      rw [← hc]
      change (∑ i, ((completionIntegersMap (k := k) place (c i) :
          place.maximalIdeal.adicCompletionIntegers K) :
          place.maximalIdeal.adicCompletion K) * m i) = ∑ i, c i • m i
      exact Finset.sum_congr rfl fun i _ => hsmul_m (c i) i
  rw [← hrange]
  exact (isCompact_range hcont).isClosed

end ImageSpan

/-! ## Finiteness of the completed upper valuation ring over the lower one -/

section ModuleFinite

variable {k : Type u} [Field k] [NumberField k]
variable {K : Type v} [Field K] [NumberField K] [Algebra k K]

/-- **Gap (A), main theorem.** The upper completed valuation ring is a finite module
over the lower one. The proof uses a `ℤ`-generating family of `𝓞 K`; the span of
the images in `K_w` is dense in `𝒪_w` (density lemma) and closed (compactness
argument), hence `𝒪_w` is the span of finitely many elements, giving finiteness. -/
theorem moduleFinite_adicCompletionIntegers (place : NumberField.FinitePlace K) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) := by
  classical
  haveI hcompact := compactSpace_adicCompletionIntegers (k := k) place
  obtain ⟨r, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := NumberField.RingOfIntegers K)
  let m : Fin r → place.maximalIdeal.adicCompletion K := fun i =>
    (algebraMap (NumberField.RingOfIntegers K) K (b i) : place.maximalIdeal.adicCompletion K)
  let M' : Submodule ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) :=
    Submodule.span _ (Set.range m)
  have hm_mem : ∀ i, m i ∈ (place.maximalIdeal.adicCompletionIntegers K :
      Set (place.maximalIdeal.adicCompletion K)) := by
    intro i
    change Valued.v (m i) ≤ 1
    change Valued.v ((algebraMap (NumberField.RingOfIntegers K) K (b i) :
      place.maximalIdeal.adicCompletion K)) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (place.maximalIdeal) (b i)
  have hgen : ∀ a : NumberField.RingOfIntegers K,
      (algebraMap (NumberField.RingOfIntegers K) K a : place.maximalIdeal.adicCompletion K) ∈ M' := by
    intro a
    have ham : a ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp ham
    let φ : NumberField.RingOfIntegers K →+* place.maximalIdeal.adicCompletion K :=
      (algebraMap K (place.maximalIdeal.adicCompletion K)).comp
        (algebraMap (NumberField.RingOfIntegers K) K)
    change φ a ∈ M'
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    have hφb : φ (b i) = m i := rfl
    rw [hφb]
    have hbridge : c i • m i = ((c i : ℤ) :
        (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) • m i := by
      rw [zsmul_eq_mul, Algebra.smul_def, map_intCast]
    rw [hbridge]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense : ∀ x ∈ (place.maximalIdeal.adicCompletionIntegers K :
      Set (place.maximalIdeal.adicCompletion K)), x ∈ closure (M' :
        Set (place.maximalIdeal.adicCompletion K)) := by
    intro x hx
    rw [mem_closure_iff_nhds]
    intro W hW
    rw [Valued.mem_nhds] at hW
    obtain ⟨γ, hγW⟩ := hW
    have hemb_ne : MonoidWithZeroHom.ValueGroup₀.embedding (γ :
        MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass
          (Valued.v : Valuation (place.maximalIdeal.adicCompletion K) ℤᵐ⁰))) ≠ 0 := by
      intro h
      exact Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
        (by rw [h, map_zero]))
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt hemb_ne
    obtain ⟨a, ha⟩ := exists_ringOfIntegers_sub_valued_le (v := place.maximalIdeal) ⟨x, hx⟩ n
    have hmW : (algebraMap (NumberField.RingOfIntegers K) K a :
        place.maximalIdeal.adicCompletion K) ∈ W := by
      refine hγW ?_
      show Valued.v.restrict ((algebraMap (NumberField.RingOfIntegers K) K a :
          place.maximalIdeal.adicCompletion K) - x) < ↑γ
      rw [Valuation.restrict_lt_iff_lt_embedding]
      refine lt_of_le_of_lt ?_ hn
      have ha' : Valued.v ((x : place.maximalIdeal.adicCompletion K) -
          (algebraMap (NumberField.RingOfIntegers K) K a :
            place.maximalIdeal.adicCompletion K)) ≤ WithZero.exp (-(n : ℤ)) := by
        have hcoe2 : (((⟨x, hx⟩ : place.maximalIdeal.adicCompletionIntegers K) -
            algebraMap (NumberField.RingOfIntegers K)
              (place.maximalIdeal.adicCompletionIntegers K) a :
            place.maximalIdeal.adicCompletionIntegers K) :
            place.maximalIdeal.adicCompletion K) =
            (x : place.maximalIdeal.adicCompletion K) -
              (algebraMap (NumberField.RingOfIntegers K) K a :
                place.maximalIdeal.adicCompletion K) := by
          rw [show (((⟨x, hx⟩ : place.maximalIdeal.adicCompletionIntegers K) -
              algebraMap (NumberField.RingOfIntegers K)
                (place.maximalIdeal.adicCompletionIntegers K) a :
              place.maximalIdeal.adicCompletionIntegers K) :
              place.maximalIdeal.adicCompletion K) =
              (x : place.maximalIdeal.adicCompletion K) -
                ((algebraMap (NumberField.RingOfIntegers K)
                  (place.maximalIdeal.adicCompletionIntegers K) a :
                  place.maximalIdeal.adicCompletionIntegers K) :
                  place.maximalIdeal.adicCompletion K) from rfl]
          rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        rw [← hcoe2]
        exact ha
      rw [Valuation.map_sub_swap]
      exact ha'
    exact ⟨_, hmW, hgen a⟩
  have hclosed : IsClosed (M' : Set (place.maximalIdeal.adicCompletion K)) := by
    have h := isClosed_span_range_algebraMap_adicCompletion (k := k) place r b
    convert h using 2
  let P : Submodule ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) :=
    { carrier := (place.maximalIdeal.adicCompletionIntegers K :
        Set (place.maximalIdeal.adicCompletion K))
      zero_mem' := by
        rw [SetLike.mem_coe]
        exact (place.maximalIdeal.adicCompletionIntegers K).zero_mem
      add_mem' := fun hx hy => by
        rw [SetLike.mem_coe] at hx hy ⊢
        exact (place.maximalIdeal.adicCompletionIntegers K).add_mem _ _ hx hy
      smul_mem' := fun c y hy => by
        rw [SetLike.mem_coe] at hy ⊢
        rw [Algebra.smul_def, algebraMap_instAlgebraAdicCompletionIntegersCompletion]
        rw [RingHom.comp_apply, ValuationSubring.algebraMap_apply]
        exact (place.maximalIdeal.adicCompletionIntegers K).mul_mem _ _
          (completionMap_mem_adicCompletionIntegers place c.2) hy }
  have hM'le : M' ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hm_mem i
  have hOwin : ∀ z ∈ (place.maximalIdeal.adicCompletionIntegers K :
      Set (place.maximalIdeal.adicCompletion K)), z ∈ M' := by
    intro z hz
    have h := hdense z hz
    rwa [hclosed.closure_eq] at h
  have hPle : P ≤ M' := fun z hz => hOwin z hz
  have hPM : P = M' := le_antisymm hPle hM'le
  have hMfin : Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) ↥M' :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range m))
  show Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) ↥P
  rw [hPM]
  exact hMfin

end ModuleFinite

end LeanFormal.IUT.NumberFieldFinitePlace
