import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# The global degree sum formula for finite-place completions

For a finite extension `k → K` of number fields and a finite place `v` of `k`, this
file studies the sum of the local basis degrees `[K_w : k_v]` over all places `w` of
`K` above `v`:

`∑_{w | v} Module.finrank k_v K_w = Module.finrank k K`.

The *fibre* `w | v` is the subtype `PlacesAbove v` of the finite places of `K` whose
contraction is `v`; it is canonically equivalent to the prime ideals of `𝓞 K` over
`v.maximalIdeal.asIdeal`, and therefore finite. The file proves:

* `placesAboveEquivPrimesOver` and `placesAboveFintype`: the fibre is finite and is
  exactly the fibre of the contraction, reindexed by the primes over `v`.
* `relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg`: the relative degree
  `e * f` of a place extension is the product of Mathlib's localised
  `Ideal.ramificationIdx` and `Ideal.inertiaDeg`.
* `sum_relativeCompletionDegree_eq_fieldDegree`: the **unconditional** fibre sum of
  the relative degrees, `∑_{w | v} e_w * f_w = [K : k]`, obtained from Mathlib's
  `Ideal.sum_ramification_inertia_eq_finrank` at the integer rings. This is the
  ideal-layer global formula expressed in the finite-place fibre language.
* `finrank_ringOfIntegers_eq_fieldDegree`: the rank of `𝓞 K` over `𝓞 k` is the field
  degree `[K : k]`.
* `sum_finrank_adicCompletion_eq_fieldDegree_of_relativeCompletionDegree`: **the
  global degree sum formula**, reduced to the per-place identity
  `[K_w : k_v] = e_w * f_w`.
* `sum_finrank_adicCompletion_eq_fieldDegree`: the same formula with the exact named
  inputs of `FinitePlaceCompletionDegree.lean`, namely `Module.Finite 𝒪_v 𝒪_w` and
  `localDataAgreesWithPlaceData` for every place `w` in the fibre.

Honest scope. Level 1 of the task — an unconditional proof of
`∑_{w | v} [K_w : k_v] = [K : k]` — is not proved in this file itself: this file
reduces it to the per-place identity `[K_w : k_v] = e_w * f_w`, which is not
available in Mathlib 4.32.2 and is now proved in this development downstream
(see the closing paragraph). Exactly as in `FinitePlaceCompletionDegree.lean`,
that identity requires for each `w`:

1. `Module.Finite 𝒪_v 𝒪_w` for the completed valuation rings, equivalently
   `IsIntegralClosure 𝒪_w 𝒪_v K_w` (uniqueness of the extension of a complete
   valuation); and
2. `localDataAgreesWithPlaceData w`, the comparison of the local ramification index
   and local residue degree at the completed rings with the ideal-theoretic data.

Both inputs are now proved unconditionally in this development — input 1 in
`AdicCompletionValuationUniqueness` (`moduleFinite_adicCompletionIntegers`) and
input 2 in `FinitePlaceCompletionLocalInputs`
(`localDataAgreesWithPlaceData_adicCompletion`) — and the unconditional fibre sum
is assembled downstream of this file, in `RelativeCompletionFinrankReduction`,
as `sum_finrank_adicCompletion_eq_fieldDegree_unconditional`, together with the
six hypothesis-free norm transports of `FinitePlaceCompletionNormTransport`. The
reduction theorems below still take both inputs as explicit hypotheses, never as
axioms or placeholders. The statements proved in this file itself remain the
reindexing bridge `∑_{w | v} e_w * f_w = [K : k]` and the rank identity
`Module.finrank (𝓞 k) (𝓞 K) = Module.finrank k K`.
-/

open scoped Valued

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## The fibre of finite places above a fixed lower place -/

/-- The finite places of `K` lying above a fixed finite place `lowerPlace` of `k`,
i.e. the fibre of the contraction map `comap`. -/
abbrev PlacesAbove (lowerPlace : NumberField.FinitePlace k) :=
  {upperPlace : NumberField.FinitePlace K // comap (k := k) upperPlace = lowerPlace}

/-- The prime ideal of `𝓞 K` underlying a place above `lowerPlace` is a prime over
`lowerPlace.maximalIdeal.asIdeal`. -/
def primeOverOfPlaceAbove (lowerPlace : NumberField.FinitePlace k)
    (upperPlace : PlacesAbove (K := K) lowerPlace) :
    lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) := by
  refine ⟨upperPlace.val.maximalIdeal.asIdeal, upperPlace.val.maximalIdeal.isPrime, ?_⟩
  have above := comap_liesOver (k := k) upperPlace.val
  rw [upperPlace.property] at above
  exact above

/-- Conversely, every prime of `𝓞 K` over `lowerPlace.maximalIdeal.asIdeal` defines a
finite place of `K` whose contraction is `lowerPlace`. -/
noncomputable def placeAboveOfPrimeOver (lowerPlace : NumberField.FinitePlace k)
    (upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
      (NumberField.RingOfIntegers K)) :
    PlacesAbove (K := K) lowerPlace := by
  letI : upperPrime.val.IsPrime := upperPrime.property.1
  letI : upperPrime.val.LiesOver lowerPlace.maximalIdeal.asIdeal := upperPrime.property.2
  letI : lowerPlace.maximalIdeal.asIdeal.IsMaximal := lowerPlace.maximalIdeal.isMaximal
  have upperMaximal : upperPrime.val.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal upperPrime.val lowerPlace.maximalIdeal.asIdeal
  let upperHeightOne : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    { asIdeal := upperPrime.val
      isPrime := upperPrime.property.1
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField upperMaximal
        (NumberField.RingOfIntegers.not_isField K) }
  refine ⟨NumberField.FinitePlace.mk upperHeightOne, ?_⟩
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  simp only [comap_maximalIdeal, NumberField.FinitePlace.maximalIdeal_mk]
  exact ((Ideal.liesOver_iff upperPrime.val lowerPlace.maximalIdeal.asIdeal).mp
    upperPrime.property.2).symm

@[simp]
theorem placeAboveOfPrimeOver_maximalIdeal (lowerPlace : NumberField.FinitePlace k)
    (upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
      (NumberField.RingOfIntegers K)) :
    (placeAboveOfPrimeOver lowerPlace upperPrime).val.maximalIdeal.asIdeal =
      upperPrime.val := by
  simp [placeAboveOfPrimeOver, NumberField.FinitePlace.maximalIdeal_mk]

/-- The fibre of the contraction over `lowerPlace` is exactly the set of primes of
`𝓞 K` over `lowerPlace.maximalIdeal.asIdeal`. -/
noncomputable def placesAboveEquivPrimesOver (lowerPlace : NumberField.FinitePlace k) :
    PlacesAbove (K := K) lowerPlace ≃
      lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) where
  toFun := primeOverOfPlaceAbove lowerPlace
  invFun := placeAboveOfPrimeOver lowerPlace
  left_inv upperPlace := by
    apply Subtype.ext
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact placeAboveOfPrimeOver_maximalIdeal lowerPlace
      (primeOverOfPlaceAbove lowerPlace upperPlace)
  right_inv upperPrime := by
    apply Subtype.ext
    exact placeAboveOfPrimeOver_maximalIdeal lowerPlace upperPrime

/-- The fibre of the contraction over a finite place is finite, transported from the
finiteness of the primes over the underlying maximal ideal. -/
instance placesAboveFintype (lowerPlace : NumberField.FinitePlace k) :
    Fintype (PlacesAbove (K := K) lowerPlace) := by
  letI := (Algebra.QuasiFinite.finite_primesOver
    (S := NumberField.RingOfIntegers K) lowerPlace.maximalIdeal.asIdeal).fintype
  exact Fintype.ofEquiv
    (lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K))
    (placesAboveEquivPrimesOver (K := K) lowerPlace).symm

/-! ## The ideal-layer sum in the finite-place fibre language -/

/-- The relative completion degree `e * f` of a place extension, written with
Mathlib's localised `Ideal.ramificationIdx` and `Ideal.inertiaDeg`. -/
theorem relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg
    (upperPlace : NumberField.FinitePlace K) :
    relativeCompletionDegree (k := k) upperPlace =
      upperPlace.maximalIdeal.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
        upperPlace.maximalIdeal.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  haveI : upperPlace.maximalIdeal.asIdeal.IsMaximal := upperPlace.maximalIdeal.isMaximal
  haveI : (comap (k := k) upperPlace).maximalIdeal.asIdeal.IsMaximal :=
    (comap (k := k) upperPlace).maximalIdeal.isMaximal
  unfold relativeCompletionDegree relativeRamificationIndex relativeResidueDegree
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _
      (comap (k := k) upperPlace).maximalIdeal.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]

/-- The rank of `𝓞 K` over `𝓞 k` is the relative field degree `[K : k]`. -/
theorem finrank_ringOfIntegers_eq_fieldDegree :
    Module.finrank (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) =
      Module.finrank k K := by
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K)
        (nonZeroDivisors (NumberField.RingOfIntegers k))) K :=
    IsIntegralClosure.isLocalization (NumberField.RingOfIntegers k) k K
      (NumberField.RingOfIntegers K)
  have module_rank := IsLocalizedModule.finrank_eq
    (nonZeroDivisors (NumberField.RingOfIntegers k))
    (IsScalarTower.toAlgHom (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers K) K).toLinearMap le_rfl
  have scalar_rank : Module.finrank k K =
      Module.finrank (NumberField.RingOfIntegers k) K :=
    congrArg Cardinal.toNat
      (IsLocalization.rank_eq (R := NumberField.RingOfIntegers k) (N := K)
        k (nonZeroDivisors (NumberField.RingOfIntegers k)) le_rfl)
  exact module_rank.symm.trans scalar_rank.symm

/-- **The ideal-layer global formula in the fibre language.** The sum over the fibre
of the relative degrees `e_w * f_w` is the relative field degree. This is
Mathlib's `Ideal.sum_ramification_inertia_eq_finrank` at the integer rings, reindexed
along `placesAboveEquivPrimesOver`. It is unconditional. -/
theorem sum_relativeCompletionDegree_eq_fieldDegree
    (lowerPlace : NumberField.FinitePlace k) :
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
      relativeCompletionDegree (k := k) upperPlace.val) = Module.finrank k K := by
  letI : lowerPlace.maximalIdeal.asIdeal.IsPrime := lowerPlace.maximalIdeal.isPrime
  letI : Fintype (lowerPlace.maximalIdeal.asIdeal.primesOver
      (NumberField.RingOfIntegers K)) :=
    (Algebra.QuasiFinite.finite_primesOver
      (S := NumberField.RingOfIntegers K) lowerPlace.maximalIdeal.asIdeal).fintype
  calc
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
        relativeCompletionDegree (k := k) upperPlace.val)
        = ∑ upperPlace : PlacesAbove (K := K) lowerPlace,
            (fun upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
                (NumberField.RingOfIntegers K) =>
              upperPrime.val.ramificationIdx (NumberField.RingOfIntegers k) *
                upperPrime.val.inertiaDeg (NumberField.RingOfIntegers k))
              (placesAboveEquivPrimesOver (K := K) lowerPlace upperPlace) := by
          apply Finset.sum_congr rfl
          intro upperPlace _
          rw [relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg]
          rfl
      _ = ∑ upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
              (NumberField.RingOfIntegers K),
            upperPrime.val.ramificationIdx (NumberField.RingOfIntegers k) *
              upperPrime.val.inertiaDeg (NumberField.RingOfIntegers k) :=
          (placesAboveEquivPrimesOver (K := K) lowerPlace).sum_comp
            (fun upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
                (NumberField.RingOfIntegers K) =>
              upperPrime.val.ramificationIdx (NumberField.RingOfIntegers k) *
                upperPrime.val.inertiaDeg (NumberField.RingOfIntegers k))
      _ = Module.finrank (NumberField.RingOfIntegers k)
            (NumberField.RingOfIntegers K) :=
          Ideal.sum_ramification_inertia_eq_finrank lowerPlace.maximalIdeal.asIdeal
            (NumberField.RingOfIntegers K)
      _ = Module.finrank k K := finrank_ringOfIntegers_eq_fieldDegree (k := k) (K := K)

/-! ## The global degree sum formula, reduced to the per-place local identity -/

/-- **The global degree sum formula, reduced.** If the local basis degree of every
place `w` above `lowerPlace` agrees with its relative degree `e_w * f_w`, then the
fibre sum of the local basis degrees is the relative field degree. This isolates the
per-place local fundamental identity as the only missing input; the reindexing and the
ideal-layer sum are proved in `sum_relativeCompletionDegree_eq_fieldDegree`. -/
theorem sum_finrank_adicCompletion_eq_fieldDegree_of_relativeCompletionDegree
    (lowerPlace : NumberField.FinitePlace k)
    (hlocal : ∀ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
          (upperPlace.val.maximalIdeal.adicCompletion K) =
        relativeCompletionDegree (k := k) upperPlace.val) :
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
        (upperPlace.val.maximalIdeal.adicCompletion K)) = Module.finrank k K := by
  calc
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
        Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
          (upperPlace.val.maximalIdeal.adicCompletion K))
        = ∑ upperPlace : PlacesAbove (K := K) lowerPlace,
            relativeCompletionDegree (k := k) upperPlace.val := by
          apply Finset.sum_congr rfl
          intro upperPlace _
          exact hlocal upperPlace
      _ = Module.finrank k K := sum_relativeCompletionDegree_eq_fieldDegree (K := K) lowerPlace

/-- **The global degree sum formula from the named inputs of
`FinitePlaceCompletionDegree.lean`.** Assuming, for every place `w` above
`lowerPlace`, the finiteness `Module.Finite 𝒪_v 𝒪_w` of the completed valuation rings
and the agreement `localDataAgreesWithPlaceData w` of the local ramification index and
local residue degree with the ideal-theoretic data, the fibre sum of the local basis
degrees is the relative field degree.

Both hypotheses are exactly the named inputs of
`finrank_adicCompletion_eq_relativeCompletionDegree`; they are not assumed anywhere
unconditionally and are not axioms. -/
theorem sum_finrank_adicCompletion_eq_fieldDegree
    (lowerPlace : NumberField.FinitePlace k)
    (hfinite : ∀ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.Finite
        ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletionIntegers k)
        (upperPlace.val.maximalIdeal.adicCompletionIntegers K))
    (hagree : ∀ upperPlace : PlacesAbove (K := K) lowerPlace,
      localDataAgreesWithPlaceData (k := k) upperPlace.val) :
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
        (upperPlace.val.maximalIdeal.adicCompletion K)) = Module.finrank k K :=
  sum_finrank_adicCompletion_eq_fieldDegree_of_relativeCompletionDegree (K := K) lowerPlace
    fun upperPlace =>
      finrank_adicCompletion_eq_relativeCompletionDegree (k := k) upperPlace.val
        (hfinite upperPlace) (hagree upperPlace)

/-! ## A fibre-independent form of the reduction -/

/-- A uniform form of the reduction: if the per-place local identity holds for *every*
finite place of `K`, then the fibre sum over any lower place is the relative field
degree. -/
theorem sum_finrank_adicCompletion_eq_fieldDegree_of_forall
    (hlocal : ∀ upperPlace : NumberField.FinitePlace K,
      Module.finrank ((comap (k := k) upperPlace).maximalIdeal.adicCompletion k)
          (upperPlace.maximalIdeal.adicCompletion K) =
        relativeCompletionDegree (k := k) upperPlace)
    (lowerPlace : NumberField.FinitePlace k) :
    (∑ upperPlace : PlacesAbove (K := K) lowerPlace,
      Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
        (upperPlace.val.maximalIdeal.adicCompletion K)) = Module.finrank k K :=
  sum_finrank_adicCompletion_eq_fieldDegree_of_relativeCompletionDegree (K := K) lowerPlace
    fun upperPlace => hlocal upperPlace.val

/-! ## The one-sided bound obtained from the ideal-layer sum -/

/-- Every local basis degree in the fibre is at most the relative field degree; this is
the one-sided consequence of the global formula already available for a single
completion. -/
theorem finrank_adicCompletion_le_fieldDegree_of_placesAbove
    (lowerPlace : NumberField.FinitePlace k)
    (upperPlace : PlacesAbove (K := K) lowerPlace) :
    Module.finrank ((comap (k := k) upperPlace.val).maximalIdeal.adicCompletion k)
        (upperPlace.val.maximalIdeal.adicCompletion K) ≤ Module.finrank k K :=
  finrank_completionAlgebra_le_fieldDegree (k := k) upperPlace.val

end

end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finitePlaceCompletionGlobalDegree : Obligation :=
  { id := "Foundations.NumberField.finite-place-completion-global-degree"
    source :=
      "The local-global degree formula Sum_{w | v} [K_w : k_v] = [K : k] " ++
        "(Neukirch, Algebraic Number Theory, I.13 / II.8; Serre, Local Fields, II.2)"
    status := VerificationStatus.conditional
    note :=
      "`PlacesAbove v` is the fibre of the contraction `comap` over the finite place " ++
        "`v`; `placesAboveEquivPrimesOver` reindexes it by the primes of `O_K` over " ++
        "`v.maximalIdeal.asIdeal` and `placesAboveFintype` makes the fibre finite. " ++
        "`relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg` identifies the " ++
        "relative degree with the product of Mathlib's localised " ++
        "`Ideal.ramificationIdx` and `Ideal.inertiaDeg`. " ++
        "`finrank_ringOfIntegers_eq_fieldDegree` is the rank identity " ++
        "`finrank (O_k) (O_K) = [K : k]`. " ++
        "`sum_relativeCompletionDegree_eq_fieldDegree` is the *unconditional* fibre " ++
        "sum `Sum_{w | v} e_w * f_w = [K : k]`, from Mathlib's " ++
        "`Ideal.sum_ramification_inertia_eq_finrank`. " ++
        "`sum_finrank_adicCompletion_eq_fieldDegree_of_relativeCompletionDegree` is " ++
        "the global degree sum formula reduced to the per-place identity " ++
        "`[K_w : k_v] = e_w * f_w`; " ++
        "`sum_finrank_adicCompletion_eq_fieldDegree` states it from the exact named " ++
        "inputs `Module.Finite O_v O_w` and `localDataAgreesWithPlaceData w` of " ++
        "`FinitePlaceCompletionDegree.lean`, and " ++
        "`sum_finrank_adicCompletion_eq_fieldDegree_of_forall` is the uniform form. " ++
        "The unconditional identity `Sum_{w | v} [K_w : k_v] = [K : k]` is now " ++
        "proved in this development, downstream of this file: the two per-place " ++
        "inputs above (a residue-field isomorphism `O_v / m_v ~= O_k / v` compatible " ++
        "with `Ideal.ramificationIdx'` under adic completion, and the identification " ++
        "of `O_w` with the integral closure of `O_v` in `K_w`) are discharged by " ++
        "`AdicCompletionValuationUniqueness.moduleFinite_adicCompletionIntegers` " ++
        "and by `FinitePlaceCompletionLocalInputs.localDataAgreesWithPlaceData_" ++
        "adicCompletion`; their assembly is " ++
        "`RelativeCompletionFinrankReduction.sum_finrank_adicCompletion_eq_" ++
        "fieldDegree_unconditional`, together with the six hypothesis-free norm " ++
        "transports, in modules that import this file and therefore cannot be " ++
        "imported back. The reductions above retain the two inputs as explicit " ++
        "hypotheses, never as axioms or placeholders."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-completion-local-fundamental-identity" ]
    externalAxioms := []
    sorryItems := [] }

end LeanFormal.IUT.Audit
