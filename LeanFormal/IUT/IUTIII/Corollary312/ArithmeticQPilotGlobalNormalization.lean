import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
Actual fibers of finite places for the arithmetic q-pilot normalization.

The selected upper places are the entire inverse image of the selected lower
places under contraction. In particular, places above one lower place retain
their separate contributions. The local input is the actual completion map
and the residue-norm normalization from `ArithmeticQPilotBaseChange`.

The resulting arithmetic sum divided by absolute field degree is invariant.
Identification with the paper's actual q-pilot, Tate uniformization, coricity,
and theta-hull properties are separate claims and are not established here.
-/

namespace LeanFormal.IUT

namespace ArithmeticQPilotGlobalNormalization

open NumberFieldFinitePlace ArithmeticQPilotLogVolume ArithmeticQPilotBaseChange

universe u v

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- All actual upper finite places contracting to the specified lower place. -/
abbrev UpperPlaceFiber (lowerPlace : NumberField.FinitePlace k) :=
  {upperPlace : NumberField.FinitePlace K // comap (k := k) upperPlace = lowerPlace}

/-- The entire inverse image of the finite selected lower set under contraction. -/
abbrev AllSelectedUpperPlaces (selectedLowerPlaces : Finset (NumberField.FinitePlace k)) :=
  {upperPlace : NumberField.FinitePlace K //
    comap (k := k) upperPlace ∈ selectedLowerPlaces}

/-- Exact indexing of all selected upper places by lower place and its full fiber. -/
def selectedUpperEquivFiberSigma
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k)) :
    AllSelectedUpperPlaces (K := K) selectedLowerPlaces ≃
      (Σ lowerPlace : selectedLowerPlaces, UpperPlaceFiber (K := K) lowerPlace.val) where
  toFun upperPlace :=
    ⟨⟨comap (k := k) upperPlace.val, upperPlace.property⟩, ⟨upperPlace.val, rfl⟩⟩
  invFun indexedPlace :=
    ⟨indexedPlace.2.val, by
      rw [indexedPlace.2.property]
      exact indexedPlace.1.property⟩
  left_inv upperPlace := by
    apply Subtype.ext
    rfl
  right_inv indexedPlace := by
    rcases indexedPlace with ⟨⟨lowerPlace, lower_mem⟩, upperPlace, above_eq⟩
    cases above_eq
    rfl

/-- The maximal ideal of an actual place in the contraction fiber lies over the
specified lower maximal ideal. -/
def primeOverOfUpperPlace (lowerPlace : NumberField.FinitePlace k)
    (upperPlace : UpperPlaceFiber (K := K) lowerPlace) :
    lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) := by
  refine ⟨upperPlace.val.maximalIdeal.asIdeal, upperPlace.val.maximalIdeal.isPrime, ?_⟩
  have above := comap_liesOver (k := k) upperPlace.val
  rw [upperPlace.property] at above
  exact above

/-- Every prime above the selected nonzero lower prime defines an upper finite
place; maximality and nonzeroness follow from the actual integral extension. -/
def upperPlaceOfPrimeOver (lowerPlace : NumberField.FinitePlace k)
    (upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
      (NumberField.RingOfIntegers K)) : UpperPlaceFiber (K := K) lowerPlace := by
  letI : upperPrime.val.IsPrime := upperPrime.property.1
  letI : upperPrime.val.LiesOver lowerPlace.maximalIdeal.asIdeal := upperPrime.property.2
  letI : lowerPlace.maximalIdeal.asIdeal.IsMaximal := lowerPlace.maximalIdeal.isMaximal
  have upper_maximal : upperPrime.val.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal upperPrime.val lowerPlace.maximalIdeal.asIdeal
  let upperHeightOne : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    { asIdeal := upperPrime.val
      isPrime := upperPrime.property.1
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField upper_maximal
        (NumberField.RingOfIntegers.not_isField K) }
  refine ⟨NumberField.FinitePlace.mk upperHeightOne, ?_⟩
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  simp only [comap_maximalIdeal, NumberField.FinitePlace.maximalIdeal_mk]
  exact ((Ideal.liesOver_iff upperPrime.val lowerPlace.maximalIdeal.asIdeal).mp
    upperPrime.property.2).symm

@[simp] theorem upperPlaceOfPrimeOver_maximalIdeal
    (lowerPlace : NumberField.FinitePlace k)
    (upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
      (NumberField.RingOfIntegers K)) :
    (upperPlaceOfPrimeOver lowerPlace upperPrime).val.maximalIdeal.asIdeal = upperPrime.val := by
  simp [upperPlaceOfPrimeOver, NumberField.FinitePlace.maximalIdeal_mk]

/-- The actual contraction fiber and all primes above the lower prime have the
same elements, with no choice of a proper subset upstairs. -/
def upperPlaceFiberEquivPrimesOver (lowerPlace : NumberField.FinitePlace k) :
    UpperPlaceFiber (K := K) lowerPlace ≃
      lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) where
  toFun := primeOverOfUpperPlace lowerPlace
  invFun := upperPlaceOfPrimeOver lowerPlace
  left_inv upperPlace := by
    apply Subtype.ext
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact upperPlaceOfPrimeOver_maximalIdeal lowerPlace
      (primeOverOfUpperPlace lowerPlace upperPlace)
  right_inv upperPrime := by
    apply Subtype.ext
    exact upperPlaceOfPrimeOver_maximalIdeal lowerPlace upperPrime

/-- Finiteness comes from the finite ring-of-integers extension. -/
instance upperPlaceFiberFintype (lowerPlace : NumberField.FinitePlace k) :
    Fintype (UpperPlaceFiber (K := K) lowerPlace) := by
  letI := (Algebra.QuasiFinite.finite_primesOver
    (S := NumberField.RingOfIntegers K) lowerPlace.maximalIdeal.asIdeal).fintype
  exact Fintype.ofEquiv
    (lowerPlace.maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K))
    (upperPlaceFiberEquivPrimesOver lowerPlace).symm

/-- The complete inverse image of a finite lower selection is actually finite. -/
instance allSelectedUpperPlacesFintype
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k)) :
    Fintype (AllSelectedUpperPlaces (K := K) selectedLowerPlaces) :=
  Fintype.ofEquiv
    (Σ lowerPlace : selectedLowerPlaces, UpperPlaceFiber (K := K) lowerPlace.val)
    (selectedUpperEquivFiberSigma selectedLowerPlaces).symm

/-- The fundamental sum, first expressed at the actual rings-of-integers rank. -/
theorem sum_completionNormDegree_eq_integerRingRank
    (lowerPlace : NumberField.FinitePlace k) :
    (∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace,
      completionNormDegree (k := k) upperPlace.val) =
        Module.finrank (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) := by
  letI : lowerPlace.maximalIdeal.asIdeal.IsPrime := lowerPlace.maximalIdeal.isPrime
  letI := (Algebra.QuasiFinite.finite_primesOver
    (S := NumberField.RingOfIntegers K) lowerPlace.maximalIdeal.asIdeal).fintype
  calc
    (∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace,
        completionNormDegree (k := k) upperPlace.val) =
        ∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace,
          upperPlace.val.maximalIdeal.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
            upperPlace.val.maximalIdeal.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
      apply Finset.sum_congr rfl
      intro upperPlace _
      letI : upperPlace.val.maximalIdeal.asIdeal.IsMaximal :=
        upperPlace.val.maximalIdeal.isMaximal
      letI : (comap (k := k) upperPlace.val).maximalIdeal.asIdeal.IsMaximal :=
        (comap (k := k) upperPlace.val).maximalIdeal.isMaximal
      unfold completionNormDegree localRamificationIndex localResidueDegree
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _
        (comap (k := k) upperPlace.val).maximalIdeal.ne_bot,
        Ideal.inertiaDeg'_eq_inertiaDeg]
    _ = ∑ upperPrime : lowerPlace.maximalIdeal.asIdeal.primesOver
          (NumberField.RingOfIntegers K),
        upperPrime.val.ramificationIdx (NumberField.RingOfIntegers k) *
          upperPrime.val.inertiaDeg (NumberField.RingOfIntegers k) :=
      (upperPlaceFiberEquivPrimesOver (K := K) lowerPlace).sum_comp
        (fun upperPrime =>
          upperPrime.val.ramificationIdx (NumberField.RingOfIntegers k) *
            upperPrime.val.inertiaDeg (NumberField.RingOfIntegers k))
    _ = Module.finrank (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) :=
      Ideal.sum_ramification_inertia_eq_finrank lowerPlace.maximalIdeal.asIdeal
        (NumberField.RingOfIntegers K)

/-- Relative rank is computed after localizing the actual integer rings and
their scalar action. No principal-ideal or free-module assumption is imposed. -/
theorem integerRingRank_eq_fieldDegree :
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
  have scalar_rank : Module.finrank k K = Module.finrank (NumberField.RingOfIntegers k) K :=
    congrArg Cardinal.toNat
      (IsLocalization.rank_eq (R := NumberField.RingOfIntegers k) (N := K)
        k (nonZeroDivisors (NumberField.RingOfIntegers k)) le_rfl)
  exact module_rank.symm.trans scalar_rank.symm

/-- The fundamental arithmetic identity on the full actual finite-place fiber. -/
theorem sum_completionNormDegree_eq_fieldDegree
    (lowerPlace : NumberField.FinitePlace k) :
    (∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace,
      completionNormDegree (k := k) upperPlace.val) = Module.finrank k K := by
  rw [sum_completionNormDegree_eq_integerRingRank, integerRingRank_eq_fieldDegree]

/-- Actual contraction is surjective, so each complete fiber is nonempty. -/
theorem upperPlaceFiber_nonempty (lowerPlace : NumberField.FinitePlace k) :
    Nonempty (UpperPlaceFiber (K := K) lowerPlace) := by
  obtain ⟨upperPlace, contracts_to_lower⟩ :=
    comap_surjective (k := k) (K := K) lowerPlace
  exact ⟨⟨upperPlace, contracts_to_lower⟩⟩

theorem allSelectedUpperPlaces_nonempty
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    Nonempty (AllSelectedUpperPlaces (K := K) selectedLowerPlaces) := by
  obtain ⟨lowerPlace, lower_mem⟩ := selected_nonempty
  obtain ⟨upperPlace⟩ := upperPlaceFiber_nonempty (K := K) lowerPlace
  refine ⟨⟨upperPlace.val, ?_⟩⟩
  rw [upperPlace.property]
  exact lower_mem

theorem localLogMagnitude_transport
    {lowerPlace otherPlace : NumberField.FinitePlace k}
    (place_eq : lowerPlace = otherPlace)
    (parameter : FinitePlaceQCandidate lowerPlace) :
    localLogMagnitude (place_eq ▸ parameter) = localLogMagnitude parameter := by
  cases place_eq
  rfl

/-- One lower actual q-candidate is transported to every place in its full fiber. -/
def fiberMappedParameter (lowerPlace : NumberField.FinitePlace k)
    (parameter : FinitePlaceQCandidate lowerPlace)
    (upperPlace : UpperPlaceFiber (K := K) lowerPlace) :
    FinitePlaceQCandidate upperPlace.val :=
  FinitePlaceQCandidate.map upperPlace.val (upperPlace.property.symm ▸ parameter)

theorem localLogMagnitude_fiberMappedParameter
    (lowerPlace : NumberField.FinitePlace k)
    (parameter : FinitePlaceQCandidate lowerPlace)
    (upperPlace : UpperPlaceFiber (K := K) lowerPlace) :
    localLogMagnitude (fiberMappedParameter lowerPlace parameter upperPlace) =
      (completionNormDegree (k := k) upperPlace.val : ℝ) *
        localLogMagnitude parameter := by
  unfold fiberMappedParameter
  rw [localLogMagnitude_map, localLogMagnitude_transport]

/-- The family on the full upper selection induced by the selected lower family. -/
def selectedMappedParameter
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (upperPlace : AllSelectedUpperPlaces (K := K) selectedLowerPlaces) :
    FinitePlaceQCandidate upperPlace.val :=
  FinitePlaceQCandidate.map upperPlace.val
    (parameters ⟨comap (k := k) upperPlace.val, upperPlace.property⟩)

/-- The full-fiber q-magnitude sum uses each actual upper place once. -/
theorem sum_fiberLogMagnitude_eq_integerRingRank_mul
    (lowerPlace : NumberField.FinitePlace k)
    (parameter : FinitePlaceQCandidate lowerPlace) :
    (∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace,
      localLogMagnitude (fiberMappedParameter lowerPlace parameter upperPlace)) =
        (Module.finrank (NumberField.RingOfIntegers k)
          (NumberField.RingOfIntegers K) : ℝ) * localLogMagnitude parameter := by
  simp_rw [localLogMagnitude_fiberMappedParameter]
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast sum_completionNormDegree_eq_integerRingRank (K := K) lowerPlace

/-- The ordinary selected sum already contains `log N(v)` in every local term;
there is no second local-degree weight. -/
def selectedLowerMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  ∑ lowerPlace : selectedLowerPlaces, localLogMagnitude (parameters lowerPlace)

/-- The ordinary sum over the full inverse image of the selected lower places. -/
def selectedUpperMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  ∑ upperPlace : AllSelectedUpperPlaces (K := K) selectedLowerPlaces,
    localLogMagnitude (selectedMappedParameter selectedLowerPlaces parameters upperPlace)

/-- Reindex the actual upper selection into complete fibers without dropping
places or counting one upper place in two different fibers. -/
theorem selectedUpperMagnitude_eq_fiberSums
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    selectedUpperMagnitude (K := K) selectedLowerPlaces parameters =
      ∑ lowerPlace : selectedLowerPlaces,
        ∑ upperPlace : UpperPlaceFiber (K := K) lowerPlace.val,
          localLogMagnitude
            (fiberMappedParameter lowerPlace.val (parameters lowerPlace) upperPlace) := by
  calc
    selectedUpperMagnitude (K := K) selectedLowerPlaces parameters =
        ∑ indexedPlace : (Σ lowerPlace : selectedLowerPlaces,
          UpperPlaceFiber (K := K) lowerPlace.val),
          localLogMagnitude (fiberMappedParameter indexedPlace.1.val
            (parameters indexedPlace.1) indexedPlace.2) := by
      rw [← (selectedUpperEquivFiberSigma (K := K) selectedLowerPlaces).sum_comp]
      apply Finset.sum_congr rfl
      intro upperPlace _
      rfl
    _ = _ := Fintype.sum_sigma _

/-- Global unnormalized scaling, at the module rank supplied by the fundamental
ramification-inertia identity. -/
theorem selectedUpperMagnitude_eq_integerRingRank_mul
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    selectedUpperMagnitude (K := K) selectedLowerPlaces parameters =
      (Module.finrank (NumberField.RingOfIntegers k)
        (NumberField.RingOfIntegers K) : ℝ) *
          selectedLowerMagnitude selectedLowerPlaces parameters := by
  rw [selectedUpperMagnitude_eq_fiberSums]
  simp_rw [sum_fiberLogMagnitude_eq_integerRingRank_mul, selectedLowerMagnitude]
  rw [← Finset.mul_sum]

/-- Summing the local `e f` scaling over every upper place multiplies the full
selected q-magnitude sum by the actual relative field degree. -/
theorem selectedUpperMagnitude_eq_fieldDegree_mul
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    selectedUpperMagnitude (K := K) selectedLowerPlaces parameters =
      (Module.finrank k K : ℝ) * selectedLowerMagnitude selectedLowerPlaces parameters := by
  rw [selectedUpperMagnitude_eq_integerRingRank_mul, integerRingRank_eq_fieldDegree]

theorem selectedLowerMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < selectedLowerMagnitude selectedLowerPlaces parameters := by
  simpa [selectedLowerMagnitude, selectedLogMagnitude] using
    selectedLogMagnitude_pos selectedLowerPlaces parameters (fun _ => 1)
      selected_nonempty (by intro lowerPlace; norm_num)

theorem selectedUpperMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < selectedUpperMagnitude (K := K) selectedLowerPlaces parameters := by
  unfold selectedUpperMagnitude
  apply Finset.sum_pos
  · intro upperPlace _
    exact localLogMagnitude_pos
      (selectedMappedParameter selectedLowerPlaces parameters upperPlace)
  · obtain ⟨upperPlace⟩ :=
      allSelectedUpperPlaces_nonempty (K := K) selectedLowerPlaces selected_nonempty
    exact ⟨upperPlace, Finset.mem_univ _⟩

/-- The absolute-degree denominator is the actual degree over the rationals. -/
def absoluteDegreeNormalizedLowerMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  selectedLowerMagnitude selectedLowerPlaces parameters / (Module.finrank ℚ k : ℝ)

def absoluteDegreeNormalizedUpperMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  selectedUpperMagnitude (K := K) selectedLowerPlaces parameters / (Module.finrank ℚ K : ℝ)

theorem absoluteDegreeNormalizedLowerMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < absoluteDegreeNormalizedLowerMagnitude selectedLowerPlaces parameters := by
  apply div_pos (selectedLowerMagnitude_pos selectedLowerPlaces parameters selected_nonempty)
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := k))

theorem absoluteDegreeNormalizedUpperMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < absoluteDegreeNormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters := by
  apply div_pos (selectedUpperMagnitude_pos (K := K)
    selectedLowerPlaces parameters selected_nonempty)
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))

/-- The absolute field degrees form the actual rational scalar tower. -/
theorem absoluteDegree_eq_relative_mul :
    Module.finrank ℚ K = Module.finrank k K * Module.finrank ℚ k := by
  simpa only [Nat.mul_comm] using (Module.finrank_mul_finrank ℚ k K).symm

/-- Absolute-degree normalization is invariant for the coherent q-family on
the entire upper inverse image. No assertion concerns a proper upper subset. -/
theorem absoluteDegreeNormalizedMagnitude_invariant
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    absoluteDegreeNormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters =
      absoluteDegreeNormalizedLowerMagnitude selectedLowerPlaces parameters := by
  unfold absoluteDegreeNormalizedUpperMagnitude absoluteDegreeNormalizedLowerMagnitude
  rw [selectedUpperMagnitude_eq_fieldDegree_mul,
    absoluteDegree_eq_relative_mul (k := k), Nat.cast_mul]
  have relative_degree_ne_zero : (Module.finrank k K : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := k) (M := K)))
  have lower_degree_ne_zero : (Module.finrank ℚ k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := k)))
  apply (div_eq_div_iff
    (mul_ne_zero relative_degree_ne_zero lower_degree_ne_zero) lower_degree_ne_zero).2
  ring

/-- Signed q-logarithms use the same lower selection and the same actual q-family. -/
def selectedLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  ∑ lowerPlace : selectedLowerPlaces, localSignedLog (parameters lowerPlace)

def selectedUpperSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  ∑ upperPlace : AllSelectedUpperPlaces (K := K) selectedLowerPlaces,
    localSignedLog (selectedMappedParameter selectedLowerPlaces parameters upperPlace)

theorem selectedLowerSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    selectedLowerSignedLog selectedLowerPlaces parameters =
      -selectedLowerMagnitude selectedLowerPlaces parameters := by
  simp only [selectedLowerSignedLog, selectedLowerMagnitude,
    localSignedLog_eq_neg_magnitude, Finset.sum_neg_distrib]

theorem selectedUpperSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    selectedUpperSignedLog (K := K) selectedLowerPlaces parameters =
      -selectedUpperMagnitude (K := K) selectedLowerPlaces parameters := by
  simp only [selectedUpperSignedLog, selectedUpperMagnitude,
    localSignedLog_eq_neg_magnitude, Finset.sum_neg_distrib]

def absoluteDegreeNormalizedLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  selectedLowerSignedLog selectedLowerPlaces parameters / (Module.finrank ℚ k : ℝ)

def absoluteDegreeNormalizedUpperSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  selectedUpperSignedLog (K := K) selectedLowerPlaces parameters / (Module.finrank ℚ K : ℝ)

theorem normalizedLowerSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters =
      -absoluteDegreeNormalizedLowerMagnitude selectedLowerPlaces parameters := by
  simp only [absoluteDegreeNormalizedLowerSignedLog, absoluteDegreeNormalizedLowerMagnitude,
    selectedLowerSignedLog_eq_neg_magnitude, neg_div]

theorem normalizedUpperSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    absoluteDegreeNormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters =
      -absoluteDegreeNormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters := by
  simp only [absoluteDegreeNormalizedUpperSignedLog, absoluteDegreeNormalizedUpperMagnitude,
    selectedUpperSignedLog_eq_neg_magnitude, neg_div]

/-- The same arithmetic normalization also preserves the actual signed q sum. -/
theorem absoluteDegreeNormalizedSignedLog_invariant
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val) :
    absoluteDegreeNormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters =
      absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters := by
  rw [normalizedUpperSignedLog_eq_neg_magnitude,
    normalizedLowerSignedLog_eq_neg_magnitude, absoluteDegreeNormalizedMagnitude_invariant]

theorem normalizedLowerSignedLog_neg
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters < 0 := by
  rw [normalizedLowerSignedLog_eq_neg_magnitude]
  exact neg_neg_of_pos
    (absoluteDegreeNormalizedLowerMagnitude_pos selectedLowerPlaces parameters selected_nonempty)

theorem abs_normalizedLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    |absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters| =
      absoluteDegreeNormalizedLowerMagnitude selectedLowerPlaces parameters := by
  rw [abs_of_neg (normalizedLowerSignedLog_neg selectedLowerPlaces parameters selected_nonempty),
    normalizedLowerSignedLog_eq_neg_magnitude, neg_neg]

end

end ArithmeticQPilotGlobalNormalization

end LeanFormal.IUT
