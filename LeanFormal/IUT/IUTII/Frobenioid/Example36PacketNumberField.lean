/-
  # The concrete packet number field of the source theater (IUT III, Example 3.6)

  The source theater of `Example36SourceTheaterCarrier` is built from the
  Gaussian initial Theta data: its number field is the concrete quadratic field
  Q(i), already constructed in `ConcreteArithmeticExample` as the AdjoinRoot
  model `GaussianField`.  The handoff Chapter 1, section J1 asks for the actual
  packet number field, not merely generic place data.  This module constructs
  the packet as a concrete arithmetic object:

  * `packetNumberField` is the concrete Gaussian number field, with its
    `NumberField` structure and the computation `finrank_Q = 2` of its degree
    (`packetNumberField_finrank`);
  * `packetPlaceIndex` is the actual place index, the disjoint union of the
    actual finite places (height-one primes of the ring of integers) and the
    actual archimedean places (`NumberField.InfinitePlace`); it is proved
    equivalent to the repository's full place carrier `NumberFieldPlace`
    (`packetPlaceEquiv`), and the finite and archimedean ranges are proved to
    cover all places and to be disjoint (`packetPlaceSet_eq_union`,
    `packetFinitePlaceSet_disjoint_infinitePlaceSet`);
  * the selected finite place is the actual height-one prime of the source
    theater, proved to lie over the rational prime 5
    (`packetFinitePlace_natGenerator`), proved equal to the boundary place of
    the concrete source Frobenioid (`packetFinitePlace_eq_boundaryPlace`),
    and its maximal ideal is the concrete height-one prime
    (`packetHeightOneSpectrum_eq_concrete`);
  * the actual archimedean place is constructed from an explicit complex
    embedding i |-> I; it is proved complex, every archimedean place of the
    field is proved equal to it, and the archimedean place set is exactly the
    singleton of this place;
  * `packetCompletion` is the actual completion at every place: the actual
    `v.adicCompletion Q(i)` at a finite place and the actual
    `w.Completion` at an archimedean place; the concrete archimedean
    completion is proved ring-equivalent to C
    (`packetArchimedeanCompletionRingEquivComplex`) and isometric to C
    (`packetArchimedeanCompletionIsometryEquivComplex`);
  * the local value data of Example 3.6 is instantiated at both selected
    places (`packetFiniteLocalValueData`, `packetInfiniteLocalValueData`,
    `packetGlobalPlaceData`); the finite completion valuation is identified
    with the global finite coordinate
    (`packetFiniteCompletion_valuation_eq_global`), and the archimedean
    coordinate is identified with the logarithm of the completion norm
    (`packetInfiniteLocalValueData_deltaAdd_eq_log_completionNorm`) and with
    the existing archimedean additive character `absLogAddHom`
    (`packetInfiniteLocalValueData_deltaAdd_eq_absLogAddHom`);
  * the packet field is identified with the source theater data by actual
    theorems about the concrete `sourceTheater`: its `Fmod`, `F`, and `K`
    are the packet field
    (`sourceTheater_arithmetic_Fmod_eq_packet`,
    `sourceTheater_arithmetic_F_eq_packet`,
    `sourceTheater_arithmetic_K_eq_packet`), the selected finite place is
    the boundary place of the concrete source Frobenioid
    (`packetFinitePlace_eq_boundaryPlace`), and the concrete finite local
    field is the packet completion
    (`packetFiniteCompletion_eq_placeLocalField`,
    `packetFiniteCompletion_eq_boundaryCompletion`).

  Boundary: this is the arithmetic packet field and its place/completion data.
  It does not construct the source Hodge theater, the local Galois invariant
  monoid, the log-link compatibility, the prime-strip components, or any
  theta/q-pilot identification.  No frozen structure card is introduced: every
  object below is a concrete type or an actual Mathlib construction, and the
  only definitional identities are the unfoldings of the concrete
  abbreviations that name those constructions.  The substantive inputs are the
  arithmetic separability/degree computation, the explicit complex embedding,
  the over-5 place computation, the complex-place uniqueness theorem, the
  Mathlib completion ring/isometry equivalence, the global/local valuation
  bridge, and the logarithm of the completion norm.  In particular the
  source-theater equalities are *not* obtained from a detached structure card:
  the carrier data is the actual `HodgeTheater` produced by
  `concreteInitialThetaCStage`, and the equalities are computed from its
  concrete arithmetic record.
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianLocalGalois
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceCompletionBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace PacketNumberFieldConstruction

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaussianPlaceStrip
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaussianLocalGalois
open IsDedekindDomain
open scoped NumberField

local instance packetGaussianPolynomialIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The concrete packet number field and its degree -/

/-- The concrete packet number field of the source theater: the Gaussian field
Q(i) used by the concrete initial Theta data. -/
abbrev packetNumberField : Type := GaussianField

instance packetNumberFieldField : Field packetNumberField :=
  inferInstanceAs (Field GaussianField)

instance packetNumberFieldNumberField : NumberField packetNumberField :=
  gaussianFieldNumberField

/-- The defining square root of -1 in the packet number field. -/
def packetSqrtNegOne : packetNumberField :=
  AdjoinRoot.root gaussianPolynomial

/-- The defining relation of the packet number field: the chosen square root of
-1 really squares to -1. -/
theorem packetSqrtNegOne_sq : packetSqrtNegOne * packetSqrtNegOne = -1 := by
  have h := root_X_pow_sub_C_pow (K := ℚ) 2 (-1)
  simpa [packetSqrtNegOne, gaussianPolynomial, pow_two] using h

/-- The packet number field is two-dimensional over Q. -/
theorem packetNumberField_finrank :
    Module.finrank ℚ packetNumberField = 2 := by
  change Module.finrank ℚ
    (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) = 2
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ).Monic :=
    Polynomial.monic_X_pow_sub_C (-1) (by norm_num)
  rw [(AdjoinRoot.powerBasis' hmonic).finrank]
  rw [AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]

/-- The packet number field is not the rational field: its degree is two. -/
theorem packetNumberField_finrank_ne_one :
    Module.finrank ℚ packetNumberField ≠ 1 := by
  rw [packetNumberField_finrank]
  norm_num

/-! ## 2. The actual complex embedding and the archimedean place -/

/-- The explicit complex embedding of the packet number field sending the
chosen square root of -1 to the complex number I. -/
def packetComplexEmbedding : packetNumberField →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℚ ℂ) Complex.I (by
    simp)

/-- The explicit embedding sends the square root i to I. -/
@[simp]
theorem packetComplexEmbedding_sqrtNegOne :
    packetComplexEmbedding packetSqrtNegOne = Complex.I := by
  unfold packetComplexEmbedding packetSqrtNegOne
  exact AdjoinRoot.lift_root _

/-- The actual archimedean place of the packet number field defined by the
explicit complex embedding i |-> I. -/
def packetInfinitePlace : NumberField.InfinitePlace packetNumberField :=
  NumberField.InfinitePlace.mk packetComplexEmbedding

/-- Evaluation of the actual archimedean place is the norm of the explicit
complex embedding. -/
@[simp]
theorem packetInfinitePlace_apply (x : packetNumberField) :
    packetInfinitePlace x = ‖packetComplexEmbedding x‖ :=
  rfl

/-- Every complex embedding of the packet number field sends i to I or to
-I; this is the elementary root computation for X^2 + 1. -/
theorem packetEmbedding_sqrtNegOne_eq_I_or_neg (φ : packetNumberField →+* ℂ) :
    φ packetSqrtNegOne = Complex.I ∨ φ packetSqrtNegOne = -Complex.I := by
  have hsq : φ packetSqrtNegOne * φ packetSqrtNegOne = -1 := by
    rw [← map_mul, packetSqrtNegOne_sq, map_neg, map_one]
  have hfac : (φ packetSqrtNegOne - Complex.I) *
      (φ packetSqrtNegOne + Complex.I) = 0 := by
    calc
      (φ packetSqrtNegOne - Complex.I) * (φ packetSqrtNegOne + Complex.I)
          = φ packetSqrtNegOne * φ packetSqrtNegOne - Complex.I * Complex.I := by
            ring
      _ = (-1 : ℂ) - (-1 : ℂ) := by rw [hsq, Complex.I_mul_I]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfac with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    exact eq_neg_of_add_eq_zero_left h

/-- No complex embedding of the packet number field is real: evaluating at the
chosen square root of -1 gives I or -I, neither of which is fixed by complex
conjugation. -/
theorem packetEmbedding_not_isReal (φ : packetNumberField →+* ℂ) :
    ¬ NumberField.ComplexEmbedding.IsReal φ := by
  rintro hφ
  have hconj : NumberField.ComplexEmbedding.conjugate φ = φ :=
    NumberField.ComplexEmbedding.isReal_iff.mp hφ
  have hfix : star (φ packetSqrtNegOne) = φ packetSqrtNegOne := by
    simpa using RingHom.congr_fun hconj packetSqrtNegOne
  have him : (φ packetSqrtNegOne).im = 0 :=
    Complex.conj_eq_iff_im.mp hfix
  rcases packetEmbedding_sqrtNegOne_eq_I_or_neg φ with h | h <;>
    rw [h] at him <;> norm_num at him

/-- The packet number field has no real archimedean places. -/
theorem packetNrRealPlaces_eq_zero :
    NumberField.InfinitePlace.nrRealPlaces packetNumberField = 0 := by
  classical
  rw [← NumberField.InfinitePlace.card_real_embeddings]
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun φ => packetEmbedding_not_isReal φ.1 φ.2⟩

/-- The packet number field has exactly one complex archimedean place. -/
theorem packetNrComplexPlaces_eq_one :
    NumberField.InfinitePlace.nrComplexPlaces packetNumberField = 1 := by
  classical
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank packetNumberField
  rw [packetNrRealPlaces_eq_zero, packetNumberField_finrank] at h
  omega

/-- The actual archimedean place is complex. -/
theorem packetInfinitePlace_isComplex :
    packetInfinitePlace.IsComplex := by
  classical
  rcases NumberField.InfinitePlace.isReal_or_isComplex packetInfinitePlace with h | h
  · have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces packetNumberField := by
      rw [← NumberField.InfinitePlace.card_real_embeddings]
      exact Fintype.card_pos_iff.mpr
        ⟨⟨packetInfinitePlace.embedding, NumberField.InfinitePlace.isReal_iff.mp h⟩⟩
    rw [packetNrRealPlaces_eq_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  · exact h

/-- The actual archimedean place is not real. -/
theorem packetInfinitePlace_not_isReal :
    ¬ packetInfinitePlace.IsReal :=
  NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr packetInfinitePlace_isComplex

/-- There is exactly one archimedean place of the packet number field. -/
theorem packetInfinitePlace_card :
    Fintype.card (NumberField.InfinitePlace packetNumberField) = 1 := by
  classical
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    packetNrRealPlaces_eq_zero, packetNrComplexPlaces_eq_one]

/-- Every archimedean place of the packet number field is the explicit complex
place packetInfinitePlace. -/
theorem packetInfinitePlace_unique
    (w : NumberField.InfinitePlace packetNumberField) :
    w = packetInfinitePlace := by
  have hcard : Fintype.card (NumberField.InfinitePlace packetNumberField) ≤ 1 :=
    le_of_eq packetInfinitePlace_card
  exact Fintype.card_le_one_iff.mp hcard w packetInfinitePlace

/-- The actual archimedean place set of the packet number field is exactly the
singleton of the explicit complex place. -/
theorem packetInfinitePlaceSet_eq_singleton :
    (Set.univ : Set (NumberField.InfinitePlace packetNumberField)) =
      {packetInfinitePlace} := by
  ext w
  simp [packetInfinitePlace_unique w]

/-- The actual archimedean place set is nonempty. -/
theorem packetInfinitePlaceSet_nonempty :
    (Set.univ : Set (NumberField.InfinitePlace packetNumberField)).Nonempty :=
  ⟨packetInfinitePlace, Set.mem_univ _⟩

/-! ## 3. The actual finite place and the concrete height-one prime -/

/-- The selected finite place of the packet number field: the actual concrete
Gaussian place above 5 that is used by the source theater and by the concrete
source Frobenioid boundary. -/
noncomputable def packetFinitePlace : NumberField.FinitePlace packetNumberField :=
  ConcreteSourceFrobenioidBridge.concretePlace

/-- The underlying concrete finite place is the checked Gaussian place above
5 of `ConcreteFinitePlaceBoundary`. -/
theorem packetFinitePlace_eq_concreteGaussianFivePlace :
    packetFinitePlace = concreteGaussianFivePlace :=
  rfl

/-- The actual height-one prime of the packet number field at the selected
finite place: the maximal ideal of the concrete finite place. -/
noncomputable def packetHeightOneSpectrum :
    HeightOneSpectrum (𝓞 packetNumberField) :=
  packetFinitePlace.maximalIdeal

/-- The height-one prime of the packet number field is the concrete height-one
prime used by the Example 3.6 place data. -/
theorem packetHeightOneSpectrum_eq_concrete :
    packetHeightOneSpectrum =
      SourceTheaterCarrier.concreteHeightOneSpectrum :=
  rfl

/-- The selected finite place is the boundary place of the concrete source
Frobenioid of any prime label `l ≥ 5`. -/
theorem packetFinitePlace_eq_boundaryPlace (l : PrimeGeFive) :
    packetFinitePlace =
      (ConcreteSourceFrobenioidBridge.concreteSourceFrobenioidBoundary l).place := by
  rw [ConcreteSourceFrobenioidBridge.boundary_place]
  rfl

/-- The packet place restricts to the checked rational place at 5. -/
theorem packetFinitePlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace = concreteFivePlace :=
  concreteGaussianFivePlace_comap

/-- The selected finite place lies over the rational prime 5: the natural
generator of the rational prime below it is 5. -/
theorem packetFinitePlace_natGenerator :
    Rat.HeightOneSpectrum.natGenerator
      (NumberFieldFinitePlace.underlyingPrime
        (NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace)) = 5 :=
  SourceTheaterCarrier.concretePlace_rationalPrime_natGenerator

/-- The underlying height-one prime of the selected finite place is the packet
height-one prime. -/
theorem packetFinitePlace_underlyingPrime :
    NumberFieldFinitePlace.underlyingPrime packetFinitePlace =
      packetHeightOneSpectrum :=
  rfl

/-! ## 4. The full actual place set as a disjoint union -/

/-- The full place index of the packet number field: the actual finite places
(height-one primes of the ring of integers) together with the actual
archimedean places. -/
abbrev packetPlaceIndex : Type :=
  HeightOneSpectrum (𝓞 packetNumberField) ⊕
    NumberField.InfinitePlace packetNumberField

/-- The full place index is equivalent to the repository's actual finite/infinite
place carrier `NumberFieldPlace`; the equivalence retains the actual Mathlib
place objects (no place is renamed or replaced by a label). -/
noncomputable def packetPlaceEquiv :
    packetPlaceIndex ≃ NumberFieldPlace packetNumberField :=
  GaussianPlaceStrip.gaussianPlaceIndexEquiv

/-- The equivalence sends a finite place to the corresponding finite place of
the full carrier. -/
theorem packetPlaceEquiv_finite
    (v : HeightOneSpectrum (𝓞 packetNumberField)) :
    packetPlaceEquiv (Sum.inl v) =
      NumberFieldPlace.finite (NumberField.FinitePlace.mk v) :=
  rfl

/-- The equivalence sends an archimedean place to the corresponding
archimedean place of the full carrier. -/
theorem packetPlaceEquiv_infinite
    (w : NumberField.InfinitePlace packetNumberField) :
    packetPlaceEquiv (Sum.inr w) = NumberFieldPlace.infinite w :=
  rfl

/-- The finite places of the packet number field, as a set of full places. -/
def packetFinitePlaceSet : Set (NumberFieldPlace packetNumberField) :=
  Set.range (NumberFieldPlace.finite (K := packetNumberField))

/-- The archimedean places of the packet number field, as a set of full
places. -/
def packetInfinitePlaceSet : Set (NumberFieldPlace packetNumberField) :=
  Set.range (NumberFieldPlace.infinite (K := packetNumberField))

/-- **Disjoint-union decomposition of the actual place set.** Every place of the
packet number field is either a finite place or an archimedean place. -/
theorem packetPlaceSet_eq_union :
    (Set.univ : Set (NumberFieldPlace packetNumberField)) =
      packetFinitePlaceSet ∪ packetInfinitePlaceSet := by
  ext p
  cases p with
  | finite v => simp [packetFinitePlaceSet, packetInfinitePlaceSet]
  | infinite w => simp [packetFinitePlaceSet, packetInfinitePlaceSet]

/-- The finite and archimedean parts of the place set are disjoint. -/
theorem packetFinitePlaceSet_disjoint_infinitePlaceSet :
    Disjoint packetFinitePlaceSet packetInfinitePlaceSet := by
  rw [Set.disjoint_left]
  rintro p ⟨v, rfl⟩ ⟨w, h⟩
  cases h

/-! ## 5. The actual completions and the local value data -/

/-- The actual completion at every place of the packet number field: the actual
`v`-adic completion at a finite place and the actual archimedean completion
`w.Completion` at an archimedean place. -/
noncomputable def packetCompletion (P : packetPlaceIndex) : Type :=
  match P with
  | Sum.inl v => v.adicCompletion packetNumberField
  | Sum.inr w => w.Completion

/-- The completion is a field at every place. -/
noncomputable instance packetCompletionField (P : packetPlaceIndex) :
    Field (packetCompletion P) := by
  cases P with
  | inl v => exact inferInstanceAs (Field (v.adicCompletion packetNumberField))
  | inr w => exact inferInstanceAs (Field (w.Completion))

/-- At a finite place the actual completion is the `v`-adic completion. -/
theorem packetCompletion_finite
    (v : HeightOneSpectrum (𝓞 packetNumberField)) :
    packetCompletion (Sum.inl v) = v.adicCompletion packetNumberField :=
  rfl

/-- At an archimedean place the actual completion is `w.Completion`. -/
theorem packetCompletion_infinite
    (w : NumberField.InfinitePlace packetNumberField) :
    packetCompletion (Sum.inr w) = w.Completion :=
  rfl

/-- The actual completion at the selected finite place. -/
abbrev packetFiniteCompletion : Type :=
  packetHeightOneSpectrum.adicCompletion packetNumberField

/-- The actual completion at the selected archimedean place. -/
abbrev packetArchimedeanCompletion : Type :=
  packetInfinitePlace.Completion

/-- The concrete finite packet completion is the value of the place-indexed
completion at the selected finite place. -/
theorem packetFiniteCompletion_eq_packetCompletion :
    packetFiniteCompletion =
      packetCompletion (Sum.inl packetHeightOneSpectrum) :=
  rfl

/-- The concrete archimedean packet completion is the value of the place-indexed
completion at the selected archimedean place. -/
theorem packetArchimedeanCompletion_eq_packetCompletion :
    packetArchimedeanCompletion =
      packetCompletion (Sum.inr packetInfinitePlace) :=
  rfl

/-- The concrete finite packet completion is the actual `v`-adic completion
at the packet height-one prime. -/
theorem packetFiniteCompletion_eq_adicCompletion :
    packetFiniteCompletion =
      packetHeightOneSpectrum.adicCompletion packetNumberField :=
  rfl

/-- The concrete archimedean packet completion is the actual Mathlib
archimedean completion at the explicit complex place. -/
theorem packetArchimedeanCompletion_eq_completion :
    packetArchimedeanCompletion = packetInfinitePlace.Completion :=
  rfl

/-- **The archimedean completion is the complex field.** The actual completion
at the unique complex archimedean place is ring-equivalent to C, the local
field of the source theater at that place. -/
noncomputable def packetArchimedeanCompletionRingEquivComplex :
    packetArchimedeanCompletion ≃+* ℂ :=
  NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    packetInfinitePlace_isComplex

/-- The archimedean completion is isometric to C. -/
noncomputable def packetArchimedeanCompletionIsometryEquivComplex :
    packetArchimedeanCompletion ≃ᵢ ℂ :=
  NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    packetInfinitePlace_isComplex

/-- The norm of a global element inside the archimedean packet completion is
the value of the selected archimedean place. -/
theorem packetArchimedeanCompletion_norm_coe (x : packetNumberField) :
    ‖(x : packetArchimedeanCompletion)‖ = packetInfinitePlace x := by
  show ‖(x : packetInfinitePlace.Completion)‖ = packetInfinitePlace x
  rw [show (x : packetInfinitePlace.Completion) =
      ((WithAbs.toAbs packetInfinitePlace.1 x : WithAbs packetInfinitePlace.1) :
        packetInfinitePlace.Completion) from rfl]
  rw [NumberField.InfinitePlace.Completion.norm_coe]
  rfl

/-- The finite local value data of IUT III, Example 3.6 at the selected finite
place: value group Z, nonnegative integral cone, and the actual v-adic
exponent as principal map. -/
noncomputable def packetFiniteLocalValueData :
    LocalValueData packetNumberField ℤ :=
  numberFieldFiniteLocalValueData packetHeightOneSpectrum

/-- The archimedean local value data of IUT III, Example 3.6 at the selected
complex place. -/
noncomputable def packetInfiniteLocalValueData :
    LocalValueData packetNumberField ℝ :=
  numberFieldInfiniteLocalValueData packetInfinitePlace

/-- The packaged global place data of the packet number field. -/
noncomputable def packetGlobalPlaceData :
    GlobalPlaceData packetNumberField :=
  numberFieldGlobalPlaceData

/-- The principal map of the finite packet local data is the actual v-adic
exponent at the packet height-one prime. -/
theorem packetFiniteLocalValueData_deltaAdd
    (f : packetNumberFieldˣ) :
    packetFiniteLocalValueData.deltaAdd f =
      finitePlaceValueExponent packetHeightOneSpectrum f :=
  numberFieldFiniteLocalValueData_deltaAdd packetHeightOneSpectrum f

/-- **Global finite value equals the finite completion valuation.** The global
finite coordinate of a packet unit at the selected finite place is the
classical valuation exponent of its image in the actual finite packet
completion. -/
theorem packetFiniteCompletion_valuation_eq_global
    (f : packetNumberFieldˣ) :
    packetGlobalPlaceData.finiteDelta f packetHeightOneSpectrum =
      completionValuationExponent packetHeightOneSpectrum
        (Units.map (algebraMap packetNumberField
          (packetHeightOneSpectrum.adicCompletion packetNumberField)).toMonoidHom
            f) :=
  numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent
    packetHeightOneSpectrum f

/-- The finite local principal map itself is the completion valuation exponent,
i.e. the local value data and the completion valuation agree on global
units. -/
theorem packetFiniteLocalValueData_deltaAdd_eq_completionValuationExponent
    (f : packetNumberFieldˣ) :
    packetFiniteLocalValueData.deltaAdd f =
      completionValuationExponent packetHeightOneSpectrum
        (Units.map (algebraMap packetNumberField
          (packetHeightOneSpectrum.adicCompletion packetNumberField)).toMonoidHom
            f) := by
  rw [packetFiniteLocalValueData_deltaAdd]
  have h := packetFiniteCompletion_valuation_eq_global f
  rw [show packetGlobalPlaceData.finiteDelta f packetHeightOneSpectrum =
      numberFieldGlobalPlaceData.finiteDelta f packetHeightOneSpectrum from rfl,
    numberFieldGlobalPlaceData_finiteDelta] at h
  exact h

/-- The principal map of the archimedean packet local data is the archimedean
coordinate `-log (w .)` at the complex place. -/
theorem packetInfiniteLocalValueData_deltaAdd
    (f : packetNumberFieldˣ) :
    packetInfiniteLocalValueData.deltaAdd f =
      archimedeanPlaceValue packetInfinitePlace f :=
  numberFieldInfiniteLocalValueData_deltaAdd packetInfinitePlace f

/-- **The archimedean coordinate is the logarithm of the completion norm.**
For a packet unit, the archimedean local coordinate equals minus the logarithm
of the norm of its image in the actual archimedean packet completion. -/
theorem packetInfiniteLocalValueData_deltaAdd_eq_log_completionNorm
    (f : packetNumberFieldˣ) :
    packetInfiniteLocalValueData.deltaAdd f =
      -Real.log ‖((f : packetNumberField) : packetArchimedeanCompletion)‖ := by
  rw [packetInfiniteLocalValueData_deltaAdd, archimedeanPlaceValue,
    packetArchimedeanCompletion_norm_coe]

/-- The archimedean coordinate is the existing archimedean additive character
`absLogAddHom` of the actual packet completion, applied to the image unit. -/
theorem packetInfiniteLocalValueData_deltaAdd_eq_absLogAddHom
    (f : packetNumberFieldˣ) :
    packetInfiniteLocalValueData.deltaAdd f =
      absLogAddHom packetArchimedeanCompletion
        (Additive.ofMul (Units.map (algebraMap packetNumberField
          packetArchimedeanCompletion).toMonoidHom f)) := by
  rw [packetInfiniteLocalValueData_deltaAdd_eq_log_completionNorm,
    absLogAddHom_ofMul]
  simp [Units.coe_map, NumberField.InfinitePlace.Completion.algebraMap_apply]

/-- The finite coordinate of the global packet place data is the actual v-adic
exponent at every finite place. -/
theorem packetGlobalPlaceData_finiteDelta
    (f : packetNumberFieldˣ)
    (v : HeightOneSpectrum (𝓞 packetNumberField)) :
    packetGlobalPlaceData.finiteDelta f v = finitePlaceValueExponent v f :=
  numberFieldGlobalPlaceData_finiteDelta f v

/-- The archimedean coordinate of the global packet place data is
`-log (w .)` at every archimedean place. -/
theorem packetGlobalPlaceData_infiniteDelta
    (f : packetNumberFieldˣ)
    (w : NumberField.InfinitePlace packetNumberField) :
    packetGlobalPlaceData.infiniteDelta f w =
      -Real.log (w (f : packetNumberField)) :=
  numberFieldGlobalPlaceData_infiniteDelta f w

/-! ## 6. Identification with the concrete source theater -/

/-- The `Fmod` of the concrete source theater is the packet number field. -/
theorem sourceTheater_arithmetic_Fmod_eq_packet (l : PrimeGeFive) :
    (SourceTheaterCarrier.sourceTheater l).arithmetic.Fmod =
      packetNumberField := by
  rw [SourceTheaterCarrier.sourceTheater_arithmetic]
  rfl

/-- The `F` of the concrete source theater is the packet number field. -/
theorem sourceTheater_arithmetic_F_eq_packet (l : PrimeGeFive) :
    (SourceTheaterCarrier.sourceTheater l).arithmetic.F =
      packetNumberField := by
  rw [SourceTheaterCarrier.sourceTheater_arithmetic]
  rfl

/-- The `K` of the concrete source theater is the packet number field. -/
theorem sourceTheater_arithmetic_K_eq_packet (l : PrimeGeFive) :
    (SourceTheaterCarrier.sourceTheater l).arithmetic.K =
      packetNumberField := by
  rw [SourceTheaterCarrier.sourceTheater_arithmetic]
  rfl

/-- The concrete finite local field of the source theater is the packet finite
completion. -/
theorem packetFiniteCompletion_eq_placeLocalField :
    packetFiniteCompletion = placeLocalField concreteGaussianPlace := by
  show packetHeightOneSpectrum.adicCompletion packetNumberField =
    placeLocalField concreteGaussianPlace
  rw [show concreteGaussianPlace =
      finiteGaussianPlace SourceTheaterCarrier.concreteHeightOneSpectrum from rfl,
    placeLocalField_finite]
  rfl

/-- At the source theater boundary place, the concrete finite completion is the
packet finite completion. -/
theorem packetFiniteCompletion_eq_boundaryCompletion (l : PrimeGeFive) :
    packetFiniteCompletion =
      ((ConcreteSourceFrobenioidBridge.concreteSourceFrobenioidBoundary l).place.maximalIdeal).adicCompletion
        packetNumberField := by
  show packetHeightOneSpectrum.adicCompletion packetNumberField = _
  rw [packetHeightOneSpectrum]
  rw [show packetFinitePlace =
      (ConcreteSourceFrobenioidBridge.concreteSourceFrobenioidBoundary l).place from
    packetFinitePlace_eq_boundaryPlace l]

/-- The concrete archimedean local field of the source theater at the unique
complex place is C. -/
theorem packetArchimedeanLocalField_eq_complex :
    placeLocalField (infiniteGaussianPlace packetInfinitePlace) = ℂ :=
  archimedeanPlaceLocalField_eq_complex packetInfinitePlace
    packetInfinitePlace_not_isReal

/-- **Source-theater packet identification.** The concrete source theater's
three number fields are the packet field, the selected finite place is the
boundary place of the concrete source Frobenioid, and the concrete finite
completion is the packet completion at that boundary place. -/
theorem sourceTheater_packet_identification (l : PrimeGeFive) :
    (SourceTheaterCarrier.sourceTheater l).arithmetic.Fmod = packetNumberField ∧
    (SourceTheaterCarrier.sourceTheater l).arithmetic.F = packetNumberField ∧
    (SourceTheaterCarrier.sourceTheater l).arithmetic.K = packetNumberField ∧
    packetFinitePlace =
      (ConcreteSourceFrobenioidBridge.concreteSourceFrobenioidBoundary l).place ∧
    packetFiniteCompletion =
      ((ConcreteSourceFrobenioidBridge.concreteSourceFrobenioidBoundary l).place.maximalIdeal).adicCompletion
        packetNumberField := by
  exact ⟨sourceTheater_arithmetic_Fmod_eq_packet l,
    sourceTheater_arithmetic_F_eq_packet l,
    sourceTheater_arithmetic_K_eq_packet l,
    packetFinitePlace_eq_boundaryPlace l,
    packetFiniteCompletion_eq_boundaryCompletion l⟩

end PacketNumberFieldConstruction
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT
