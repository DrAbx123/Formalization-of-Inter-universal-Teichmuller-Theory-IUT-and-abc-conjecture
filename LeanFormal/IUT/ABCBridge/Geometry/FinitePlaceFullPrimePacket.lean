import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The full finite packet over one rational prime

Its coordinates are all actual finite places above p. Finiteness follows
by embedding this fiber into the finite set of prime ideals over the
corresponding rational prime ideal, rather than assuming a finite list
has covered the fiber.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

def rationalFinitePlace (p : ℕ) [Fact p.Prime] : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk
    ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
      ⟨p, Fact.out⟩)

theorem comap_eq_rationalFinitePlace (place : FinitePlaceAtPrime K p) :
    comap (k := ℚ) place.val = rationalFinitePlace p := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  have hprime : completionRationalPrime place.val = ⟨p, Fact.out⟩ :=
    Subtype.ext place.property
  simpa only [completionRationalPrime, rationalFinitePlace,
    NumberField.FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using hprime

def fullPrimePlaceIdealEmbedding : FinitePlaceAtPrime K p ↪
    (rationalFinitePlace p).maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) where
  toFun place := by
    refine ⟨place.val.maximalIdeal.asIdeal, inferInstance, ?_⟩
    simpa only [comap_eq_rationalFinitePlace place] using
      (comap_liesOver (k := ℚ) place.val)
  inj' first second heq := by
    apply Subtype.ext
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact congrArg Subtype.val heq

theorem fullPrimePlaceIdealEmbedding_surjective :
    Function.Surjective (fullPrimePlaceIdealEmbedding (K := K) (p := p)) := by
  intro primeIdeal
  have hnonzero : primeIdeal.val ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (rationalFinitePlace p).maximalIdeal.ne_bot primeIdeal.property
  let prime : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    ⟨primeIdeal.val, primeIdeal.property.1, hnonzero⟩
  let place := NumberField.FinitePlace.mk prime
  have hcomap : comap (k := ℚ) place = rationalFinitePlace p := by
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [comap_maximalIdeal]
    change Ideal.comap
      (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K))
      (NumberField.FinitePlace.mk prime).maximalIdeal.asIdeal = _
    rw [NumberField.FinitePlace.maximalIdeal_mk]
    exact ((Ideal.liesOver_iff _ _).mp primeIdeal.property.2).symm
  refine ⟨⟨place, ?_⟩, ?_⟩
  · unfold completionRationalPrime
    rw [hcomap]
    simp only [rationalFinitePlace, NumberField.FinitePlace.maximalIdeal_mk,
      Equiv.apply_symm_apply]
  · apply Subtype.ext
    change (NumberField.FinitePlace.mk prime).maximalIdeal.asIdeal = primeIdeal.val
    rw [NumberField.FinitePlace.maximalIdeal_mk]

def fullPrimePlaceIdealEquiv : FinitePlaceAtPrime K p ≃
    (rationalFinitePlace p).maximalIdeal.asIdeal.primesOver (NumberField.RingOfIntegers K) :=
  Equiv.ofBijective fullPrimePlaceIdealEmbedding
    ⟨fullPrimePlaceIdealEmbedding.injective, fullPrimePlaceIdealEmbedding_surjective⟩

instance nonempty_fullPrimePlaces : Nonempty (FinitePlaceAtPrime K p) := by
  obtain ⟨primeIdeal⟩ := Ideal.nonempty_primesOver
    (S := NumberField.RingOfIntegers K) (rationalFinitePlace p).maximalIdeal.asIdeal
  obtain ⟨place, _⟩ := fullPrimePlaceIdealEmbedding_surjective primeIdeal
  exact ⟨place⟩

instance finite_fullPrimePlaces : Finite (FinitePlaceAtPrime K p) :=
  Finite.of_injective fullPrimePlaceIdealEmbedding fullPrimePlaceIdealEmbedding.injective

instance fintype_fullPrimePlaces : Fintype (FinitePlaceAtPrime K p) := Fintype.ofFinite _

abbrev FullPrimeCompletionPacket (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :=
  CompletionPacket (fun place : FinitePlaceAtPrime K p => place)

instance fullPrimeCompletionPacketNontrivial : Nontrivial (FullPrimeCompletionPacket K p) :=
  inferInstanceAs (Nontrivial ((place : FinitePlaceAtPrime K p) → CommonPrimeCompletion place))

def fullPrimePacketLogRegion : Set (FullPrimeCompletionPacket K p) :=
  completionPacketLogRegion (fun place : FinitePlaceAtPrime K p => place)

theorem isCompact_fullPrimePacketLogRegion :
    IsCompact (fullPrimePacketLogRegion (K := K) (p := p)) :=
  isCompact_completionPacketLogRegion _

theorem rat_span_fullPrimePacketLogRegion_eq_top :
    Submodule.span ℚ (fullPrimePacketLogRegion (K := K) (p := p)) = ⊤ :=
  rat_span_completionPacketLogRegion_eq_top _

variable (K p) {ι : Type*} [Finite ι] [Nonempty ι]

theorem fullPrimeArithmeticIQCarrier_eq_top :
    arithmeticIQCarrier (fun (_ : ι) (place : FinitePlaceAtPrime K p) => place) = ⊤ :=
  arithmeticIQCarrier_eq_top _

end

end LeanFormal.IUT.NumberFieldFinitePlace
