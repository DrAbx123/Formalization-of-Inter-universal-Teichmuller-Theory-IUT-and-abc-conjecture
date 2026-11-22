import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Quotient
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The completed carrier `K_v` of a finite place of a number field

For a number field `K` and a finite place `place`, the adic completion of the
height-one prime `place.maximalIdeal` provides the completed valued field
`K_v` and its valuation ring `O_v`; `LocalQParameter.lean` already exposes
these as `Completion` and `CompletionIntegers`.  This file adds the residue
field of the completed valuation ring and aligns it with the residue
characteristic `residueCharacteristic` of `FinitePlaces.lean`.

Main declarations:

* `CompletionResidueField place`: the residue field `O_v / m_v`;
* `charP_completionResidueField`: `O_v / m_v` has characteristic
  `residueCharacteristic place`;
* `ringChar_completionResidueField`: the corresponding `ringChar` equality;
* `valued_algebraMap_completionIntegers`: the valuation bridge between the
  number ring and the completed valuation ring;
* `completionIntegers_mem_maximalIdeal_iff_valued_lt_one`: the maximal ideal
  of `O_v` is the open unit ball;
* `algebraMap_completion_injective` and the `CharZero` instance: `K_v` is a
  characteristic-zero extension of `K`.

Consumed by item (2) of `IUT-II.prime-strips-frobenioid-boundary` and by the
place data of `IUTIII/Theorem311/SourceOriginalInput.lean` (IUT I,
Definition 3.1(a)).

The canonical ring equivalence between `O_v / m_v` and the residue field
`ResidueField place` of the number ring is *not* reproved here; it is
available, together with the residue-degree and ramification-index
comparisons and the conditional finrank consumers, in
`ABCBridge/Geometry/FinitePlaceCompletionLocalInputs.lean`
(`residueEquivAdicCompletionIntegers`,
`localInertiaDegree_eq_relativeResidueDegree`,
`localRamificationIndex_eq_relativeRamificationIndex`,
`finrank_adicCompletion_eq_relativeCompletionDegree_of_isIntegralClosure`).
This file keeps `Foundations` free of `ABCBridge` imports and proves only
the characteristic alignment, through the valuation bridge; the finiteness
of `O_w` over `O_v` is a separate open input recorded in that file.

## Boundary: the geometric fundamental group (S13, not constructed)

The projection `DPrimeStrip.proj` should eventually be the surjection from
the etale fundamental group of a curve onto the absolute Galois group of the
base field, whose kernel `pi_1^geo` carries the arithmetic content of the
strip; in the current instances it is the identity, so the geometric kernel
is trivial.  A faithful statement requires: a smooth, proper, geometrically
connected curve `X` over `K` with a geometric base point, the etale
fundamental group `pi_1^et(X)` as a profinite group, base change to the
algebraic closure of `K`, and the functorial exact sequence
`1 -> pi_1^geo -> pi_1^et(X) -> Gal(Kbar/K) -> 1`.  Mathlib 4.32.2 has
field-level Galois theory but no etale fundamental group of a curve, and the
kernel cannot be replaced by an arbitrary group.  The frozen interface and
its consumers are recorded as `geometricPiOneBoundary` below; no object is
constructed here.
-/

namespace LeanFormal.IUT

universe u

namespace NumberFieldFinitePlace

variable {K : Type u} [Field K] [NumberField K]

/-- The residue field of the completed valuation ring `O_v` of a finite
place: the residue field of `CompletionIntegers`. -/
abbrev CompletionResidueField (place : NumberField.FinitePlace K) :=
  IsLocalRing.ResidueField (CompletionIntegers place)

/-- For an element of the number ring, its image in the completed valuation
ring sits inside the completion with its global valuation. -/
theorem valued_algebraMap_completionIntegers
    (place : NumberField.FinitePlace K)
    (r : NumberField.RingOfIntegers K) :
    Valued.v ((algebraMap (NumberField.RingOfIntegers K)
        (CompletionIntegers place) r : CompletionIntegers place) :
        Completion place) =
      (underlyingPrime place).valuation K
        (algebraMap (NumberField.RingOfIntegers K) K r) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := underlyingPrime place)
    (k := algebraMap (NumberField.RingOfIntegers K) K r)

/-- An element of the completed valuation ring lies in its maximal ideal
exactly when its valuation is strictly below one. -/
theorem completionIntegers_mem_maximalIdeal_iff_valued_lt_one
    (place : NumberField.FinitePlace K)
    {x : CompletionIntegers place} :
    x ∈ IsLocalRing.maximalIdeal (CompletionIntegers place) ↔
      Valued.v (x : Completion place) < 1 :=
  Valuation.mem_maximalIdeal_iff (Completion place)
    (Valued.v : Valuation (Completion place) (WithZero (Multiplicative Int)))

/-- The completion embedding of a number field at a finite place is
injective. -/
theorem algebraMap_completion_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (algebraMap K (Completion place)) := by
  intro x y hxy
  have hzero : (x - y : K) = 0 := by
    refine (Valuation.zero_iff ((underlyingPrime place).valuation K)).mp ?_
    have hmapsub : ((x - y : K) : Completion place) = 0 := by
      have h : algebraMap K (Completion place) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      exact h
    have hval : Valued.v ((x - y : K) : Completion place) = 0 := by
      rw [hmapsub, map_zero]
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (v := underlyingPrime place) (k := x - y)]
    exact hval
  exact sub_eq_zero.mp hzero

/-- The completion at a finite place is a characteristic-zero field. -/
noncomputable instance instCharZeroCompletion
    (place : NumberField.FinitePlace K) : CharZero (Completion place) :=
  charZero_of_injective_algebraMap (algebraMap_completion_injective place)

/-- The residue field of the completed valuation ring of a finite place
carries the residue characteristic of that place. -/
theorem charP_completionResidueField
    (place : NumberField.FinitePlace K) :
    CharP (CompletionResidueField place) (residueCharacteristic place) := by
  haveI hResidue : CharP (ResidueField place) (residueCharacteristic place) :=
    ringChar.of_eq rfl
  refine ⟨fun m => ?_⟩
  constructor
  · intro hm
    have hm_residue : IsLocalRing.residue (CompletionIntegers place)
        (m : CompletionIntegers place) = 0 := by
      have hcast : (m : CompletionResidueField place) =
          IsLocalRing.residue (CompletionIntegers place)
            (m : CompletionIntegers place) :=
        (map_natCast (IsLocalRing.residue (CompletionIntegers place)) m).symm
      exact hcast ▸ hm
    have hm_mem : (m : CompletionIntegers place) ∈
        IsLocalRing.maximalIdeal (CompletionIntegers place) :=
      (IsLocalRing.residue_eq_zero_iff
        (m : CompletionIntegers place)).mp hm_residue
    have hm_val : Valued.v ((m : CompletionIntegers place) :
        Completion place) < 1 :=
      (completionIntegers_mem_maximalIdeal_iff_valued_lt_one place).mp
        hm_mem
    have hm_up : Valued.v ((algebraMap (NumberField.RingOfIntegers K)
        (CompletionIntegers place) (m : NumberField.RingOfIntegers K) :
          CompletionIntegers place) : Completion place) < 1 := by
      have hcoe : ((m : CompletionIntegers place) : Completion place) =
          ((algebraMap (NumberField.RingOfIntegers K)
            (CompletionIntegers place)
            (m : NumberField.RingOfIntegers K) :
              CompletionIntegers place) : Completion place) :=
        congrArg (fun y : CompletionIntegers place =>
          (y : Completion place))
          (map_natCast (algebraMap (NumberField.RingOfIntegers K)
            (CompletionIntegers place)) m).symm
      rwa [hcoe] at hm_val
    have hm_val' : (underlyingPrime place).valuation K
        (algebraMap (NumberField.RingOfIntegers K) K
          (m : NumberField.RingOfIntegers K)) < 1 := by
      rwa [valued_algebraMap_completionIntegers place
        (m : NumberField.RingOfIntegers K)] at hm_up
    have hm_mem_v : (m : NumberField.RingOfIntegers K) ∈
        (underlyingPrime place).asIdeal :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)
        (v := underlyingPrime place)
        (m : NumberField.RingOfIntegers K)).mp hm_val'
    have hm_zero : (m : ResidueField place) = 0 := by
      have hker : Ideal.Quotient.mk (underlyingPrime place).asIdeal
          (m : NumberField.RingOfIntegers K) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hm_mem_v
      have hcast : Ideal.Quotient.mk (underlyingPrime place).asIdeal
          (m : NumberField.RingOfIntegers K) =
            (m : ResidueField place) :=
        map_natCast (Ideal.Quotient.mk
          (underlyingPrime place).asIdeal) m
      exact hcast ▸ hker
    exact (CharP.cast_eq_zero_iff (ResidueField place)
      (residueCharacteristic place) m).mp hm_zero
  · intro hpm
    have hp_mem :
        (residueCharacteristic place : NumberField.RingOfIntegers K) ∈
          (underlyingPrime place).asIdeal :=
      Ideal.natCast_mem_of_charP_quotient (residueCharacteristic place)
        (underlyingPrime place).asIdeal
    have hp_global : (underlyingPrime place).valuation K
        (algebraMap (NumberField.RingOfIntegers K) K
          (residueCharacteristic place :
            NumberField.RingOfIntegers K)) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)
        (v := underlyingPrime place)
        (residueCharacteristic place :
          NumberField.RingOfIntegers K)).mpr hp_mem
    have hp_up : Valued.v ((algebraMap (NumberField.RingOfIntegers K)
        (CompletionIntegers place)
        (residueCharacteristic place : NumberField.RingOfIntegers K) :
          CompletionIntegers place) : Completion place) < 1 := by
      rwa [← valued_algebraMap_completionIntegers place
        (residueCharacteristic place : NumberField.RingOfIntegers K)]
        at hp_global
    have hp_val : Valued.v
        ((residueCharacteristic place : CompletionIntegers place) :
          Completion place) < 1 := by
      have hcoe : ((algebraMap (NumberField.RingOfIntegers K)
          (CompletionIntegers place)
          (residueCharacteristic place : NumberField.RingOfIntegers K) :
            CompletionIntegers place) : Completion place) =
          ((residueCharacteristic place : CompletionIntegers place) :
            Completion place) :=
        congrArg (fun y : CompletionIntegers place =>
          (y : Completion place))
          (map_natCast (algebraMap (NumberField.RingOfIntegers K)
            (CompletionIntegers place)) (residueCharacteristic place))
      rwa [hcoe] at hp_up
    have hp_mem' :
        (residueCharacteristic place : CompletionIntegers place) ∈
          IsLocalRing.maximalIdeal (CompletionIntegers place) :=
      (completionIntegers_mem_maximalIdeal_iff_valued_lt_one place).mpr
        hp_val
    have hp_zero : (residueCharacteristic place :
        CompletionResidueField place) = 0 := by
      have hres : IsLocalRing.residue (CompletionIntegers place)
          (residueCharacteristic place : CompletionIntegers place) = 0 :=
        (IsLocalRing.residue_eq_zero_iff
          (residueCharacteristic place : CompletionIntegers place)).mpr
          hp_mem'
      have hcast : (residueCharacteristic place :
          CompletionResidueField place) =
          IsLocalRing.residue (CompletionIntegers place)
            (residueCharacteristic place : CompletionIntegers place) :=
        (map_natCast (IsLocalRing.residue (CompletionIntegers place))
          (residueCharacteristic place)).symm
      exact hcast ▸ hres
    obtain ⟨k, hk⟩ := hpm
    rw [hk, Nat.cast_mul, hp_zero, zero_mul]

/-- The residue characteristic of the completed valuation ring at a finite
place is the residue characteristic of that place. -/
theorem ringChar_completionResidueField
    (place : NumberField.FinitePlace K) :
    ringChar (CompletionResidueField place) = residueCharacteristic place := by
  haveI := charP_completionResidueField place
  exact ringChar.eq (CompletionResidueField place) (residueCharacteristic place)

end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def numberFieldPlaceCompletionCarrier : Obligation :=
  { id := "Foundations.NumberField.place-completion-carrier"
    source :=
      "Completion of a number field at a finite place; IUT I, Definition " ++
        "3.1(a) place-data prerequisite"
    status := VerificationStatus.proved
    note :=
      "For a number field K and a finite place, the completed valued field " ++
        "K_v and its valuation ring O_v reuse the abbreviations Completion " ++
        "and CompletionIntegers, with the discrete valuation-ring structure " ++
        "supplied by Mathlib's adic-completion API. Additions proved here: " ++
        "the residue field of O_v (CompletionResidueField); the " ++
        "characteristic alignment CharP (O_v / m_v) (residueCharacteristic " ++
        "place) and its ringChar form; the valuation bridge between the " ++
        "number ring and O_v; the characterization of the maximal ideal of " ++
        "O_v as the open unit ball; and injectivity and characteristic zero " ++
        "of the completion embedding. This file keeps Foundations free of " ++
        "ABCBridge imports: the canonical residue-field equivalence and the " ++
        "e/f comparisons are not reproved here but live in " ++
        "ABCBridge/Geometry/FinitePlaceCompletionLocalInputs.lean " ++
        "(residueEquivAdicCompletionIntegers, " ++
        "localInertiaDegree_eq_relativeResidueDegree, " ++
        "localRamificationIndex_eq_relativeRamificationIndex, and the " ++
        "conditional finrank consumer forms); that file also records the " ++
        "still-open finiteness input Module.Finite O_v O_w."
    dependsOn := [ "Foundations.NumberField.finite-places" ] }

def geometricPiOneBoundary : Obligation :=
  { id := "IUT-II.prime-strips-boundary.geometric-pi-one"
    source :=
      "IUT II, Sections 3-6: geometric fundamental group of the base " ++
        "curve; consumers IUT III, Proposition 3.5 / Theorem 3.11(ii)"
    status := VerificationStatus.pending
    note :=
      "Frozen interface, not constructed. Objects: a smooth proper " ++
        "geometrically connected curve X over a number field K; a geometric " ++
        "base point; the etale fundamental group pi_1^et(X) as a profinite " ++
        "group; the base change of X to the algebraic closure of K. " ++
        "Assumptions: X smooth, proper, geometrically connected, with the " ++
        "base point geometric. Conclusion: the functorial surjection " ++
        "pi_1^et(X) -> Gal(Kbar/K) with kernel pi_1^geo, i.e. the exact " ++
        "sequence 1 -> pi_1^geo -> pi_1^et(X) -> Gal(Kbar/K) -> 1, " ++
        "realizing DPrimeStrip.proj with geometric kernel " ++
        "DPrimeStrip.geometric (currently the identity projection, hence a " ++
        "trivial kernel). Consumers: item (1) of " ++
        "IUT-II.prime-strips-frobenioid-boundary, the Frobenioid input of " ++
        "IUTII/Kummer/VerticalLogKummer.lean, and the K1/K2 realization of " ++
        "IUTIII/Theorem311/SourceK1K2Construction.lean. Mathlib 4.32.2 " ++
        "provides field-level Galois groups but no etale fundamental group " ++
        "of a curve; the kernel is arithmetic content and cannot be " ++
        "replaced by an arbitrary group."
    dependsOn := [] }

end LeanFormal.IUT.Audit
