import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
# C1 native place slice

Read the Definition 3.1(e) selected places, their base-place bijection, the
finite/infinite index conversion, and the selected-place subtype.  No arbitrary
external V and no old selected realization are input.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeC1

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Finite place carrier identifies with the height-one prime index. -/
noncomputable def finitePlaceIndexEquiv {K : Type u} [Field K] [NumberField K] :
    NumberField.FinitePlace K ≃ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) where
  toFun := NumberFieldFinitePlace.underlyingPrime
  invFun := NumberField.FinitePlace.mk
  left_inv := NumberFieldFinitePlace.mk_underlyingPrime
  right_inv := NumberField.FinitePlace.maximalIdeal_mk

/-- Convert the disjoint finite/infinite place carrier to the index sum. -/
def placeToIndex {K : Type u} [Field K] [NumberField K] :
    NumberFieldPlace K → NumberFieldPlaceIndex (F := K)
  | NumberFieldPlace.finite p => Sum.inl (finitePlaceIndexEquiv p)
  | NumberFieldPlace.infinite p => Sum.inr p

def placeOfIndex {K : Type u} [Field K] [NumberField K] :
    NumberFieldPlaceIndex (F := K) → NumberFieldPlace K
  | Sum.inl p => NumberFieldPlace.finite (finitePlaceIndexEquiv.symm p)
  | Sum.inr p => NumberFieldPlace.infinite p

theorem placeOfIndex_toIndex {K : Type u} [Field K] [NumberField K]
    (P : NumberFieldPlace K) : placeOfIndex (placeToIndex P) = P := by
  cases P <;> simp [placeOfIndex, placeToIndex]

theorem placeToIndex_ofIndex {K : Type u} [Field K] [NumberField K]
    (P : NumberFieldPlaceIndex (F := K)) : placeToIndex (placeOfIndex P) = P := by
  cases P <;> simp [placeOfIndex, placeToIndex]

noncomputable def placeIndexEquiv {K : Type u} [Field K] [NumberField K] :
    NumberFieldPlace K ≃ NumberFieldPlaceIndex (F := K) where
  toFun := placeToIndex
  invFun := placeOfIndex
  left_inv := placeOfIndex_toIndex
  right_inv := placeToIndex_ofIndex

/-- The native places, first as base places, then as the finite/infinite index. -/
noncomputable def nativePlaceIndexEquiv :
    NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod) :=
  (nativePlaceEquiv X.S).trans placeIndexEquiv

/-- Native place equivalence to the disjoint place carrier is the C1 place bijection. -/
noncomputable def placeEquiv : NativePlaces X.S ≃ NumberFieldPlace X.S.arithmetic.Fmod :=
  nativePlaceEquiv X.S

theorem placeEquiv_comap (v : NativePlaces X.S) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1 = placeEquiv X v :=
  nativePlaceEquiv_comap X.S v

theorem selected_place_mem (v : NativePlaces X.S) :
    v.1 ∈ X.S.tuple.source.V := v.2


/-- Actual local field at a native selected place. -/
noncomputable def localFieldAt (v : NativePlaces X.S) : Type _ :=
  placeLocalField (F := X.S.arithmetic.Fmod) (nativePlaceIndexEquiv X v)



/-- Actual local value-group carrier at a native selected place. -/
abbrev valueGroupAt (v : NativePlaces X.S) : Type _ :=
  match nativePlaceIndexEquiv X v with
  | Sum.inl _ => finitePlaceValueGroup
  | Sum.inr _ => archimedeanValueGroup

instance valueGroupAtCommMonoid (v : NativePlaces X.S) : CommMonoid (valueGroupAt X v) := by
  unfold valueGroupAt
  split <;> infer_instance


/-- Restriction map between the base and K adic completions at a finite place. -/
noncomputable def completionRestriction
    (p : NumberField.FinitePlace X.S.arithmetic.K) :
    (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.adicCompletion
        X.S.arithmetic.Fmod →+*
      p.maximalIdeal.adicCompletion X.S.arithmetic.K :=
  NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) p


theorem completionRestriction_coe
    (p : NumberField.FinitePlace X.S.arithmetic.K) (x : X.S.arithmetic.Fmod) :
    completionRestriction X p
        (x : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.adicCompletion
          X.S.arithmetic.Fmod) =
      (algebraMap X.S.arithmetic.Fmod X.S.arithmetic.K x :
        p.maximalIdeal.adicCompletion X.S.arithmetic.K) :=
  NumberFieldFinitePlace.completionMap_coe (k := X.S.arithmetic.Fmod) p x

theorem completionRestriction_valuation
    (p : NumberField.FinitePlace X.S.arithmetic.K)
    (x : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.adicCompletion
      X.S.arithmetic.Fmod) :
    Valued.v x ^
        (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.asIdeal.ramificationIdx'
          p.maximalIdeal.asIdeal =
      Valued.v (completionRestriction X p x) :=
  NumberFieldFinitePlace.valuation_completionMap (k := X.S.arithmetic.Fmod) p x


/-- A bad finite base place selected from native nonemptiness. -/
noncomputable def badBasePlace : NumberField.FinitePlace X.S.arithmetic.Fmod :=
  Classical.choose (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

theorem badBasePlace_mem :
    badBasePlace X ∈ X.S.tuple.source.V_mod_bad :=
  Classical.choose_spec (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

/-- The corresponding selected K-place, finite over the bad base place. -/
noncomputable def badPlace : NativePlaces X.S :=
  X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite (badBasePlace X))

theorem badPlace_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) (badPlace X).1 =
      NumberFieldPlace.finite (badBasePlace X) := by
  have h : X.S.tuple.source.V_mod_bijection.symm (badPlace X) =
      NumberFieldPlace.finite (badBasePlace X) := by
    unfold badPlace
    rw [Equiv.symm_apply_apply]
  exact (X.S.tuple.source.V_place_comap (badPlace X)).trans h

/-- All-place local tower restriction: for every finite K-place `p` and every
base element `x`, restricting to the `Fmod`-completion and then using the
tower `Fmod -> F -> K` agrees with the `F`-completion map followed by the
`Fmod -> F` algebra map.  This is the full-quantifier tower law, not a
selected-place special case. -/
theorem completionRestriction_tower_coe
    (p : NumberField.FinitePlace X.S.arithmetic.K)
    (x : X.S.arithmetic.Fmod) :
    completionRestriction X p
        (x : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.adicCompletion
          X.S.arithmetic.Fmod) =
      NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.F) p
        (algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F x :
          (NumberFieldFinitePlace.comap (k := X.S.arithmetic.F) p).maximalIdeal.adicCompletion
            X.S.arithmetic.F) := by
  rw [completionRestriction,
    NumberFieldFinitePlace.completionMap_coe (k := X.S.arithmetic.Fmod) p x,
    NumberFieldFinitePlace.completionMap_coe (k := X.S.arithmetic.F) p
      (algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F x)]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  simpa using IsScalarTower.algebraMap_apply X.S.arithmetic.Fmod X.S.arithmetic.F
    X.S.arithmetic.K x

/-- Full-quantifier form of the tower restriction law over all finite K-places
and all base elements. -/
theorem completionRestriction_tower_all :
    ∀ (p : NumberField.FinitePlace X.S.arithmetic.K) (x : X.S.arithmetic.Fmod),
      completionRestriction X p
          (x : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) p).maximalIdeal.adicCompletion
            X.S.arithmetic.Fmod) =
        NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.F) p
          (algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F x :
            (NumberFieldFinitePlace.comap (k := X.S.arithmetic.F) p).maximalIdeal.adicCompletion
              X.S.arithmetic.F) := by
  intro p x
  exact completionRestriction_tower_coe X p x

/-- Exact missing production target for the strip/fiber comparison: every
native theater strip fiber at every native place maps to the actual local
value group.  No inhabitant is asserted and this is NOT a C1 input field. -/
structure NativeStripFiberComparison (X : N8NativeInput l) where
  /-- Fiber comparison for every theater index and every native place. -/
  fiberMonEquiv : ∀ (i : X.family.index) (v : NativePlaces X.S),
    (X.family.theater i).primeStrip.Mon v ≃* valueGroupAt X v

/-- The exact missing production declaration for the strip/fiber comparison.
It is an obligation, not an input, and has no constructed inhabitant here. -/
def NativeStripFiberComparisonObligation (X : N8NativeInput l) : Prop :=
  Nonempty (NativeStripFiberComparison X)

end LeanFormal.IUT.N8Closure.NativeC1