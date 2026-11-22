/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ObjectLockDataActual
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-! # Galois ring action bridge and primesOver transitivity

Builds the trivial Gal(F/Fmod)-action on Fmod, the induced action on O_F,
the missing SMulDistribClass G (O_Fmod) (O_F), the ring-level IsGaloisGroup,
and Mathlib transitivity on primesOver.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GaloisRingBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual
open scoped Pointwise

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- Trivial Galois action on the base field Fmod. -/
noncomputable instance galoisFmodMulSemiringAction :
    MulSemiringAction (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
      T.arithmetic.Fmod where
  smul _ r := r
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The missing compatibility: the Galois action on O_F distributes over the
O_Fmod-algebra action.  Proof descends to F and uses that g fixes Fmod. -/
noncomputable instance galoisSMulDistribClass :
    SMulDistribClass (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
      (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.F) where
  smul_distrib_smul g r s := by
    have hgr : (g • r : NumberField.RingOfIntegers T.arithmetic.Fmod) = r := by
      apply NumberField.RingOfIntegers.ext
      change (g • (r : T.arithmetic.Fmod) : T.arithmetic.Fmod) = (r : T.arithmetic.Fmod)
      rfl
    apply NumberField.RingOfIntegers.ext
    simp [NumberField.RingOfIntegers.coe_eq_algebraMap,
      integralClosure.coe_smul, Algebra.smul_def, AlgEquiv.commutes, hgr]

/-- Ring-level Galois group instance. -/
noncomputable instance galoisRingIsGaloisGroup :
    IsGaloisGroup (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
      (NumberField.RingOfIntegers T.arithmetic.Fmod)
      (NumberField.RingOfIntegers T.arithmetic.F) := by
  haveI : Finite (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F) := inferInstance
  exact (IsGaloisGroup.iff_isFractionRing
    (G := T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (A := NumberField.RingOfIntegers T.arithmetic.Fmod)
    (B := NumberField.RingOfIntegers T.arithmetic.F)
    (K := T.arithmetic.Fmod) (L := T.arithmetic.F)).mpr
    ⟨inferInstance, inferInstance⟩

/-- Bridge from finite place to a prime over p. -/
noncomputable def primesOverMkPlace
    (place : NumberField.FinitePlace T.arithmetic.F)
    (p : Ideal (NumberField.RingOfIntegers T.arithmetic.Fmod))
    (h : place.maximalIdeal.asIdeal.LiesOver p) :
    Ideal.primesOver p (NumberField.RingOfIntegers T.arithmetic.F) :=
  (⟨place.maximalIdeal.asIdeal, ⟨place.maximalIdeal.isPrime, h⟩⟩ :
    Ideal.primesOver p (NumberField.RingOfIntegers T.arithmetic.F))

/-- Mathlib transitivity on primesOver, specialized. -/
theorem exists_galois_smul_primesOver
    (p : Ideal (NumberField.RingOfIntegers T.arithmetic.Fmod))
    (P Q : Ideal.primesOver p (NumberField.RingOfIntegers T.arithmetic.F)) :
    exists σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F,
      σ • P.1 = Q.1 :=
  Ideal.exists_smul_eq_of_isGaloisGroup p P.1 Q.1
    (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)


/-- The Fmod prime below both chosen places. -/
noncomputable def nativeFmodPrime (b : Bad (nativePlaceSelection T)) :
    Ideal (NumberField.RingOfIntegers T.arithmetic.Fmod) :=
  (b.1).maximalIdeal.asIdeal

theorem nativeBadFPlace_liesOver (b : Bad (nativePlaceSelection T)) :
    (nativeBadToFPlace T b).maximalIdeal.asIdeal.LiesOver (nativeFmodPrime (T := T) b) := by
  rw [Ideal.liesOver_iff, Ideal.under_def]
  rw [← NumberFieldFinitePlace.comap_maximalIdeal (k := T.arithmetic.Fmod)
    (nativeBadToFPlace T b)]
  exact congrArg (fun v => v.maximalIdeal.asIdeal)
    (nativeBadToFPlace_comap (T := T) b).symm

theorem nativeKContraction_liesOver (b : Bad (nativePlaceSelection T)) :
    (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBadToKPlace T b)).maximalIdeal.asIdeal.LiesOver
      (nativeFmodPrime (T := T) b) := by
  rw [Ideal.liesOver_iff, Ideal.under_def]
  rw [← NumberFieldFinitePlace.comap_maximalIdeal (k := T.arithmetic.Fmod)
    (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBadToKPlace T b))]
  rw [NumberFieldFinitePlace.comap_comap]
  exact congrArg (fun v => v.maximalIdeal.asIdeal)
    (nativeBadToKPlace_comap (T := T) b).symm

/-- The native F-place as a prime over the common Fmod prime. -/
noncomputable def nativeFPrimeOver (b : Bad (nativePlaceSelection T)) :
    Ideal.primesOver (nativeFmodPrime (T := T) b)
      (NumberField.RingOfIntegers T.arithmetic.F) :=
  primesOverMkPlace (T := T) (nativeBadToFPlace T b) (nativeFmodPrime (T := T) b)
    (nativeBadFPlace_liesOver (T := T) b)

/-- The contraction of the chosen K-place as a prime over the same Fmod prime. -/
noncomputable def nativeKPrimeOver (b : Bad (nativePlaceSelection T)) :
    Ideal.primesOver (nativeFmodPrime (T := T) b)
      (NumberField.RingOfIntegers T.arithmetic.F) :=
  primesOverMkPlace (T := T)
    (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBadToKPlace T b))
    (nativeFmodPrime (T := T) b) (nativeKContraction_liesOver (T := T) b)

/-- Galois transitivity produces an automorphism carrying the native F-prime to
the contracted K-prime. -/
theorem exists_galois_move_nativeF (b : Bad (nativePlaceSelection T)) :
    exists σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F,
      σ • (nativeFPrimeOver (T := T) b).1 = (nativeKPrimeOver (T := T) b).1 :=
  exists_galois_smul_primesOver (T := T) (nativeFmodPrime (T := T) b)
    (nativeFPrimeOver (T := T) b) (nativeKPrimeOver (T := T) b)




theorem nativeFPrimeOver_val (b : Bad (nativePlaceSelection T)) :
    (nativeFPrimeOver (T := T) b).1 =
      (nativeBadToFPlace T b).maximalIdeal.asIdeal := rfl

theorem nativeKPrimeOver_val (b : Bad (nativePlaceSelection T)) :
    (nativeKPrimeOver (T := T) b).1 =
      (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
        (nativeBadToKPlace T b)).maximalIdeal.asIdeal := rfl



/-- Convert the primesOver movement to the FinitePlace alignment used by
galoisPlaceMk (retry with change/congrArg and named val lemmas). -/
theorem galoisPlaceMk_alignment_of_smul
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T))
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (hσ : σ • (nativeFPrimeOver (T := T) b).1 = (nativeKPrimeOver (T := T) b).1) :
    galoisPlaceMk (T := T) σ (nativeBadToFPlace T b) =
      LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
        (nativeBadToKPlace T b) := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  change (galoisPlaceMk (T := T) σ (nativeBadToFPlace T b)).maximalIdeal =
    (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBadToKPlace T b)).maximalIdeal
  rw [galoisPlaceMk_maximalIdeal]
  have hring : (MulSemiringAction.toRingHom
      (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
      (NumberField.RingOfIntegers T.arithmetic.F) σ) =
      (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom := by
    first
    | rfl
    | (apply RingHom.ext; intro x
       simp [NumberField.RingOfIntegers.mapRingEquiv_apply])
  have hσ' : (nativeFPrimeOver (T := T) b).1.map
      (MulSemiringAction.toRingHom
        (T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
        (NumberField.RingOfIntegers T.arithmetic.F) σ) =
      (nativeKPrimeOver (T := T) b).1 := by
    simpa [Ideal.pointwise_smul_def] using hσ
  have hmap : (nativeBadToFPlace T b).maximalIdeal.asIdeal.map
      (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) =
      (nativeKPrimeOver (T := T) b).1 := by
    rw [hring] at hσ'
    rw [nativeFPrimeOver_val] at hσ'
    exact hσ'
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [show (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv)
      (nativeBadToFPlace T b).maximalIdeal).asIdeal =
      (nativeBadToFPlace T b).maximalIdeal.asIdeal.map
        (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) by
    exact Ideal.comap_symm (I := (nativeBadToFPlace T b).maximalIdeal.asIdeal)
      (f := (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv))]
  rw [hmap, nativeKPrimeOver_val]



/-- The concrete Galois alignment condition now holds by transitivity. -/
theorem galoisFPlaceAlignmentCondition_actual
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual.GaloisFPlaceAlignmentCondition
      (T := T) b := by
  obtain ⟨σ, hσ⟩ := exists_galois_move_nativeF (T := T) b
  exact ⟨σ, galoisPlaceMk_alignment_of_smul (T := T) b σ hσ⟩



/-- The actual completion embedding at the contracted K-place (lower completion is
completion at comap_F(K-place)).  No sigma-extension is used here. -/
noncomputable def alignedCompletionMapAtComap (b : Bad (nativePlaceSelection T)) :
    (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
      (nativeBadToKPlace T b)).maximalIdeal.adicCompletion T.arithmetic.F →+*
      (nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := T.arithmetic.F)
    (nativeBadToKPlace T b)

theorem alignedCompletionMapAtComap_injective (b : Bad (nativePlaceSelection T)) :
    Function.Injective (alignedCompletionMapAtComap (T := T) b) :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionMap_injective (k := T.arithmetic.F)
    (nativeBadToKPlace T b)



/-- Cast the aligned completion map at the comap place to the (moved) native
F-place completion along the Galois place equality. -/
noncomputable def alignedCompletionMapMoved
    (b : Bad (nativePlaceSelection T))
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (h : galoisPlaceMk (T := T) σ (nativeBadToFPlace T b) =
      LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
        (nativeBadToKPlace T b)) :
    (galoisPlaceMk (T := T) σ (nativeBadToFPlace T b)).maximalIdeal.adicCompletion
        T.arithmetic.F →+*
      (nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K :=
  h ▸ alignedCompletionMapAtComap (T := T) b


end LeanFormal.IUT.XiFPaper.Mzk1GaloisRingBridgeActual
end
