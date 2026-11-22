import tmp.sheaf.n8.closure.EtaNativeQExponentActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNativeQExponentActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

example {l : PrimeGeFive} (X : N8NativeInput l) :
    (nativeBadBasePlace X).maximalIdeal.asIdeal.LiesOver
      (Ideal.span {((nativeQBasePrime X) : ℤ)}) := by
  let place := nativeBadBasePlace X
  let v := (comap (k := ℚ) place).maximalIdeal
  have hspan := Rat.HeightOneSpectrum.span_natGenerator v
  have hmem_map : ((nativeQBasePrime X : ℤ) ∈
      v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))) := by
    rw [← hspan]
    exact Ideal.mem_span_singleton.mpr dvd_rfl
  have hmem_v : (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm
      (nativeQBasePrime X : ℤ) ∈ v.asIdeal := by
    rw [Ideal.symm_apply_mem_of_equiv_iff]
    exact hmem_map
  have halg_hom : (algebraMap ℤ (NumberField.RingOfIntegers ℚ) : ℤ →+* NumberField.RingOfIntegers ℚ) =
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm :=
    RingHom.ext_int _ _
  have halg : (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) (nativeQBasePrime X : ℤ) =
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm
        (nativeQBasePrime X : ℤ) :=
    congrArg (fun f : ℤ →+* NumberField.RingOfIntegers ℚ => f (nativeQBasePrime X : ℤ)) halg_hom
  have hlies := comap_liesOver (k := ℚ) place
  rw [Ideal.liesOver_span_iff]
  · rw [IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers X.S.arithmetic.Fmod)]
    change algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers X.S.arithmetic.Fmod)
      (algebraMap ℤ (NumberField.RingOfIntegers ℚ) (nativeQBasePrime X : ℤ)) ∈
      place.maximalIdeal.asIdeal
    let x : NumberField.RingOfIntegers ℚ :=
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) (nativeQBasePrime X : ℤ)
    have hx_v : x ∈ v.asIdeal := by
      simpa [x, halg] using hmem_v
    have hx_under : x ∈ Ideal.under (NumberField.RingOfIntegers ℚ)
        place.maximalIdeal.asIdeal := by
      rw [← hlies.over]
      exact hx_v
    have hfx : (algebraMap (NumberField.RingOfIntegers ℚ)
        (NumberField.RingOfIntegers X.S.arithmetic.Fmod)) x =
        (nativeQBasePrime X : NumberField.RingOfIntegers X.S.arithmetic.Fmod) := by
      dsimp [x]
      norm_num
    exact (Ideal.mem_comap).mp (by simpa [Ideal.under_def, hfx] using hx_under)
  · exact place.maximalIdeal.isPrime.ne_top
  · exact Nat.prime_iff_prime_int.mp (nativeQBasePrime_prime (X := X))