/-
# S2710: exact residue norm and relative residue degree one at the Gaussian
places above 5 and 2161

Layer: source/arithmetic q-side.  Consumer: the multi-Q q-pilot layer
(SourcePilotQFamily / residue-degree-one donor gap), i.e. the input
`relativeResidueDegree (k := ℚ) place = 1` for the actual Gaussian places of the
concrete q-pilot data.

## What is proved here (actual, no assumption of the target)

1. **The Gaussian place above 5.**
   * `S2710_residueNormBase_five` : `residueNormBase concreteGaussianFivePlace = 5`
     (cited from the actual `S1487_residueNormBase_five`).
   * `S2710_relativeResidueDegree_five` / `S2710_localResidueDegree_five` : the
     relative residue degree at that place is `1` (cited from the actual
     `concreteGaussianFivePlace_relativeResidueDegree_eq_one`).
   * `S2710_residueNormBase_eq_residueCharacteristic_five` : the residue norm is
     the residue characteristic, `5 = 5`.

2. **The Gaussian place above 2161.**
   The Gaussian-integer factorization `(44+15i)(44-15i) = 2161`, transported to
   the ring of integers of `ℚ(i)`, gives the ideal factorization
   `(2161) = 𝔭₊ 𝔭₋` and hence the classification of *every* prime of `ℤ[i]`
   containing `2161` as one of the two explicit primes `𝔭₊, 𝔭₋`
   (`S2710_gaussianField2161Prime_classification`).  The classical place
   `S2696GaussianPlace2161` contains `2161` (its contraction is the rational
   place at 2161), so its maximal ideal is `𝔭₊` or `𝔭₋`; both have residue ring
   `ZMod 2161` by the actual residue equivalences of `S2698Two2161ResidueActual`,
   so its absolute residue norm is `2161` and its relative residue degree is `1`:
   * `S2710_absNorm_GaussianPlace2161`;
   * `S2710_residueNormBase_2161 : residueNormBase S2696GaussianPlace2161 = 2161`;
   * `S2710_localResidueDegree_2161 : localResidueDegree (k := ℚ) ... = 1`
     (equivalently `relativeResidueDegree (k := ℚ) ... = 1`);
   * `S2710_residueNormBase_eq_residueCharacteristic_2161`.

   The absolute norm is computed two independent ways: directly as `2161 ^ 1`
   from the rational base (`Ideal.absNorm_span_natCast`), and from
   `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver` together with the residue
   equivalence `(ℤ[i]/𝔭) ≃+* ZMod 2161`.

No sorry, axiom, native_decide or True-slot is used; every statement below is a
theorem about the actual Mathlib objects.
-/
import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
import tmp.sheaf.xif.paper.S2697Two2161PlacesActual
import tmp.sheaf.xif.paper.S2698Two2161ResidueActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2710GaussianResidueDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
open LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

local instance s2710GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The Gaussian place above 5 -/

/-- The arithmetic residue norm at the concrete Gaussian five place is `5`. -/
theorem S2710_residueNormBase_five :
    residueNormBase concreteGaussianFivePlace = 5 :=
  S1487_residueNormBase_five

/-- The relative residue degree of the concrete Gaussian five place over `ℚ` is
one. -/
theorem S2710_relativeResidueDegree_five :
    relativeResidueDegree (k := ℚ) concreteGaussianFivePlace = 1 :=
  concreteGaussianFivePlace_relativeResidueDegree_eq_one

/-- The local residue degree of the concrete Gaussian five place over `ℚ` is
one.  This is the definition used by the q-pilot base change
(`ArithmeticQPilotBaseChange.localResidueDegree`); it is definitionally the
same as `relativeResidueDegree`. -/
theorem S2710_localResidueDegree_five :
    localResidueDegree (k := ℚ) concreteGaussianFivePlace = 1 :=
  concreteGaussianFivePlace_relativeResidueDegree_eq_one

/-- At the Gaussian place above `5` the residue norm equals the residue
characteristic. -/
theorem S2710_residueNormBase_eq_residueCharacteristic_five :
    residueNormBase concreteGaussianFivePlace =
      (NumberFieldFinitePlace.residueCharacteristic concreteGaussianFivePlace : ℝ) := by
  rw [concreteGaussianFivePlace_residueCharacteristic, S2710_residueNormBase_five]
  norm_num

/-! ## 2. The Gaussian place above 2161

The Gaussian integer factorization `(44 + 15i)(44 - 15i) = 2161`, transported
along the ring-of-integers equivalence, gives the ideal factorization
`(2161) = 𝔭₊ 𝔭₋` in `𝓞(ℚ(i))`, and hence the classification of all primes
containing `2161`. -/

/-- The actual Gaussian-integer factorization `(44+15i)(44-15i) = 2161`. -/
theorem S2710_gaussianInt2161_mul :
    S2697GaussianIntPlus * S2697GaussianIntMinus = (2161 : GaussianInt) := by
  apply Zsqrtd.ext_iff.mpr
  constructor <;> norm_num [S2697GaussianIntPlus, S2697GaussianIntMinus]

/-- The principal-ideal factorization `(2161) = (44+15i)(44-15i)` in `ℤ[i]`. -/
theorem S2710_gaussianInt2161_ideal_factorization :
    Ideal.span {(2161 : GaussianInt)} =
      Ideal.span {S2697GaussianIntPlus} * Ideal.span {S2697GaussianIntMinus} := by
  rw [← S2710_gaussianInt2161_mul]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

/-- The ideal factorization `(2161) = 𝔭₊ 𝔭₋` in the ring of integers of the
Gaussian field. -/
theorem S2710_gaussianField2161_ideal_factorization :
    Ideal.span {(2161 : gaussianRingOfIntegers)} =
      S2697GaussianFieldPrimePlus * S2697GaussianFieldPrimeMinus := by
  have hmap : Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (Ideal.span {(2161 : gaussianRingOfIntegers)}) =
      Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (S2697GaussianFieldPrimePlus * S2697GaussianFieldPrimeMinus) := by
    rw [Ideal.map_mul]
    rw [S2697GaussianFieldPrimePlus, S2697GaussianFieldPrimeMinus]
    rw [Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective,
      Ideal.map_comap_of_surjective
        (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
        gaussianRingOfIntegersEquivGaussianInt.surjective]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    have h2161 : gaussianRingOfIntegersEquivGaussianInt.toRingHom
        (2161 : gaussianRingOfIntegers) = (2161 : GaussianInt) :=
      map_natCast _ 2161
    rw [h2161]
    exact S2710_gaussianInt2161_ideal_factorization
  have h := congrArg (Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom) hmap
  rw [Ideal.comap_map_of_bijective (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
      gaussianRingOfIntegersEquivGaussianInt.bijective,
    Ideal.comap_map_of_bijective (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
      gaussianRingOfIntegersEquivGaussianInt.bijective] at h
  exact h

/-- Classification of the primes of the Gaussian ring of integers containing
`2161`: exactly the two explicit Gaussian primes `𝔭₊` and `𝔭₋`. -/
theorem S2710_gaussianField2161Prime_classification
    (P : Ideal gaussianRingOfIntegers) [hP : P.IsPrime]
    (h2161 : Ideal.span {(2161 : gaussianRingOfIntegers)} ≤ P) :
    P = S2697GaussianFieldPrimePlus ∨ P = S2697GaussianFieldPrimeMinus := by
  have hle : S2697GaussianFieldPrimePlus * S2697GaussianFieldPrimeMinus ≤ P := by
    rw [← S2710_gaussianField2161_ideal_factorization]
    exact h2161
  rcases (Ideal.IsPrime.mul_le hP).mp hle with h | h
  · left
    exact (S2697GaussianFieldPrimePlus_isMaximal.eq_of_le hP.ne_top h).symm
  · right
    exact (S2697GaussianFieldPrimeMinus_isMaximal.eq_of_le hP.ne_top h).symm

/-- The absolute norm of the explicit Gaussian prime `𝔭₊` above `2161` is
`2161`: its residue ring is `ZMod 2161` by the actual residue equivalence
`S2698FieldResidueEquivPlus`. -/
theorem S2710_absNorm_plus :
    (S2697GaussianFieldPrimePlus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  calc Nat.card (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimePlus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr S2698FieldResidueEquivPlus.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The absolute norm of the explicit Gaussian prime `𝔭₋` above `2161` is
`2161`. -/
theorem S2710_absNorm_minus :
    (S2697GaussianFieldPrimeMinus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  calc Nat.card (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimeMinus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr S2698FieldResidueEquivMinus.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-! ### 2.1 The maximal ideal of the actual place above 2161 -/

/-- The maximal ideal of the rational place at `2161` is the principal ideal
`(2161)`. -/
theorem S2710_Place2161_maximalIdeal_asIdeal :
    S2696Place2161.maximalIdeal.asIdeal =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  rw [S2696Place2161, NumberField.FinitePlace.maximalIdeal_mk]
  exact S2696HeightOne2161_asIdeal_eq_span

/-- The contraction of the maximal ideal of the actual Gaussian place above
`2161` is the principal ideal `(2161)` of the rational ring of integers. -/
theorem S2710_GaussianPlace2161_under :
    (S2696GaussianPlace2161.maximalIdeal : Ideal gaussianRingOfIntegers).under
        (NumberField.RingOfIntegers ℚ) =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  rw [Ideal.under_def]
  have h := NumberFieldFinitePlace.comap_maximalIdeal (k := ℚ) S2696GaussianPlace2161
  rw [S2696GaussianPlace2161_comap, S2710_Place2161_maximalIdeal_asIdeal] at h
  exact h.symm

/-- The rational prime `2161` lies in the maximal ideal of the actual Gaussian
place above `2161`. -/
theorem S2710_GaussianPlace2161_2161_mem :
    (2161 : gaussianRingOfIntegers) ∈
      (S2696GaussianPlace2161.maximalIdeal : Ideal gaussianRingOfIntegers) := by
  have hunder := S2710_GaussianPlace2161_under
  have hmem : algebraMap (NumberField.RingOfIntegers ℚ) gaussianRingOfIntegers
      (2161 : NumberField.RingOfIntegers ℚ) ∈
      (S2696GaussianPlace2161.maximalIdeal : Ideal gaussianRingOfIntegers) := by
    rw [← Ideal.mem_under]
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have hmap : algebraMap (NumberField.RingOfIntegers ℚ) gaussianRingOfIntegers
      (2161 : NumberField.RingOfIntegers ℚ) = (2161 : gaussianRingOfIntegers) :=
    map_natCast _ 2161
  rwa [hmap] at hmem

/-- The maximal ideal of the actual Gaussian place above `2161` is one of the
two explicit Gaussian primes `𝔭₊`, `𝔭₋`. -/
theorem S2710_GaussianPlace2161_maximalIdeal_eq_plus_or_minus :
    (S2696GaussianPlace2161.maximalIdeal : Ideal gaussianRingOfIntegers) =
        S2697GaussianFieldPrimePlus ∨
      (S2696GaussianPlace2161.maximalIdeal : Ideal gaussianRingOfIntegers) =
        S2697GaussianFieldPrimeMinus := by
  haveI : (S2696GaussianPlace2161.maximalIdeal :
      Ideal gaussianRingOfIntegers).IsPrime :=
    S2696GaussianPlace2161.maximalIdeal.isPrime
  exact S2710_gaussianField2161Prime_classification _
    (Ideal.span_le.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact S2710_GaussianPlace2161_2161_mem))

/-- The absolute norm of the maximal ideal of the actual Gaussian place above
`2161` is exactly `2161`. -/
theorem S2710_absNorm_GaussianPlace2161 :
    Ideal.absNorm (S2696GaussianPlace2161.maximalIdeal.asIdeal) = 2161 := by
  rcases S2710_GaussianPlace2161_maximalIdeal_eq_plus_or_minus with h | h
  · rw [h]
    exact S2710_absNorm_plus
  · rw [h]
    exact S2710_absNorm_minus

/-! ### 2.2 The residue norm and the residue degree at the actual place -/

/-- The arithmetic residue norm at the actual Gaussian place above `2161` is
`2161`. -/
theorem S2710_residueNormBase_2161 :
    residueNormBase S2696GaussianPlace2161 = 2161 := by
  unfold residueNormBase
  rw [S2710_absNorm_GaussianPlace2161]
  norm_num

/-- The relative residue degree (equivalently the local residue degree) of the
actual Gaussian place above `2161` over `ℚ` is one. -/
theorem S2710_localResidueDegree_2161 :
    localResidueDegree (k := ℚ) S2696GaussianPlace2161 = 1 := by
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
    (P := S2696GaussianPlace2161.maximalIdeal.asIdeal)
    (p := (comap (k := ℚ) S2696GaussianPlace2161).maximalIdeal.asIdeal)
    (comap (k := ℚ) S2696GaussianPlace2161).maximalIdeal.isPrime
    (comap (k := ℚ) S2696GaussianPlace2161).maximalIdeal.ne_bot
  have hp : (comap (k := ℚ) S2696GaussianPlace2161).maximalIdeal.asIdeal =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
    rw [NumberFieldFinitePlace.comap_maximalIdeal, ← Ideal.under_def]
    exact S2710_GaussianPlace2161_under
  have hbase :
      Ideal.absNorm (Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)}) = 2161 := by
    change Ideal.absNorm
      (Ideal.span {((2161 : ℕ) : NumberField.RingOfIntegers ℚ)}) = 2161
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      Module.finrank_self]
    norm_num
  rw [S2710_absNorm_GaussianPlace2161, hp, hbase] at h
  have h2 : (2161 : ℕ) ^ ((Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)}).inertiaDeg'
      S2696GaussianPlace2161.maximalIdeal.asIdeal) = (2161 : ℕ) ^ 1 := by
    rw [pow_one]
    exact h.symm
  have hdeg := Nat.pow_right_injective (by norm_num) h2
  unfold localResidueDegree
  rw [hp]
  exact hdeg

/-- The relative residue degree of the actual Gaussian place above `2161` is
one (the form used by the residue-norm base-change API). -/
theorem S2710_relativeResidueDegree_2161 :
    relativeResidueDegree (k := ℚ) S2696GaussianPlace2161 = 1 :=
  S2710_localResidueDegree_2161

/-- At the actual Gaussian place above `2161` the residue norm equals the
residue characteristic. -/
theorem S2710_residueNormBase_eq_residueCharacteristic_2161 :
    residueNormBase S2696GaussianPlace2161 =
      (NumberFieldFinitePlace.residueCharacteristic S2696GaussianPlace2161 : ℝ) := by
  rw [S2696GaussianPlace2161_residueCharacteristic, S2710_residueNormBase_2161]
  norm_num

/-! ### 2.3 The second actual Gaussian place above 2161 -/

/-- The rational prime `2161` lies in the maximal ideal of the actual Gaussian
place `S2696GaussianPlace` (the classical prime over `(2161)` constructed in
`S2696GaussianPlace2161Actual`). -/
theorem S2710_S2696GaussianPlace_2161_mem :
    (2161 : gaussianRingOfIntegers) ∈
      (S2696GaussianPlace.maximalIdeal : Ideal gaussianRingOfIntegers) := by
  have hLO : S2696PrimeOver.ideal.LiesOver (Ideal.span {(2161 : ℤ)}) := by
    simpa [S2696IntegerPrimeIdeal] using S2696PrimeOver.liesOver
  have hunder :
      (S2696GaussianPlace.maximalIdeal : Ideal gaussianRingOfIntegers).under ℤ =
        Ideal.span {(2161 : ℤ)} := by
    rw [S2696GaussianPlace_maximalIdeal, Ideal.under_def]
    exact hLO.over.symm
  have hmem : algebraMap ℤ gaussianRingOfIntegers (2161 : ℤ) ∈
      (S2696GaussianPlace.maximalIdeal : Ideal gaussianRingOfIntegers) := by
    rw [← Ideal.mem_under, hunder]
    exact Ideal.mem_span_singleton_self _
  simpa using hmem

/-- The maximal ideal of the actual Gaussian place `S2696GaussianPlace` is one
of the two explicit Gaussian primes `𝔭₊`, `𝔭₋`. -/
theorem S2710_S2696GaussianPlace_maximalIdeal_eq_plus_or_minus :
    (S2696GaussianPlace.maximalIdeal : Ideal gaussianRingOfIntegers) =
        S2697GaussianFieldPrimePlus ∨
      (S2696GaussianPlace.maximalIdeal : Ideal gaussianRingOfIntegers) =
        S2697GaussianFieldPrimeMinus := by
  haveI : (S2696GaussianPlace.maximalIdeal :
      Ideal gaussianRingOfIntegers).IsPrime :=
    S2696GaussianPlace.maximalIdeal.isPrime
  exact S2710_gaussianField2161Prime_classification _
    (Ideal.span_le.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact S2710_S2696GaussianPlace_2161_mem))

/-- **The `S2698` inequality is an equality.**  The absolute norm of the
maximal ideal of the actual Gaussian place `S2696GaussianPlace` above `2161` is
exactly `2161`; hence its residue norm is exactly `2161`, upgrading
`S2698_residueNormBase_ge`. -/
theorem S2710_absNorm_S2696GaussianPlace :
    Ideal.absNorm (S2696GaussianPlace.maximalIdeal.asIdeal) = 2161 := by
  rcases S2710_S2696GaussianPlace_maximalIdeal_eq_plus_or_minus with h | h
  · rw [h]
    exact S2710_absNorm_plus
  · rw [h]
    exact S2710_absNorm_minus

/-- The arithmetic residue norm at the actual Gaussian place
`S2696GaussianPlace` above `2161` is exactly `2161` (equality form of
`S2698_residueNormBase_ge`). -/
theorem S2710_residueNormBase_S2696GaussianPlace :
    residueNormBase S2696GaussianPlace = 2161 := by
  unfold residueNormBase
  rw [S2710_absNorm_S2696GaussianPlace]
  norm_num

/-! ## 3. Axiom audit -/

#print axioms S2710_residueNormBase_five
#print axioms S2710_relativeResidueDegree_five
#print axioms S2710_localResidueDegree_five
#print axioms S2710_residueNormBase_eq_residueCharacteristic_five
#print axioms S2710_gaussianInt2161_mul
#print axioms S2710_gaussianInt2161_ideal_factorization
#print axioms S2710_gaussianField2161_ideal_factorization
#print axioms S2710_gaussianField2161Prime_classification
#print axioms S2710_absNorm_plus
#print axioms S2710_absNorm_minus
#print axioms S2710_Place2161_maximalIdeal_asIdeal
#print axioms S2710_GaussianPlace2161_under
#print axioms S2710_GaussianPlace2161_2161_mem
#print axioms S2710_GaussianPlace2161_maximalIdeal_eq_plus_or_minus
#print axioms S2710_absNorm_GaussianPlace2161
#print axioms S2710_residueNormBase_2161
#print axioms S2710_localResidueDegree_2161
#print axioms S2710_relativeResidueDegree_2161
#print axioms S2710_residueNormBase_eq_residueCharacteristic_2161
#print axioms S2710_S2696GaussianPlace_2161_mem
#print axioms S2710_S2696GaussianPlace_maximalIdeal_eq_plus_or_minus
#print axioms S2710_absNorm_S2696GaussianPlace
#print axioms S2710_residueNormBase_S2696GaussianPlace

end LeanFormal.IUT.XiFPaper.S2710GaussianResidueDegreeActual
end
