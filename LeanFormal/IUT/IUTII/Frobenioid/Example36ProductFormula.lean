/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import Mathlib.NumberTheory.NumberField.ProductFormula

set_option linter.unusedSectionVars false

/-!
# The product formula for the actual number-field place data and the global
prime-strip degree kernel

This module proves, for the actual number-field place data of IUT III,
Example 3.6, the product formula in the normalization used by the
prime-strip bridge Example36PrimeStripBridge.lean:

  sum over finite places v of nu_v(f) * log(#(O_F / v))
    + sum over archimedean places w of [F_w : R] * (-log (w f)) = 0,

for every global unit f : F^x of a number field F, where:

* nu_v(f) is the classical v-adic valuation exponent
  (finitePlaceValueExponent, i.e. the finite-place coordinate of the
  principal divisor of Example 3.6);
* #(O_F / v) is the actual residue-field cardinality, which is the ideal
  norm of v (finitePlaceResidueCardinality);
* -log (w f) is the archimedean value coordinate of Example 3.6
  (archimedeanPlaceValue, the plus-coordinate of principalDivisorInfinite);
* [F_w : R] is the local degree over R, i.e. the multiplicity
  InfinitePlace.mult (1 at a real place, 2 at a complex place).

The statement is derived from Mathlib's product formula
NumberField.prod_abs_eq_one, whose normalization is compared explicitly with
the present one in Section 1:

* at a finite place v, Mathlib's absolute value of f is
  #(O_F / v) ^ (-nu_v(f)) (via FinitePlace.norm_embedding' and
  WithZeroMulInt.toNNReal), so its logarithm is -nu_v(f) * log(#(O_F / v));
* at an infinite place w, Mathlib's absolute value of f is w f, with the
  multiplicity InfinitePlace.mult as the exponent in Mathlib's product.

The additive normalized form is then used to construct the global
prime-strip degree kernel on the concrete divisor coordinates
(SourceModelBackend.ExplicitDivisor).  The global weight functional is the
SIGNED place-index aggregate

  d |-> sum_v d_v * log(#(O_F / v)) + sum_w [F_w : R] * d_w

(read with plus signs: the finite exponent against log #(O_F / v), and the
archimedean coordinate d_w = -log (w .) against the local degree).  It is not
literally the unsigned product or sum of the local realifications of the
prime-strip value kernels: the finite-place realification of the value kernel
is -nu_v * log #(O_F / v), the negative of the finite summand, while the
archimedean realification is -log (w f), which enters the archimedean summand
with the multiplicity [F_w : R].  The explicit sign and multiplicity
conversion is proved in Example36LocalGlobalDegreeKernel.lean, where the
local-to-global degree is the sum of the local degree weights over the actual
place index and is shown to coincide with this global weight
(localToGlobalWeight_eq_globalPrimeStripWeight).  The product formula says
exactly that this global degree vanishes on the
principal units, i.e. on the explicit principal divisor
SourceModelBackend.principalDivisorExplicit of every global unit.  The
kernel is trivial on principal units: its realification vanishes and its
degree is one there.  The same vanishing statement is transported to the
model-Frobenioid backend: the comparison of the backend globalModelDivisor
with principalDivisorExplicit (Example36PrimeStripBridge.lean) gives that the
global degree of the backend divisor coordinates of a global unit is zero,
and similarly for the divisor map of the SourceModelFrobenioid input
numberFieldSourceModelInput.

Boundary (honest).  The product formula is *derived from* Mathlib's
NumberField.prod_abs_eq_one; the arithmetic input is Mathlib's finite-place
normalization (FinitePlace.norm_embedding', WithZeroMulInt.toNNReal) and the
ideal-norm identification cardQuot = absNorm, not an independent proof from
the ideal factorization.  The statement is the product formula for global
units only (the f : F^x form); no product formula for arbitrary nonzero
elements is claimed here beyond what the units version provides.  Nothing in
this file constructs the source Frobenius/log-shell carrier, Hodge theaters,
theta-pilot or q-pilot data, or any Tate uniformization claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace PrimeStripProductFormula

open LeanFormal.IUT (FrobenioidValueKernel)
open IsDedekindDomain NumberField
open scoped NumberField NNReal BigOperators

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. Normalization comparison with Mathlib's number-field place API -/

/-- The residue-field cardinality of a finite place is the ideal norm of the
place: Mathlib's Ideal.absNorm is Submodule.cardQuot = Nat.card of the
quotient. -/
theorem finitePlaceResidueCardinality_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceResidueCardinality (F := F) v = Ideal.absNorm v.asIdeal :=
  rfl

/-- **Finite-place normalization.**  The absolute value of a global unit at
the finite place v is the residue-field cardinality raised to the negated
classical exponent: |f|_v = #(O_F / v) ^ (-nu_v(f)). -/
theorem finitePlace_mk_apply_eq_residueCardinality_zpow
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    NumberField.FinitePlace.mk v (f : F) =
      (finitePlaceResidueCardinality (F := F) v : ℝ) ^ (-finitePlaceValueExponent v f) := by
  rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding']
  rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
    (finitePlaceValuation_ne_zero v f)]
  rw [← withZero_log_eq_unzero_toAdd (finitePlaceValuation_ne_zero v f)]
  rw [finitePlaceValueExponent, finitePlaceResidueCardinality_eq_absNorm, NNReal.coe_zpow,
    NNReal.coe_natCast]
  simp

/-- **Finite-place logarithmic normalization.**  The logarithm of the
absolute value of a global unit at the finite place v is
-nu_v(f) * log(#(O_F / v)). -/
theorem finitePlace_log_mk_apply (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    Real.log (NumberField.FinitePlace.mk v (f : F)) =
      -(finitePlaceValueExponent v f : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) := by
  rw [finitePlace_mk_apply_eq_residueCardinality_zpow, Real.log_zpow]
  push_cast
  ring

/-- The multiplicity of an infinite place is the local degree over R: it is
one at a real place and two at a complex place. -/
theorem infinitePlace_mult_eq_one_or_two (w : NumberField.InfinitePlace F) :
    NumberField.InfinitePlace.mult w = 1 ∨ NumberField.InfinitePlace.mult w = 2 := by
  rcases NumberField.InfinitePlace.isReal_or_isComplex w with h | h
  · exact Or.inl (NumberField.InfinitePlace.mult_isReal ⟨w, h⟩)
  · exact Or.inr (NumberField.InfinitePlace.mult_isComplex ⟨w, h⟩)

/-! ## 2. The logarithmic form of Mathlib's product formula -/

/-- The support of the finite-place absolute values of a global unit is
contained in the support of its finite principal divisor: the absolute value
is one wherever the valuation exponent vanishes. -/
theorem finitePlace_mulSupport_mk_subset (f : Fˣ) :
    Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
        ‖NumberField.FinitePlace.embedding v (f : F)‖) ⊆
      ↑(principalDivisorFinite f).support := by
  intro v hv
  rw [Function.mem_mulSupport] at hv
  change v ∈ (principalDivisorFinite f).support
  rw [principalDivisorFinite_mem_support_iff]
  intro hν
  apply hv
  rw [← NumberField.FinitePlace.mk_apply, finitePlace_mk_apply_eq_residueCardinality_zpow, hν]
  simp

/-- The product of the finite-place absolute values of a global unit is the
product over the support of its finite principal divisor, where the factor at
v is the finite-place absolute value #(O_F / v) ^ (-nu_v(f)). -/
theorem finprod_finitePlace_eq_supportProd (f : Fˣ) :
    (∏ᶠ v : NumberField.FinitePlace F, (v (f : F))) =
      ∏ v ∈ (principalDivisorFinite f).support,
        NumberField.FinitePlace.mk v (f : F) := by
  rw [← finprod_comp_equiv (NumberField.FinitePlace.equivHeightOneSpectrum.symm)]
  simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
  rw [finprod_eq_prod_of_mulSupport_subset _
    (finitePlace_mulSupport_mk_subset (F := F) f)]
  apply Finset.prod_congr rfl
  intro v _
  rw [NumberField.FinitePlace.mk_apply]

/-- **Mathlib's product formula, in logarithmic normal form.**  Taking the
logarithm of NumberField.prod_abs_eq_one gives
sum_w [F_w : R] * log(w f) + log of the finite-place product = 0.  This is
the precise comparison statement with Mathlib's normalization. -/
theorem productFormula_log (f : Fˣ) :
    (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F)))
      + Real.log (∏ᶠ v : NumberField.FinitePlace F, (v (f : F))) = 0 := by
  classical
  have hzero : (f : F) ≠ 0 := Units.ne_zero f
  set Q : ℝ := ∏ v ∈ (principalDivisorFinite f).support,
      NumberField.FinitePlace.mk v (f : F) with hQdef
  have hQeq : (∏ᶠ v : NumberField.FinitePlace F, (v (f : F))) = Q :=
    finprod_finitePlace_eq_supportProd (F := F) f
  have hprod := NumberField.prod_abs_eq_one hzero
  rw [hQeq] at hprod
  have hP_pos : 0 < (∏ w : NumberField.InfinitePlace F, (w (f : F)) ^
      NumberField.InfinitePlace.mult w) := by
    apply Finset.prod_pos
    intro w _
    exact pow_pos (NumberField.InfinitePlace.pos_iff.mpr hzero) _
  have hQ_pos : 0 < Q := by
    rw [hQdef]
    exact Finset.prod_pos (fun v _ => NumberField.FinitePlace.pos_iff.mpr hzero)
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (ne_of_gt hP_pos) (ne_of_gt hQ_pos), Real.log_one] at hlog
  have hPlog : Real.log (∏ w : NumberField.InfinitePlace F,
      (w (f : F)) ^ NumberField.InfinitePlace.mult w) =
      ∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F)) := by
    rw [Real.log_prod (fun w _ => pow_ne_zero _ (ne_of_gt
      (NumberField.InfinitePlace.pos_iff.mpr hzero)))]
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.log_pow]
  have hQlog : Real.log Q = ∑ v ∈ (principalDivisorFinite f).support,
      Real.log (NumberField.FinitePlace.mk v (f : F)) := by
    rw [hQdef, Real.log_prod (fun v _ => ne_of_gt
      (NumberField.FinitePlace.pos_iff.mpr hzero))]
  rw [hPlog, hQlog] at hlog
  rw [hQeq, hQlog]
  exact hlog

/-! ## 3. The product formula in the Example 3.6 coordinates -/

/-- The logarithm of the finite-place product of a global unit is the
negated weighted sum of its finite-place exponents. -/
theorem log_finprod_finitePlace_eq_neg_weighted (f : Fˣ) :
    Real.log (∏ᶠ v : NumberField.FinitePlace F, (v (f : F))) =
      -((principalDivisorFinite f).sum (fun v n =>
          (n : ℝ) *
            Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))) := by
  rw [finprod_finitePlace_eq_supportProd]
  rw [Real.log_prod (fun v _ => ne_of_gt
    (NumberField.FinitePlace.pos_iff.mpr (Units.ne_zero f)))]
  rw [Finsupp.sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [finitePlace_log_mk_apply, principalDivisorFinite_apply]
  ring

/-- **The product formula in the normalized finite/archimedean weights.**  For
every global unit f of the number field F,

  sum_v nu_v(f) * log(#(O_F / v)) + sum_w [F_w : R] * (-log (w f)) = 0,

with the finite sum expressed through the finitely supported principal
divisor principalDivisorFinite and the archimedean sum through the value
coordinates archimedeanPlaceValue.  The finite weights are the logarithms of
the actual residue-field cardinalities; the archimedean weights are the local
degrees InfinitePlace.mult (1 or 2). -/
theorem productFormula_finsupp (f : Fˣ) :
    (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
      + ∑ w : NumberField.InfinitePlace F,
          (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f = 0 := by
  have hlog := productFormula_log (F := F) f
  rw [log_finprod_finitePlace_eq_neg_weighted] at hlog
  have harch : (∑ w : NumberField.InfinitePlace F,
      (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f) =
      -(∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro w _
    change (NumberField.InfinitePlace.mult w : ℝ) * (-Real.log (w (f : F))) =
      -((NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F)))
    ring
  rw [harch]
  linarith

/-- **The equal-weight form of the product formula.**  In the normalized
weights the sum of the finite-place terms equals the sum of the archimedean
logarithmic terms: sum_v nu_v(f) * log(#(O_F / v)) = sum_w [F_w : R] * log(w f).
Combining this with the negated archimedean coordinates of Example 3.6 gives
the additive form productFormula_finsupp. -/
theorem weightedFiniteSum_eq_archimedeanLogSum (f : Fˣ) :
    (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) =
      ∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F)) := by
  have hlog := productFormula_log (F := F) f
  rw [log_finprod_finitePlace_eq_neg_weighted] at hlog
  linarith

/-- The product formula with the finite part written as a sum over the
support of the finite principal divisor. -/
theorem productFormula_support (f : Fˣ) :
    (∑ v ∈ (principalDivisorFinite f).support,
        (finitePlaceValueExponent v f : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
      + ∑ w : NumberField.InfinitePlace F,
          (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f = 0 := by
  have h : (∑ v ∈ (principalDivisorFinite f).support,
        (finitePlaceValueExponent v f : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) =
      (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) := by
    rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [principalDivisorFinite_apply]
  rw [h]
  exact productFormula_finsupp (F := F) f

/-! ## 4. The global prime-strip weight and degree kernel (signed place-index aggregate) -/

/-- The global prime-strip weight functional on the concrete divisor
coordinates, as the SIGNED place-index aggregate: the finite-place exponents
weighted by the logarithms of the residue-field cardinalities, plus the
archimedean coordinates weighted by the local degrees.  This is not literally
the unsigned product of the local realifications: the finite-place
realification of the prime-strip value kernel is -nu_v * log #(O_F / v) (the
negative of the finite summand) and the archimedean realification is
-log (w f) (entering the archimedean summand with the multiplicity
[F_w : R] = InfinitePlace.mult).  The equality with the signed local-to-global
degree functional of Example36LocalGlobalDegreeKernel.lean is
localToGlobalWeight_eq_globalPrimeStripWeight. -/
noncomputable def globalPrimeStripWeight
    (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  d.1.sum (fun v n =>
      (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
    + ∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * d.2 w

/-- The global prime-strip weight functional is additive in the divisor
coordinates.  It is the additive form of the signed place-index aggregate of
the local degree weights; the local-to-global degree functional of
Example36LocalGlobalDegreeKernel.lean sums the local weights over the actual
place index and is proved equal to it
(localToGlobalWeightHom_eq_globalPrimeStripWeightHom).  It is not literally the
degree readback of an unsigned product of the local realifications. -/
noncomputable def globalPrimeStripWeightHom :
    SourceModelBackend.ExplicitDivisor F →+ ℝ where
  toFun := globalPrimeStripWeight (F := F)
  map_zero' := by
    simp [globalPrimeStripWeight]
  map_add' := by
    intro a b
    simp only [globalPrimeStripWeight, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [Finsupp.sum_add_index' (fun v => by simp) (fun v x y => by push_cast; ring)]
    simp only [mul_add, Finset.sum_add_distrib]
    ring

/-- The global prime-strip degree map on the multiplicative encoding of the
divisor coordinates: the exponential of the additive global weight. -/
noncomputable def globalPrimeStripDegree :
    Multiplicative (SourceModelBackend.ExplicitDivisor F) →* Multiplicative ℝ where
  toFun m := Multiplicative.ofAdd (globalPrimeStripWeightHom (Multiplicative.toAdd m))
  map_one' := by
    change Multiplicative.ofAdd
      (globalPrimeStripWeightHom (Multiplicative.toAdd (1 : Multiplicative _))) = 1
    simp
  map_mul' := by
    intro x y
    rw [toAdd_mul, map_add, ofAdd_add]

/-- **The global prime-strip degree kernel.**  The FrobenioidValueKernel
packaging of the signed place-index aggregate on the concrete divisor
coordinates: its degree and realification are the global signed weighted sum
globalPrimeStripWeight.  Its equality with the local-to-global degree
functional of Example36LocalGlobalDegreeKernel.lean is proved there via the
sign and multiplicity conversion (finite local weight = negative of the finite
carrier realification; archimedean local weight = multiplicity times the
archimedean carrier realification), so it is not literally the unsigned
product of the local realifications.  Its effective predicate is total in this
reduced consumer form and its transport is the identity. -/
noncomputable def globalPrimeStripDegreeKernel :
    FrobenioidValueKernel (Multiplicative (SourceModelBackend.ExplicitDivisor F)) where
  degree := globalPrimeStripDegree (F := F)
  realification := fun m => globalPrimeStripWeightHom (Multiplicative.toAdd m)
  realification_mul := by
    intro x y
    rw [toAdd_mul, map_add]
  degree_realification := by
    intro m
    rfl
  unit := 1
  unit_realification := by
    change globalPrimeStripWeightHom
      (Multiplicative.toAdd (1 : Multiplicative (SourceModelBackend.ExplicitDivisor F))) = 0
    simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by
    intro m
    rfl

/-- **Triviality of the global degree on principal units.**  The global
prime-strip weight of the explicit principal divisor of every global unit
vanishes; this is the product formula. -/
theorem globalPrimeStripWeight_principalDivisorExplicit (f : Fˣ) :
    globalPrimeStripWeight (F := F)
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 := by
  change (principalDivisorFinite f).sum (fun v n =>
      (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
    + ∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f = 0
  exact productFormula_finsupp (F := F) f

/-- **Kernel triviality on principal units: realification.**  The realified
degree of the global prime-strip degree kernel vanishes on the divisor
coordinates of every global unit. -/
theorem globalPrimeStripDegreeKernel_realification_principalUnit (f : Fˣ) :
    (globalPrimeStripDegreeKernel (F := F)).realification
        (Multiplicative.ofAdd
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) = 0 :=
  globalPrimeStripWeight_principalDivisorExplicit (F := F) f

/-- **Kernel triviality on principal units: degree.**  The degree of the
global prime-strip degree kernel is one on the divisor coordinates of every
global unit. -/
theorem globalPrimeStripDegreeKernel_degree_principalUnit (f : Fˣ) :
    (globalPrimeStripDegreeKernel (F := F)).degree
        (Multiplicative.ofAdd
          (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) = 1 := by
  change Multiplicative.ofAdd (globalPrimeStripWeight (F := F)
    (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))) = 1
  rw [globalPrimeStripWeight_principalDivisorExplicit]
  rfl

/-! ## 5. The product formula in the backend divisor coordinates -/

/-- **Product formula in the model-Frobenioid backend.**  The global degree of
the backend divisor coordinates of a rational function vanishes: the
comparison globalModelDivisor = principalDivisorExplicit of
Example36PrimeStripBridge.lean identifies the backend divisor class with the
explicit principal divisor. -/
theorem globalPrimeStripWeight_globalModelDivisor (u : Additive Fˣ) :
    globalPrimeStripWeight (F := F)
        (SourceModelBackend.coneGrothendieckEquiv (F := F)
          (SourceModelBackend.globalModelDivisor (F := F) u)) = 0 := by
  rw [SourceModelBackendDocking.globalModelDivisor_coneComparison]
  rw [← ofMul_toMul u]
  exact globalPrimeStripWeight_principalDivisorExplicit (F := F) u.toMul

/-- **Product formula for the SourceModelFrobenioid input divisor map.**  The
global degree of the divisor coordinates of the model-Frobenioid input
numberFieldSourceModelInput of a rational function vanishes. -/
theorem globalPrimeStripWeight_sourceModelInput_divisor (u : Additive Fˣ) :
    globalPrimeStripWeight (F := F)
        (SourceModelBackend.coneGrothendieckEquiv (F := F)
          ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
            SourceModelBackend.bottomPoint u)) = 0 := by
  rw [SourceModelBackendDocking.sourceModelInput_divisor_eq_globalModelDivisor]
  exact globalPrimeStripWeight_globalModelDivisor (F := F) u

end PrimeStripProductFormula
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
