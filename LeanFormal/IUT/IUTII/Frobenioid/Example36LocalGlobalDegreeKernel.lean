/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianPlaceStrip
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import LeanFormal.IUT.IUTII.Frobenioid.Example36VerticalCarrier

set_option linter.unusedSectionVars false

/-!
# Local-to-global degree kernel compatibility of the place strip

This module assembles the local-to-global degree functional of the actual
number-field place data from the local degree weights of the place strip, and
identifies its kernel on principal divisors with the product formula of
Example36ProductFormula.lean.

Contents.

1. The actual place index of the number field F is the disjoint union of the
   finite places (height-one primes of O_F) and the archimedean places.  At
   every place we define the local degree weight of an explicit divisor
   coordinate d (SourceModelBackend.ExplicitDivisor F):
   * at a finite place v:  d_v * log #(O_F / v);
   * at an archimedean place w:  [F_w : R] * d_w, where [F_w : R] is the
     local degree InfinitePlace.mult (1 at real, 2 at complex places).
   The local weights are packaged as additive functionals of the divisor
   coordinates at every place (placeFiniteWeightHom, placeInfiniteWeightHom,
   placeWeightHom).  The local-to-global degree functional localToGlobalWeight
   is the sum of these local weights over the actual place index: over the
   finitely many finite places in the support of the divisor and over all
   (finitely many) archimedean places.  The localToGlobalWeight_eq_formula
   theorem computes it as the finite Finsupp sum plus the archimedean Finset
   sum, and localToGlobalWeightHom is its additive-homomorphism form.

2. localToGlobalWeight agrees with the global prime-strip weight
   globalPrimeStripWeight of Example36ProductFormula.lean on the explicit
   divisor coordinates, both as additive functionals
   (localToGlobalWeightHom_eq_globalPrimeStripWeightHom) and pointwise
   (localToGlobalWeight_eq_globalPrimeStripWeight).  On the explicit
   principal divisor of a global unit f the local-to-global degree vanishes
   (localToGlobalWeight_principalDivisorExplicit): this is the product
   formula in the normalized finite/archimedean weights.

3. The local degree weights of a principal divisor are the realifications of
   the actual vertical carriers of Example36VerticalCarrier.lean: at a finite
   place the local weight is minus the realified degree of the completion-unit
   carrier (the finite local log-volume -nu_v * log #(O_F / v)), and at an
   archimedean place it is the local degree times the realified archimedean
   carrier value (-log (w f)).  The local-to-global degree is therefore the
   sum of the local vertical-carrier realifications with the local-degree
   weights (localToGlobalWeight_principalDivisor_eq_sum_verticalCarrierRealifications).

4. The kernel side.  globalDegreeKernel is the kernel of the additive local-
   to-global degree functional on the explicit divisor coordinates, and
   placeDegreeKernel P is the kernel of the local weight at the place P.
   Proved: the intersection of all local degree kernels is trivial
   (localKernels_iInf_eq_bot: every coordinate has to vanish), it is
   contained in the global degree kernel, and the global degree kernel
   contains every principal divisor
   (principalDivisorExplicit_range_subset_globalDegreeKernel).  The precise
   "equalizer" statement realized here is that the global kernel is the zero
   fiber of the sum of the local weights and the principal divisors lie in it;
   a principal divisor is generally not in the intersection of the local
   kernels, because its local weights are individually the nontrivial local
   values.  The exact conditional statement is recorded
   (principalDivisor_not_mem_placeDegreeKernel_of_finiteExponent_ne_zero and
   the archimedean counterpart), and the bundled summary
   globalDegreeKernel_equalizer_principalDivisors states the vanishing of the
   total and the identification of the individual local contributions.

5. The Gaussian place strip of Example36GaussianPlaceStrip.lean is the
   concrete all-place local data available in the tree; for F = Q(i) the
   local weights of a principal divisor are identified with the place-strip
   realifications placeValueGroupRealification of the local values
   (gaussianFinitePlaceWeight_eq_neg_placeStripRealification,
   gaussianInfinitePlaceWeight_eq_mult_placeStripRealification), and their
   sum vanishes (gaussianLocalToGlobalWeight_principalDivisor_eq_zero).

Boundary, stated precisely.  The global degree functional here is the model
weight of the explicit divisor coordinates, built from the actual
residue-field cardinalities and the actual archimedean absolute values; it is
not the source Frobenioid global degree.  What is missing for the source
local-to-global statement is exactly the vertical carrier's missing data
recorded in Example36VerticalCarrier.lean: the V_K transport, the rho_v
normalization rho_v = 1/[K_v:(F_mod)_v] * logPhi(pv) of IUT I Example 3.5 (i),
the log-shell carrier and the Frobenius/log-Kummer carrier.  No source
normalization isomorphism is claimed, no range statement for the local images
is asserted, and no theta-pilot, q-pilot, Tate or Hodge-theater claim is made.
The D-prime-strip/Galois/geometric pi_1 structure over the places is likewise
not constructed (GaussianPlaceDPrimeStripCard).
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace LocalGlobalDegreeKernel

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open IsDedekindDomain NumberField
open scoped NumberField BigOperators

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The Gaussian field is a number field: the irreducibility fact needed for
the AdjoinRoot field structure, as in Example36GaussianPlaceStrip.lean. -/
local instance gaussianFieldFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The actual place index and the local degree weights -/

/-- The actual place index of the number field F: finite places (height-one
primes of the ring of integers) and archimedean places. -/
abbrev AllPlaceIndex (F : Type u) [Field F] [NumberField F] : Type u :=
  HeightOneSpectrum (𝓞 F) ⊕ NumberField.InfinitePlace F

/-- The finite-place component of the place index. -/
def finitePlaceIndex (v : HeightOneSpectrum (𝓞 F)) : AllPlaceIndex (F := F) :=
  Sum.inl v

/-- The archimedean component of the place index. -/
def infinitePlaceIndex (w : NumberField.InfinitePlace F) : AllPlaceIndex (F := F) :=
  Sum.inr w

/-- The finite local degree weight of a divisor coordinate at the finite place
v: the valuation exponent read against the logarithm of the actual
residue-field cardinality.  On the principal divisor of a global unit this is
-nu_v * log #(O_F / v) read with the sign of the global prime-strip weight. -/
noncomputable def placeFiniteWeight (v : HeightOneSpectrum (𝓞 F))
    (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  (d.1 v : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))

/-- The archimedean local degree weight of a divisor coordinate at the
archimedean place w: the local degree [F_w : R] = InfinitePlace.mult times the
archimedean coordinate -log (w .). -/
noncomputable def placeInfiniteWeight (w : NumberField.InfinitePlace F)
    (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  (NumberField.InfinitePlace.mult w : ℝ) * d.2 w

/-- The local degree weight of a divisor coordinate at a place. -/
noncomputable def placeWeight (P : AllPlaceIndex (F := F))
    (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  match P with
  | Sum.inl v => placeFiniteWeight v d
  | Sum.inr w => placeInfiniteWeight w d

/-- The finite place support of a divisor in the place index: the finite
places in the support of its finite coordinates, together with all
archimedean places. -/
noncomputable def placeSupport (d : SourceModelBackend.ExplicitDivisor F) :
    Finset (AllPlaceIndex (F := F)) := by
  classical
  exact d.1.support.image Sum.inl ∪
    (Finset.univ : Finset (NumberField.InfinitePlace F)).image Sum.inr

/-- The local-to-global degree functional: the sum of the local degree weights
over the actual place index (the finitely many finite places in the support of
the divisor and all archimedean places). -/
noncomputable def localToGlobalWeight (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  ∑ P ∈ placeSupport d, placeWeight P d

/-- The local degree weight at a finite place, packaged as an additive
functional of the divisor coordinates. -/
noncomputable def placeFiniteWeightHom (v : HeightOneSpectrum (𝓞 F)) :
    SourceModelBackend.ExplicitDivisor F →+ ℝ where
  toFun d := placeFiniteWeight v d
  map_zero' := by
    simp [placeFiniteWeight]
  map_add' := by
    intro a b
    simp only [placeFiniteWeight, Prod.fst_add, Finsupp.add_apply]
    push_cast
    ring

/-- The local degree weight at an archimedean place, packaged as an additive
functional of the divisor coordinates. -/
noncomputable def placeInfiniteWeightHom (w : NumberField.InfinitePlace F) :
    SourceModelBackend.ExplicitDivisor F →+ ℝ where
  toFun d := placeInfiniteWeight w d
  map_zero' := by
    simp [placeInfiniteWeight]
  map_add' := by
    intro a b
    simp only [placeInfiniteWeight, Prod.snd_add, Pi.add_apply]
    ring

/-- The local degree weight at a place, packaged as an additive functional of
the divisor coordinates. -/
noncomputable def placeWeightHom (P : AllPlaceIndex (F := F)) :
    SourceModelBackend.ExplicitDivisor F →+ ℝ :=
  match P with
  | Sum.inl v => placeFiniteWeightHom (F := F) v
  | Sum.inr w => placeInfiniteWeightHom (F := F) w

/-- The finite local weight of a divisor coordinate is its exponent times the
residue-field logarithm. -/
@[simp]
theorem placeFiniteWeight_apply (v : HeightOneSpectrum (𝓞 F))
    (d : SourceModelBackend.ExplicitDivisor F) :
    placeFiniteWeight (F := F) v d =
      (d.1 v : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) :=
  rfl

/-- The archimedean local weight of a divisor coordinate is the local degree
times the archimedean coordinate. -/
@[simp]
theorem placeInfiniteWeight_apply (w : NumberField.InfinitePlace F)
    (d : SourceModelBackend.ExplicitDivisor F) :
    placeInfiniteWeight (F := F) w d =
      (NumberField.InfinitePlace.mult w : ℝ) * d.2 w :=
  rfl

/-- The local weight at a finite place index. -/
@[simp]
theorem placeWeight_finitePlaceIndex (v : HeightOneSpectrum (𝓞 F))
    (d : SourceModelBackend.ExplicitDivisor F) :
    placeWeight (finitePlaceIndex (F := F) v) d = placeFiniteWeight (F := F) v d :=
  rfl

/-- The local weight at an archimedean place index. -/
@[simp]
theorem placeWeight_infinitePlaceIndex (w : NumberField.InfinitePlace F)
    (d : SourceModelBackend.ExplicitDivisor F) :
    placeWeight (infinitePlaceIndex (F := F) w) d = placeInfiniteWeight (F := F) w d :=
  rfl

/-- **The local-to-global degree as a sum over the actual place index.**  The
localToGlobalWeight of a divisor coordinate is the finite Finsupp sum of its
weighted finite exponents plus the archimedean Finset sum of its weighted
coordinates. -/
theorem localToGlobalWeight_eq_formula (d : SourceModelBackend.ExplicitDivisor F) :
    localToGlobalWeight (F := F) d =
      d.1.sum (fun v n => (n : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
        + ∑ w : NumberField.InfinitePlace F,
            (NumberField.InfinitePlace.mult w : ℝ) * d.2 w := by
  unfold localToGlobalWeight placeSupport
  classical
  have hdisj : Disjoint (d.1.support.image Sum.inl)
      ((Finset.univ : Finset (NumberField.InfinitePlace F)).image Sum.inr) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨v, -, rfl⟩ := ha
    obtain ⟨w, -, h⟩ := hb
    exact Sum.inl_ne_inr h.symm
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image (fun a _ b _ h => Sum.inl.inj h)]
  rw [Finset.sum_image (fun a _ b _ h => Sum.inr.inj h)]
  rw [Finsupp.sum]
  simp only [placeWeight, placeFiniteWeight, placeInfiniteWeight]

/-- The additive-homomorphism form of the local-to-global degree functional. -/
noncomputable def localToGlobalWeightHom :
    SourceModelBackend.ExplicitDivisor F →+ ℝ where
  toFun := localToGlobalWeight (F := F)
  map_zero' := by
    rw [localToGlobalWeight_eq_formula]
    simp
  map_add' := by
    intro a b
    rw [localToGlobalWeight_eq_formula, localToGlobalWeight_eq_formula,
      localToGlobalWeight_eq_formula]
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [Finsupp.sum_add_index' (fun v => by simp) (fun v x y => by push_cast; ring)]
    simp only [mul_add, Finset.sum_add_distrib]
    ring

/-- The local-to-global degree functional computed on a divisor coordinate is
its place-index sum. -/
@[simp]
theorem localToGlobalWeightHom_apply (d : SourceModelBackend.ExplicitDivisor F) :
    localToGlobalWeightHom (F := F) d = localToGlobalWeight (F := F) d :=
  rfl

/-- **Agreement with the global prime-strip weight, as additive functionals.**
The local-to-global degree functional is the global prime-strip weight
functional of Example36ProductFormula.lean. -/
theorem localToGlobalWeightHom_eq_globalPrimeStripWeightHom :
    localToGlobalWeightHom (F := F) = globalPrimeStripWeightHom (F := F) := by
  apply AddMonoidHom.ext
  intro d
  rw [localToGlobalWeightHom_apply, localToGlobalWeight_eq_formula]
  rfl

/-- **Agreement with the global prime-strip weight, pointwise.** -/
theorem localToGlobalWeight_eq_globalPrimeStripWeight
    (d : SourceModelBackend.ExplicitDivisor F) :
    localToGlobalWeight (F := F) d = globalPrimeStripWeight (F := F) d := by
  rw [← localToGlobalWeightHom_apply, localToGlobalWeightHom_eq_globalPrimeStripWeightHom]
  rfl

/-! ## 2. Principal divisors and the product formula -/

/-- **Vanishing of the local-to-global degree on principal divisors.**  The
sum over the actual place index of the local degree weights of the explicit
principal divisor of a global unit is zero: the product formula in the
normalized finite/archimedean weights. -/
theorem localToGlobalWeight_principalDivisorExplicit (f : Fˣ) :
    localToGlobalWeight (F := F)
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 := by
  rw [localToGlobalWeight_eq_formula]
  change (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
      + ∑ w : NumberField.InfinitePlace F,
          (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f = 0
  exact productFormula_finsupp (F := F) f

/-- The vanishing of the local-to-global degree on principal divisors, in the
additive-homomorphism form. -/
theorem localToGlobalWeightHom_principalDivisorExplicit (f : Fˣ) :
    localToGlobalWeightHom (F := F)
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 :=
  localToGlobalWeight_principalDivisorExplicit (F := F) f

/-- The local-to-global degree of a global unit, defined as the local-to-global
degree of its explicit principal divisor. -/
noncomputable def localToGlobalUnitWeight (f : Fˣ) : ℝ :=
  localToGlobalWeight (F := F)
    (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))

/-- The local-to-global degree of every global unit is zero. -/
theorem localToGlobalUnitWeight_eq_zero (f : Fˣ) :
    localToGlobalUnitWeight (F := F) f = 0 :=
  localToGlobalWeight_principalDivisorExplicit (F := F) f

/-- **Agreement on principal divisors**: the local-to-global degree and the
global prime-strip weight of a principal divisor are equal and both vanish. -/
theorem localToGlobalWeight_principalDivisor_eq_global_and_zero (f : Fˣ) :
    localToGlobalWeight (F := F)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      globalPrimeStripWeight (F := F)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) ∧
    globalPrimeStripWeight (F := F)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 :=
  ⟨localToGlobalWeight_eq_globalPrimeStripWeight _,
    globalPrimeStripWeight_principalDivisorExplicit (F := F) f⟩

/-! ## 3. The local weights are the vertical-carrier realifications -/

/-- **Finite-place local contribution and the vertical carrier.**  On the
principal divisor of a global unit, the finite local degree weight is minus
the realified degree of the actual completion-unit vertical carrier: the
carrier realification is the local log-volume -nu_v * log #(O_F / v), while
the global prime-strip weight uses the value coordinate +nu_v * log #(O_F / v). -/
theorem placeFiniteWeight_principalDivisor_eq_neg_verticalCarrierRealification
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    placeFiniteWeight (F := F) v
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      -(finitePlaceVerticalCarrier (F := F) v).kernel.realification
        ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f) := by
  unfold placeFiniteWeight
  rw [SourceModelBackendDocking.principalDivisorExplicit_fst,
    finitePlaceVerticalCarrier_kernel_realification_global]
  simp only [toMul_ofMul]
  ring

/-- **Archimedean local contribution and the vertical carrier.**  On the
principal divisor of a global unit, the archimedean local degree weight is the
local degree [F_w : R] times the realified degree of the archimedean vertical
carrier, i.e. times the actual archimedean value -log (w f). -/
theorem placeInfiniteWeight_principalDivisor_eq_mult_verticalCarrierRealification
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    placeInfiniteWeight (F := F) w
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      (NumberField.InfinitePlace.mult w : ℝ) *
        (archimedeanVerticalCarrier (F := F) w).kernel.realification
          ((archimedeanVerticalCarrier (F := F) w).localValue f) := by
  unfold placeInfiniteWeight
  rw [SourceModelBackendDocking.principalDivisorExplicit_snd,
    archimedeanVerticalCarrier_realification_global]
  rfl

/-- **The local-to-global degree is the weighted sum of the vertical-carrier
realifications.**  On principal divisors, the sum over the actual place index
of the local degree weights is the finite sum of minus the realified
completion-unit carrier degrees plus the archimedean sum of the local degrees
times the realified archimedean carrier values. -/
theorem localToGlobalWeight_principalDivisor_eq_sum_verticalCarrierRealifications
    (f : Fˣ) :
    localToGlobalWeight (F := F)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      -(∑ v ∈ (principalDivisorFinite f).support,
          (finitePlaceVerticalCarrier (F := F) v).kernel.realification
            ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f))
        + ∑ w : NumberField.InfinitePlace F,
            (NumberField.InfinitePlace.mult w : ℝ) *
              (archimedeanVerticalCarrier (F := F) w).kernel.realification
                ((archimedeanVerticalCarrier (F := F) w).localValue f) := by
  rw [localToGlobalWeight_eq_formula]
  have hfin : (SourceModelBackend.principalDivisorExplicit (F := F)
        (Additive.ofMul f)).1.sum (fun v n => (n : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) =
      -(∑ v ∈ (principalDivisorFinite f).support,
          (finitePlaceVerticalCarrier (F := F) v).kernel.realification
            ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f)) := by
    rw [Finsupp.sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact placeFiniteWeight_principalDivisor_eq_neg_verticalCarrierRealification (F := F) v f
  have hinf : (∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) *
          (SourceModelBackend.principalDivisorExplicit (F := F)
            (Additive.ofMul f)).2 w) =
      ∑ w : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult w : ℝ) *
          (archimedeanVerticalCarrier (F := F) w).kernel.realification
            ((archimedeanVerticalCarrier (F := F) w).localValue f) := by
    apply Finset.sum_congr rfl
    intro w _
    exact placeInfiniteWeight_principalDivisor_eq_mult_verticalCarrierRealification
      (F := F) w f
  rw [hfin, hinf]

/-! ## 4. The global degree kernel and the local degree kernels -/

/-- The global degree kernel: the kernel of the additive local-to-global degree
functional on the explicit divisor coordinates. -/
noncomputable def globalDegreeKernel :
    AddSubgroup (SourceModelBackend.ExplicitDivisor F) :=
  (localToGlobalWeightHom (F := F)).ker

/-- The local degree kernel at a place: the kernel of the local degree weight
functional at that place. -/
noncomputable def placeDegreeKernel (P : AllPlaceIndex (F := F)) :
    AddSubgroup (SourceModelBackend.ExplicitDivisor F) :=
  (placeWeightHom (F := F) P).ker

/-- Membership in the global degree kernel is the vanishing of the
local-to-global degree. -/
theorem mem_globalDegreeKernel_iff (d : SourceModelBackend.ExplicitDivisor F) :
    d ∈ globalDegreeKernel (F := F) ↔ localToGlobalWeightHom (F := F) d = 0 :=
  Iff.rfl

/-- Membership in the finite-place local degree kernel is the vanishing of the
finite coordinate at that place (the residue-field logarithm is nonzero). -/
theorem mem_placeDegreeKernel_finite_iff (v : HeightOneSpectrum (𝓞 F))
    (d : SourceModelBackend.ExplicitDivisor F) :
    d ∈ placeDegreeKernel (F := F) (finitePlaceIndex v) ↔ d.1 v = 0 := by
  unfold placeDegreeKernel
  rw [AddMonoidHom.mem_ker]
  change placeFiniteWeight (F := F) v d = 0 ↔ d.1 v = 0
  unfold placeFiniteWeight
  constructor
  · intro h
    have hL : Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)) ≠ 0 :=
      finitePlaceResidueCardinality_log_ne_zero (F := F) v
    have hzero : (d.1 v : ℝ) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 hL
    exact Int.cast_injective (α := ℝ) (by simpa using hzero)
  · intro h
    rw [h]
    simp

/-- Membership in the archimedean local degree kernel is the vanishing of the
archimedean coordinate at that place (the local degree is nonzero). -/
theorem mem_placeDegreeKernel_infinite_iff (w : NumberField.InfinitePlace F)
    (d : SourceModelBackend.ExplicitDivisor F) :
    d ∈ placeDegreeKernel (F := F) (infinitePlaceIndex w) ↔ d.2 w = 0 := by
  unfold placeDegreeKernel
  rw [AddMonoidHom.mem_ker]
  change placeInfiniteWeight (F := F) w d = 0 ↔ d.2 w = 0
  unfold placeInfiniteWeight
  constructor
  · intro h
    have hL : (NumberField.InfinitePlace.mult w : ℝ) ≠ 0 :=
      NumberField.InfinitePlace.mult_coe_ne_zero
    exact (mul_eq_zero.mp h).resolve_left hL
  · intro h
    rw [h, mul_zero]

/-- The global degree kernel contains every principal divisor: the explicit
principal divisor of a global unit lies in the kernel of the local-to-global
degree functional. -/
theorem principalDivisorExplicit_mem_globalDegreeKernel (f : Fˣ) :
    SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f) ∈
      globalDegreeKernel (F := F) := by
  rw [mem_globalDegreeKernel_iff]
  exact localToGlobalWeightHom_principalDivisorExplicit (F := F) f

/-- The range of the explicit principal-divisor map is contained in the global
degree kernel (every principal divisor has global degree zero). -/
theorem principalDivisorExplicit_range_subset_globalDegreeKernel :
    Set.range (SourceModelBackend.principalDivisorExplicit (F := F)) ⊆
      (globalDegreeKernel (F := F) : Set (SourceModelBackend.ExplicitDivisor F)) := by
  rintro x ⟨u, rfl⟩
  rw [← ofMul_toMul u]
  exact principalDivisorExplicit_mem_globalDegreeKernel (F := F) u.toMul

/-- **The intersection of the local degree kernels is trivial.**  A divisor
coordinate whose every local degree weight vanishes must vanish at every
coordinate, hence is the zero divisor. -/
theorem localKernels_iInf_eq_bot :
    (⨅ P : AllPlaceIndex (F := F), placeDegreeKernel (F := F) P) = ⊥ := by
  apply le_antisymm
  · intro d hd
    have hfin : ∀ v : HeightOneSpectrum (𝓞 F), d.1 v = 0 := by
      intro v
      have hv : d ∈ placeDegreeKernel (F := F) (finitePlaceIndex v) := by
        rw [AddSubgroup.mem_iInf] at hd
        exact hd (finitePlaceIndex v)
      rwa [mem_placeDegreeKernel_finite_iff] at hv
    have hinf : ∀ w : NumberField.InfinitePlace F, d.2 w = 0 := by
      intro w
      have hw : d ∈ placeDegreeKernel (F := F) (infinitePlaceIndex w) := by
        rw [AddSubgroup.mem_iInf] at hd
        exact hd (infinitePlaceIndex w)
      rwa [mem_placeDegreeKernel_infinite_iff] at hw
    exact Prod.ext (Finsupp.ext hfin) (funext hinf)
  · exact bot_le

/-- The intersection of the local degree kernels is contained in the global
degree kernel. -/
theorem localKernels_iInf_le_globalDegreeKernel :
    (⨅ P : AllPlaceIndex (F := F), placeDegreeKernel (F := F) P) ≤
      globalDegreeKernel (F := F) := by
  rw [localKernels_iInf_eq_bot]
  exact bot_le

/-- A principal divisor with nonzero finite exponent at v is not in the local
degree kernel at v: the local weight there is its nonzero local value.  This
is the exact sense in which a principal divisor is not in the intersection of
the local degree kernels, while its total local-to-global degree vanishes. -/
theorem principalDivisor_not_mem_placeDegreeKernel_of_finiteExponent_ne_zero
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ)
    (h : finitePlaceValueExponent v f ≠ 0) :
    SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f) ∉
      placeDegreeKernel (F := F) (finitePlaceIndex v) := by
  intro hmem
  rw [mem_placeDegreeKernel_finite_iff] at hmem
  apply h
  rw [SourceModelBackendDocking.principalDivisorExplicit_fst] at hmem
  exact hmem

/-- A principal divisor with nonzero archimedean value at w is not in the
local degree kernel at w. -/
theorem principalDivisor_not_mem_placeDegreeKernel_of_archimedean_ne_zero
    (w : NumberField.InfinitePlace F) (f : Fˣ)
    (h : archimedeanPlaceValue w f ≠ 0) :
    SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f) ∉
      placeDegreeKernel (F := F) (infinitePlaceIndex w) := by
  intro hmem
  rw [mem_placeDegreeKernel_infinite_iff] at hmem
  apply h
  rw [SourceModelBackendDocking.principalDivisorExplicit_snd] at hmem
  exact hmem

/-- **The equalizer statement on principal divisors, bundled.**  For a global
unit f: the local-to-global degree vanishes, the principal divisor lies in the
global degree kernel, the finite local weights are minus the realified
completion-unit carrier degrees, and the archimedean local weights are the
local degrees times the realified archimedean carrier values.  The global
kernel is therefore the zero fiber of the sum of the local degree weights on
principal divisors; the individual local weights need not vanish. -/
theorem globalDegreeKernel_equalizer_principalDivisors (f : Fˣ) :
    localToGlobalWeight (F := F)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 ∧
      SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f) ∈
        globalDegreeKernel (F := F) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        placeFiniteWeight (F := F) v
            (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
          -(finitePlaceVerticalCarrier (F := F) v).kernel.realification
            ((finitePlaceVerticalCarrier (F := F) v).globalToLocal f)) ∧
      (∀ w : NumberField.InfinitePlace F,
        placeInfiniteWeight (F := F) w
            (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
          (NumberField.InfinitePlace.mult w : ℝ) *
            (archimedeanVerticalCarrier (F := F) w).kernel.realification
              ((archimedeanVerticalCarrier (F := F) w).localValue f)) :=
  ⟨localToGlobalWeight_principalDivisorExplicit (F := F) f,
    principalDivisorExplicit_mem_globalDegreeKernel (F := F) f,
    fun v => placeFiniteWeight_principalDivisor_eq_neg_verticalCarrierRealification
      (F := F) v f,
    fun w => placeInfiniteWeight_principalDivisor_eq_mult_verticalCarrierRealification
      (F := F) w f⟩

/-! ## 5. The Gaussian place strip: local weights as place-strip realifications -/

/-- **Gaussian finite-place local weight.**  For the Gaussian field Q(i), the
finite local weight of the principal divisor of a global unit is minus the
realified place-strip local value at the corresponding finite Gaussian place;
the place-strip realification is the local log-volume -nu_v * log #(O_F / v). -/
theorem gaussianFinitePlaceWeight_eq_neg_placeStripRealification
    (v : HeightOneSpectrum (𝓞 GaussianField)) (f : GaussianFieldˣ) :
    placeFiniteWeight (F := GaussianField) v
        (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
          (Additive.ofMul f)) =
      -GaussianPlaceStrip.placeValueGroupRealification
        (GaussianPlaceStrip.finiteGaussianPlace v)
        (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
          (GaussianPlaceStrip.finiteGaussianPlace v) f) := by
  rw [GaussianPlaceStrip.placeLocalValueOfGlobalUnit_realification_eq_placeData]
  unfold placeFiniteWeight GaussianPlaceStrip.example36PlaceDataRealified
  simp only [GaussianPlaceStrip.finiteGaussianPlace]
  rw [SourceModelBackendDocking.principalDivisorExplicit_fst,
    numberFieldGlobalPlaceData_finiteDelta]
  simp only [toMul_ofMul]
  ring

/-- **Gaussian archimedean local weight.**  For the Gaussian field, the
archimedean local weight of the principal divisor of a global unit is the
local degree [F_w : R] times the realified place-strip archimedean value, i.e.
times -log (w f). -/
theorem gaussianInfinitePlaceWeight_eq_mult_placeStripRealification
    (w : NumberField.InfinitePlace GaussianField) (f : GaussianFieldˣ) :
    placeInfiniteWeight (F := GaussianField) w
        (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
          (Additive.ofMul f)) =
      (NumberField.InfinitePlace.mult w : ℝ) *
        GaussianPlaceStrip.placeValueGroupRealification
          (GaussianPlaceStrip.infiniteGaussianPlace w)
          (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
            (GaussianPlaceStrip.infiniteGaussianPlace w) f) := by
  rw [GaussianPlaceStrip.placeLocalValueOfGlobalUnit_realification_eq_placeData]
  unfold placeInfiniteWeight GaussianPlaceStrip.example36PlaceDataRealified
  simp only [GaussianPlaceStrip.infiniteGaussianPlace]
  rw [SourceModelBackendDocking.principalDivisorExplicit_snd,
    numberFieldGlobalPlaceData_infiniteDelta]
  rfl

/-- **The Gaussian local-to-global degree is the weighted sum of the
place-strip realifications.**  The sum over the actual Gaussian place index of
the local degree weights of a principal divisor is the finite sum of minus the
place-strip finite realifications plus the archimedean sum of the local degrees
times the place-strip archimedean realifications. -/
theorem gaussianLocalToGlobalWeight_eq_sum_placeStripRealifications
    (f : GaussianFieldˣ) :
    localToGlobalWeight (F := GaussianField)
        (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
          (Additive.ofMul f)) =
      -(∑ v ∈ (principalDivisorFinite f).support,
          GaussianPlaceStrip.placeValueGroupRealification
            (GaussianPlaceStrip.finiteGaussianPlace v)
            (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
              (GaussianPlaceStrip.finiteGaussianPlace v) f))
        + ∑ w : NumberField.InfinitePlace GaussianField,
            (NumberField.InfinitePlace.mult w : ℝ) *
              GaussianPlaceStrip.placeValueGroupRealification
                (GaussianPlaceStrip.infiniteGaussianPlace w)
                (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
                  (GaussianPlaceStrip.infiniteGaussianPlace w) f) := by
  rw [localToGlobalWeight_eq_formula]
  have hfin : (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
        (Additive.ofMul f)).1.sum (fun v n => (n : ℝ) *
          Real.log ((finitePlaceResidueCardinality (F := GaussianField) v : ℝ))) =
      -(∑ v ∈ (principalDivisorFinite f).support,
          GaussianPlaceStrip.placeValueGroupRealification
            (GaussianPlaceStrip.finiteGaussianPlace v)
            (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
              (GaussianPlaceStrip.finiteGaussianPlace v) f)) := by
    rw [Finsupp.sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact gaussianFinitePlaceWeight_eq_neg_placeStripRealification v f
  have hinf : (∑ w : NumberField.InfinitePlace GaussianField,
        (NumberField.InfinitePlace.mult w : ℝ) *
          (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
            (Additive.ofMul f)).2 w) =
      ∑ w : NumberField.InfinitePlace GaussianField,
        (NumberField.InfinitePlace.mult w : ℝ) *
          GaussianPlaceStrip.placeValueGroupRealification
            (GaussianPlaceStrip.infiniteGaussianPlace w)
            (GaussianPlaceStrip.placeLocalValueOfGlobalUnit
              (GaussianPlaceStrip.infiniteGaussianPlace w) f) := by
    apply Finset.sum_congr rfl
    intro w _
    exact gaussianInfinitePlaceWeight_eq_mult_placeStripRealification w f
  rw [hfin, hinf]

/-- **The Gaussian local-to-global degree of every global unit vanishes.** -/
theorem gaussianLocalToGlobalWeight_principalDivisor_eq_zero (f : GaussianFieldˣ) :
    localToGlobalWeight (F := GaussianField)
      (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
        (Additive.ofMul f)) = 0 :=
  localToGlobalWeight_principalDivisorExplicit (F := GaussianField) f

end LocalGlobalDegreeKernel
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
