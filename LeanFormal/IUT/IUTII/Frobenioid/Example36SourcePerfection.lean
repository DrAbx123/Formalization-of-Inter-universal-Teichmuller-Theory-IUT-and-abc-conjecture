import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellFrobeniusAction
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36RealificationUniqueness
import Mathlib.Tactic

/-!
# Actual source perfection endomorphism and Frobenius-scaling uniqueness

Task-124 (handoff Chapter 1 J5, stronger perfection/Frobenius-scaling version).
The actual task-84 p-power Frobenius on the concrete principal-unit value monoid
at the place is used as the source perfection endomorphism; its realification is
proved to be p times the realification by the actual task-84 law
`concretePlace_unitValueKernel_realification_frobenius`.

Proved here:
* `sourcePerfectionFrobenius`: the actual p-power Frobenius endomorphism of the
  concrete unit value monoid;
* `sourcePerfectionFrobenius_mul`: multiplicativity of that endomorphism;
* `sourcePerfectionFrobenius_realification`: the actual p-scaling law
  `realification (phi x) = p * realification x`;
* `realification_unique_up_to_perfection`: general stronger uniqueness: a
  multiplicative additive real-valued map with the same p-scaling law and the
  same values on a representative set whose phi-orbits generate the monoid
  equals the realification;
* `sourcePerfection_realification_unique`: the concrete instantiation at the
  actual p-power Frobenius and the actual task-21 unit value kernel.

Exact remaining statement (reported, not a card): the tree does not provide a
concrete representative/generator theorem saying that every element of the
concrete principal-unit monoid is a natural iterate of the p-power Frobenius
applied to a chosen representative set (the `hgen` hypothesis below).  Hence the
stronger uniqueness is proved conditionally on that generation statement; the
endomorphism, the p-scaling law and the uniqueness theorem itself are actual.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨by simpa [gaussianPolynomial] using gaussianPolynomial_irreducible⟩

/-- The actual source perfection endomorphism: p-power Frobenius on the
concrete principal-unit value monoid at the concrete finite place. -/
def sourcePerfectionFrobenius :
    finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum →
      finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum :=
  fun x => x ^ concreteRationalPrime

/-- The actual p-power Frobenius endomorphism is multiplicative. -/
theorem sourcePerfectionFrobenius_mul
    (x y : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum) :
    sourcePerfectionFrobenius (x * y) =
      sourcePerfectionFrobenius x * sourcePerfectionFrobenius y := by
  unfold sourcePerfectionFrobenius
  rw [mul_pow]

/-- Actual p-scaling of the realification under the source perfection
endomorphism, from the task-84 Frobenius realification law. -/
theorem sourcePerfectionFrobenius_realification
    (x : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
        SourceTheaterCarrier.concreteHeightOneSpectrum).realification (sourcePerfectionFrobenius x) =
      (concreteRationalPrime : ℝ) *
        (finitePlaceUnitValueKernel (F := GaussianField)
          SourceTheaterCarrier.concreteHeightOneSpectrum).realification x :=
  concretePlace_unitValueKernel_realification_frobenius x

/-- Stronger uniqueness up to a perfection endomorphism phi with realification
p-scaling: a multiplicative additive real-valued map is determined by its values
on any set of phi-orbit representatives. -/
theorem realification_unique_up_to_perfection
    {X : Type*} [CommMonoid X] (phi : X → X) (p : ℝ) (f g : X → ℝ)
    (hf : forall x y : X, f (x * y) = f x + f y)
    (hg : forall x y : X, g (x * y) = g x + g y)
    (hfphi : forall x : X, f (phi x) = p * f x)
    (hgphi : forall x : X, g (phi x) = p * g x)
    (S : Set X)
    (hgen : forall x : X, ∃ (n : ℕ) (s : X), s ∈ S ∧ (phi^[n]) s = x)
    (hS : forall s : X, s ∈ S → f s = g s) : f = g := by
  have hfpow : forall (n : ℕ) (s : X), f ((phi^[n]) s) = p ^ n * f s := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        rw [Function.iterate_succ_apply', hfphi, ih]
        ring
  have hgpow : forall (n : ℕ) (s : X), g ((phi^[n]) s) = p ^ n * g s := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        rw [Function.iterate_succ_apply', hgphi, ih]
        ring
  funext x
  obtain ⟨n, s, hs, hx⟩ := hgen x
  rw [← hx, hfpow n s, hgpow n s, hS s hs]

/-- Concrete stronger uniqueness for the actual task-21 unit value kernel: any
multiplicative additive real-valued map with the actual p-power Frobenius
p-scaling and the same values as the kernel on phi-orbit representatives equals
the kernel's realification. -/
theorem sourcePerfection_realification_unique
    (rho : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum → ℝ)
    (hrho : forall x y : finitePlaceUnitValueMonoid (F := GaussianField)
      SourceTheaterCarrier.concreteHeightOneSpectrum, rho (x * y) = rho x + rho y)
    (hrhop : forall x : finitePlaceUnitValueMonoid (F := GaussianField)
      SourceTheaterCarrier.concreteHeightOneSpectrum,
      rho (sourcePerfectionFrobenius x) = (concreteRationalPrime : ℝ) * rho x)
    (S : Set (finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum))
    (hgen : forall x : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum,
      ∃ (n : ℕ) (s : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum),
        s ∈ S ∧ (sourcePerfectionFrobenius^[n]) s = x)
    (hS : forall s : finitePlaceUnitValueMonoid (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum,
      s ∈ S → rho s =
        (finitePlaceUnitValueKernel (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum).realification s) :
    rho = (finitePlaceUnitValueKernel (F := GaussianField)
      SourceTheaterCarrier.concreteHeightOneSpectrum).realification :=
  realification_unique_up_to_perfection sourcePerfectionFrobenius (concreteRationalPrime : ℝ)
    rho (finitePlaceUnitValueKernel (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum).realification
    hrho (finitePlaceUnitValueKernel (F := GaussianField) SourceTheaterCarrier.concreteHeightOneSpectrum).realification_mul
    hrhop
    (concretePlace_unitValueKernel_realification_frobenius)
    S hgen hS


/-! ## Concrete phi-orbit generation for the value group (unconditional stronger uniqueness) -/

/-- The actual p-power Frobenius endomorphism of the finite-place value group
`Multiplicative ℤ`, written additively as exponent multiplication. -/
def sourcePerfectionValueGroupMap : finitePlaceValueGroup → finitePlaceValueGroup :=
  fun x => x ^ concreteRationalPrime

/-- The chosen set of phi-orbit representatives: value-group elements whose
exponent is not divisible by the rational prime (together with the identity). -/
def sourcePerfectionValueGroupRepresentatives : Set finitePlaceValueGroup :=
  fun x => ¬ ((concreteRationalPrime : ℤ) ∣ Multiplicative.toAdd x) ∨
    Multiplicative.toAdd x = 0

/-- Integer p-adic decomposition: every exponent is p^e times an integer not
divisible by p (or else zero). -/
theorem int_eq_prime_pow_mul_not_dvd_or_zero (k : ℤ) :
    ∃ (e : ℕ) (m : ℤ),
      k = (concreteRationalPrime : ℤ) ^ e * m ∧
        (¬ ((concreteRationalPrime : ℤ) ∣ m) ∨ m = 0) := by
  by_cases hk : k = 0
  · exact ⟨0, 0, by rw [hk]; ring, Or.inr rfl⟩
  · have hn : k.natAbs ≠ 0 := by
      simpa [Int.natAbs_eq_zero] using hk
    obtain ⟨e, m0, hndvd, heq⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn concreteRationalPrime
        (Fact.out : concreteRationalPrime.Prime).ne_one
    rcases le_total 0 k with hk0 | hk0
    · have hkabs : (k.natAbs : ℤ) = k := by
        exact_mod_cast (Int.natAbs_of_nonneg hk0)
      refine ⟨e, (m0 : ℤ), ?_, Or.inl ?_⟩
      · rw [← hkabs, heq]
        push_cast
        ring
      · intro hdvd
        exact hndvd (by exact_mod_cast hdvd)
    · have hkabs : (k.natAbs : ℤ) = -k := by
        have h := Int.ofNat_natAbs_of_nonpos hk0
        omega
      refine ⟨e, -(m0 : ℤ), ?_, Or.inl ?_⟩
      · rw [show k = -((k.natAbs : ℤ)) by omega, heq]
        push_cast
        ring
      · intro hdvd
        exact hndvd (by exact_mod_cast (Int.dvd_neg.mp hdvd))


/-- Concrete phi-orbit generation for the actual finite-place value group:
every value-group element is a p-power Frobenius iterate of an element whose
exponent is not divisible by p (or of the identity). -/
theorem sourcePerfectionValueGroup_generation (x : finitePlaceValueGroup) :
    ∃ (n : ℕ) (s : finitePlaceValueGroup),
      s ∈ sourcePerfectionValueGroupRepresentatives ∧
        (sourcePerfectionValueGroupMap^[n]) s = x := by
  obtain ⟨e, m, hm, hcond⟩ := int_eq_prime_pow_mul_not_dvd_or_zero
    (Multiplicative.toAdd x)
  refine ⟨e, Multiplicative.ofAdd m, ?_, ?_⟩
  · exact hcond
  · have hiter : ∀ e : ℕ,
        (sourcePerfectionValueGroupMap^[e]) (Multiplicative.ofAdd m) =
          Multiplicative.ofAdd ((concreteRationalPrime : ℤ) ^ e * m) := by
      intro e
      induction e with
      | zero => simp
      | succ e ih =>
          rw [Function.iterate_succ_apply', ih]
          unfold sourcePerfectionValueGroupMap
          apply Multiplicative.ofAdd.injective
          rw [← ofAdd_nsmul]
          congr 1
          rw [pow_succ]
          simp only [nsmul_eq_mul]
          ring
    rw [hiter, ← hm]
    simpa using (Multiplicative.ofAdd_toAdd x).symm

/-- Actual p-scaling of the value-group realification under the p-power
Frobenius. -/
theorem finitePlaceValueGroupKernel_perfection_scaling
    (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : finitePlaceValueGroup) :
    (finitePlaceValueGroupKernel (F := F) v).realification
        (sourcePerfectionValueGroupMap x) =
      (concreteRationalPrime : ℝ) *
        (finitePlaceValueGroupKernel (F := F) v).realification x := by
  unfold sourcePerfectionValueGroupMap
  rw [finitePlaceValueGroupKernel_realification,
    finitePlaceValueGroupKernel_realification, toAdd_pow, nsmul_eq_mul]
  push_cast
  ring

/-- Unconditional stronger uniqueness up to the actual p-power Frobenius for the
finite-place value-group kernel: a multiplicative additive real-valued map with
the same p-scaling and the same values on the chosen representatives equals the
actual realification. -/
theorem finitePlaceValueGroup_realification_unique_up_to_perfection
    (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (rho : finitePlaceValueGroup → ℝ)
    (hrho : ∀ x y : finitePlaceValueGroup, rho (x * y) = rho x + rho y)
    (hrhop : ∀ x : finitePlaceValueGroup,
      rho (sourcePerfectionValueGroupMap x) = (concreteRationalPrime : ℝ) * rho x)
    (hS : ∀ s : finitePlaceValueGroup, s ∈ sourcePerfectionValueGroupRepresentatives →
      rho s = (finitePlaceValueGroupKernel (F := F) v).realification s) :
    rho = (finitePlaceValueGroupKernel (F := F) v).realification :=
  realification_unique_up_to_perfection sourcePerfectionValueGroupMap
    (concreteRationalPrime : ℝ) rho
    (finitePlaceValueGroupKernel (F := F) v).realification hrho
    (finitePlaceValueGroupKernel (F := F) v).realification_mul hrhop
    (finitePlaceValueGroupKernel_perfection_scaling F v)
    sourcePerfectionValueGroupRepresentatives
    (sourcePerfectionValueGroup_generation) hS

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
