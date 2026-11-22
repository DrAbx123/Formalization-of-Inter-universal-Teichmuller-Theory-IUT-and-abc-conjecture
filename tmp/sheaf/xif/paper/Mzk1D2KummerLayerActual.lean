import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicNumbers
import PadicField.FieldNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import ContinuousKummerTheory.Kummer.PAdic
import ContinuousKummerTheory.Kummer.Equiv

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1D2KummerLayerActual
open LeanFormal.IUT

/-- Actual finite Kummer layer: the descended absolute Kummer map on
`K^x/(K^x)^n`, together with its injectivity and the explicit iso field
that remains the paper-level Kummer identification. -/
structure D2KummerLayer (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n] where
  rootsFixed : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)
  kummerMap :
    (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n)) →*
      ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
        rootsOfUnity n (AlgebraicClosure K))
  kummerMap_eq :
    kummerMap = AbsoluteKummerQuotient.absoluteKummerMapQuotient rootsFixed
  injective : Function.Injective kummerMap
  bijective : Function.Bijective kummerMap

/-- Transition compatibility and the inverse-limit statement. -/
structure D2KummerTransition (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n] [NeZero (n + 1)] where
  transition : D2KummerLayer K (n + 1) → D2KummerLayer K n
  inverseLimit : Type



/-- Cardinality criterion used by the finite-quotient Kummer route. -/
theorem bijective_of_injective_and_card {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hinj : Function.Injective f)
    (hcard : Fintype.card A = Fintype.card B) :
    Function.Bijective f :=
  (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩

#print axioms bijective_of_injective_and_card


/-- Finiteness of monoid homs from finiteness of the underlying function space. -/
noncomputable instance finiteMonoidHomOfFinite {G M : Type*} [Monoid G] [Monoid M]
    [Finite G] [Finite M] : Finite (G →* M) :=
  Finite.of_injective (fun f : G →* M => (f : G → M)) DFunLike.coe_injective

#print axioms finiteMonoidHomOfFinite
section Q5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Concrete local unit class map at `Q5`: the unnormalised valuation
`PadicField.wval` reduced modulo `n`. -/
noncomputable def q5WvalModN (n : ℕ) :
    (ℚ_[5])ˣ →* Multiplicative (ZMod n) where
  toFun u := Multiplicative.ofAdd ((PadicField.wval (p := 5) (x := (u : ℚ_[5])) : ZMod n))
  map_one' := by
    simp [PadicField.wval_one]
  map_mul' u v := by
    have hu : (u : ℚ_[5]) ≠ 0 := Units.ne_zero u
    have hv : (v : ℚ_[5]) ≠ 0 := Units.ne_zero v
    rw [Units.val_mul, PadicField.wval_mul hu hv]
    simp [Int.cast_add]

#print axioms q5WvalModN


/-- The actual kernel subgroup of `q5WvalModN`: units whose `wval` is
divisible by `n`.  This is NOT the subgroup of n-th powers. -/
noncomputable def q5WvalKernel (n : ℕ) : Subgroup (ℚ_[5])ˣ where
  carrier := {u | (n : ℤ) ∣ PadicField.wval (p := 5) (x := (u : ℚ_[5]))}
  one_mem' := by
    change (n : ℤ) ∣ PadicField.wval (p := 5) (x := (1 : ℚ_[5]))
    rw [PadicField.wval_one]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    change (n : ℤ) ∣ PadicField.wval (p := 5) (x := ((a : ℚ_[5]) * (b : ℚ_[5])))
    rw [PadicField.wval_mul (Units.ne_zero a) (Units.ne_zero b)]
    exact dvd_add ha hb
  inv_mem' := by
    intro a ha
    have h1 : (n : ℤ) ∣ PadicField.wval (p := 5) (x := ((a : ℚ_[5])⁻¹)) := by
      rw [PadicField.wval_inv (Units.ne_zero a)]
      exact dvd_neg.mpr ha
    simpa using h1

/-- Exact kernel relation for the concrete Q5 valuation-class map. -/
theorem q5WvalModN_ker (n : ℕ) [NeZero n] :
    (q5WvalModN n).ker = q5WvalKernel n := by
  ext u
  change (q5WvalModN n) u = 1 ↔
    (n : ℤ) ∣ PadicField.wval (p := 5) (x := (u : ℚ_[5]))
  constructor
  · intro h
    have h' : ((PadicField.wval (p := 5) (x := (u : ℚ_[5])) : ZMod n)) = 0 := by
      simpa [q5WvalModN, ofAdd_eq_one] using h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  · intro h
    change (q5WvalModN n) u = 1
    rw [show (q5WvalModN n) u =
      Multiplicative.ofAdd ((PadicField.wval (p := 5) (x := (u : ℚ_[5])) : ZMod n)) from rfl]
    rw [ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h

#print axioms q5WvalKernel
#print axioms q5WvalModN_ker


/-- Finiteness of the Q5 Kummer quotient, from the continuous Kummer theory
donor `FiniteKummerQuotients ℚ_[5]`. -/
instance finiteQ5KummerQuotient (n : ℕ) [NeZero n] :
    Finite ((ℚ_[5])ˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := ℚ_[5]) (n := n)) := by
  change Finite ((ℚ_[5])ˣ ⧸ (powMonoidHom n : (ℚ_[5])ˣ →* (ℚ_[5])ˣ).range)
  have h := KummerTheory.FiniteKummerQuotients.finiteIndex (K := ℚ_[5]) n (NeZero.ne n)
  exact Subgroup.finite_quotient_of_finiteIndex

#print axioms finiteQ5KummerQuotient

/-- `Mu n Ω` is definitionally `rootsOfUnity n Ω`. -/
def muEquivRootsOfUnity (n : ℕ) (Ω : Type*) [Field Ω] :
    KummerTheory.Mu n Ω ≃* rootsOfUnity n Ω :=
  MulEquiv.refl _

/-- Actual Kummer equivalence: `Kˣ/(Kˣ)^n ≃* H¹_cont(Gal(Kbar/K), μ_n)`. -/
noncomputable def q5KummerEquivContH1 (n : ℕ) [NeZero n] :
    (ℚ_[5])ˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := ℚ_[5]) (n := n) ≃*
      ContH1 (AlgebraicClosure ℚ_[5] ≃ₐ[ℚ_[5]] AlgebraicClosure ℚ_[5])
        (KummerTheory.Mu n (AlgebraicClosure ℚ_[5])) :=
  KummerTheory.kummerEquiv n ℚ_[5] (AlgebraicClosure ℚ_[5])

#print axioms muEquivRootsOfUnity
#print axioms q5KummerEquivContH1

theorem q5KummerCard_eq_contH1 (n : ℕ) [NeZero n] :
    Nat.card ((ℚ_[5])ˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := ℚ_[5]) (n := n)) =
      Nat.card (ContH1 (AlgebraicClosure ℚ_[5] ≃ₐ[ℚ_[5]] AlgebraicClosure ℚ_[5])
        (KummerTheory.Mu n (AlgebraicClosure ℚ_[5]))) :=
  Nat.card_congr (q5KummerEquivContH1 n).toEquiv

#print axioms q5KummerCard_eq_contH1
end Q5



variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- Explicit finite factorization data for a Kummer layer along a finite normal
subextension.  The section `lift` is arbitrary data (not required to be a
homomorphism), but its values are used only through `factor_spec`; the
kernel-triviality field records the actual factorization hypothesis. -/
structure D2FiniteFactorization (h : D2KummerLayer K n)
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [Normal K L] where
  lift : (L ≃ₐ[K] L) → (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  lift_spec : ∀ σ, AlgEquiv.restrictNormalHom L (lift σ) = σ
  factor :
    (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n)) →*
      ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K))
  factor_spec : ∀ (q : Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n))
    (σ : L ≃ₐ[K] L), factor q σ = h.kummerMap q (lift σ)
  kernel_trivial : ∀ (q : Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n))
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
    AlgEquiv.restrictNormalHom L τ = 1 → h.kummerMap q τ = 1

namespace D2FiniteFactorization

variable {h : D2KummerLayer K n}
variable {L : IntermediateField K (AlgebraicClosure K)}
variable [FiniteDimensional K L] [Normal K L]
variable (F : D2FiniteFactorization (K := K) (n := n) h L)

theorem factor_injective : Function.Injective F.factor := by
  intro q₁ q₂ hq
  apply h.injective
  apply MonoidHom.ext
  intro τ
  let σ : L ≃ₐ[K] L := AlgEquiv.restrictNormalHom L τ
  have hker : AlgEquiv.restrictNormalHom L ((F.lift σ)⁻¹ * τ) = 1 := by
    simp [map_mul, F.lift_spec σ, σ]
  have hk := F.kernel_trivial q₁ ((F.lift σ)⁻¹ * τ) hker
  have hk₂ := F.kernel_trivial q₂ ((F.lift σ)⁻¹ * τ) hker
  have hμ : h.kummerMap q₁ τ = h.kummerMap q₂ τ := by
    calc
      h.kummerMap q₁ τ = h.kummerMap q₁ (F.lift σ * ((F.lift σ)⁻¹ * τ)) := by simp
      _ = h.kummerMap q₁ (F.lift σ) * h.kummerMap q₁ ((F.lift σ)⁻¹ * τ) := map_mul (h.kummerMap q₁) (F.lift σ) ((F.lift σ)⁻¹ * τ)
      _ = h.kummerMap q₁ (F.lift σ) := by rw [hk, mul_one]
      _ = (F.factor q₁ σ : rootsOfUnity n (AlgebraicClosure K)) := by
        rw [F.factor_spec]
      _ = F.factor q₂ σ := by rw [hq]
      _ = h.kummerMap q₂ (F.lift σ) := by rw [F.factor_spec]
      _ = h.kummerMap q₂ (F.lift σ * ((F.lift σ)⁻¹ * τ)) := by
        rw [map_mul, hk₂, mul_one]
      _ = h.kummerMap q₂ τ := by
        exact congrArg (h.kummerMap q₂) (by group)
  exact hμ

theorem factor_bijective_of_card
    [Fintype (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n))]
    [Fintype ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K))]
    (hcard : Fintype.card (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n)) =
      Fintype.card ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K))) :
    Function.Bijective F.factor :=
  bijective_of_injective_and_card F.factor F.factor_injective hcard


/-- Cardinality version using `Nat.card`/`Finite`, avoiding explicit Fintype
instances for the quotient and hom target. -/
theorem factor_bijective_of_nat_card
    [Finite (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n))]
    [Finite ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K))]
    (hcard : Nat.card (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n)) =
      Nat.card ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K))) :
    Function.Bijective F.factor := by
  haveI : Fintype (Kˣ ⧸ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n)) :=
    Fintype.ofFinite _
  haveI : Fintype ((L ≃ₐ[K] L) →* rootsOfUnity n (AlgebraicClosure K)) :=
    Fintype.ofFinite _
  apply bijective_of_injective_and_card F.factor F.factor_injective
  simpa only [Nat.card_eq_fintype_card] using hcard

#print axioms factor_bijective_of_nat_card

end D2FiniteFactorization

#print axioms D2FiniteFactorization.factor_injective
#print axioms D2FiniteFactorization.factor_bijective_of_card

end LeanFormal.IUT.XiFPaper.Mzk1D2KummerLayerActual