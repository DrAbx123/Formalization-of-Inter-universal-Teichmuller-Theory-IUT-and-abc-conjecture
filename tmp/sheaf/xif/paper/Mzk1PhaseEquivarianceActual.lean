import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Route 3 C-Phase: independent mu2l phases and the 2l-power readout ledger

This file isolates the elementary algebra behind IUT II Remark 2.5.1(iii):
the mu2l indeterminacies at different labels are independent.

* phaseAction changes each theta value by an independent root of unity;
* weightedProduct is the product with integer weights;
* independent_phase_invariant_iff proves that invariance for ALL independent
  phase families is equivalent to each weight being divisible by 2l;
* phase_product_pow_twoL proves that the 2l-th power kills all independent
  phase factors;
* log_readout_pow_twoL records the exact readout price: the logarithm is
  multiplied by 2l.

The file does NOT assert that a theta value or its 2l-th power is the correct
paper comparison object. It supplies the phase bookkeeping only; see
coord/ROUTE3-PHASE.md.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PhaseEquivarianceActual

universe u

/-- Independent phase action on a family of values in a commutative monoid. -/
def phaseAction {M : Type u} [CommMonoid M] {ι : Type*}
    (zeta : ι -> M) (theta : ι -> M) : ι -> M :=
  fun j => zeta j * theta j

/-- Weighted product of a family, with natural-number weights. -/
def weightedProduct {M : Type u} [CommMonoid M] {ι : Type*} [Fintype ι]
    (theta : ι -> M) (a : ι -> Nat) : M :=
  ∏ j, theta j ^ a j

/-- The phase factor of a weighted product is the product of the individual
phase powers. -/
theorem weightedProduct_phaseAction
    {M : Type u} [CommMonoid M] {ι : Type*} [Fintype ι]
    (zeta theta : ι -> M) (a : ι -> Nat) :
    weightedProduct (phaseAction zeta theta) a =
      (∏ j, zeta j ^ a j) * weightedProduct theta a := by
  simp [weightedProduct, phaseAction, mul_pow, Finset.prod_mul_distrib]

/-- Invariance under every independent phase family is equivalent to all
weights being divisible by 2l.  The forward direction tests one label at a
time with a primitive 2l-th root; the reverse direction uses
zeta_j^(2l)=1 and 2l | a_j. -/
theorem independent_phase_invariant_iff
    {M : Type u} [CommMonoid M] {ι : Type*} [Fintype ι]
    (l : Nat) (omega : M) (homega : IsPrimitiveRoot omega (2 * l))
    (a : ι -> Nat) :
    (∀ zeta : ι -> M, (∀ j, zeta j ^ (2 * l) = 1) ->
        (∏ j, zeta j ^ a j) = 1) ↔
      ∀ j, 2 * l ∣ a j := by
  constructor
  · intro h j
    classical
    let zeta : ι -> M := fun k => if k = j then omega else 1
    have hzeta : ∀ k, zeta k ^ (2 * l) = 1 := by
      intro k
      by_cases hk : k = j
      · simp [zeta, hk, homega.pow_eq_one]
      · simp [zeta, hk]
    have hprod := h zeta hzeta
    have hprod_j : (∏ k, zeta k ^ a k) = omega ^ a j := by
      classical
      calc
        (∏ k, zeta k ^ a k) = zeta j ^ a j := by
          refine Finset.prod_eq_single_of_mem j (Finset.mem_univ j) ?_
          intro k _ hkj
          simp [zeta, hkj]
        _ = omega ^ a j := by simp [zeta]
    rw [hprod_j] at hprod
    exact (homega.pow_eq_one_iff_dvd (a j)).mp hprod
  · intro hdiv zeta hzeta
    refine Finset.prod_eq_one ?_
    intro j _
    rcases hdiv j with ⟨c, hc⟩
    rw [hc, pow_mul, hzeta j, one_pow]

/-- Taking the 2l-th power kills all independent phase factors. -/
theorem phase_product_pow_twoL
    {M : Type u} [CommMonoid M] {ι : Type*} [Fintype ι]
    (l : Nat) (zeta theta : ι -> M)
    (hzeta : ∀ j, zeta j ^ (2 * l) = 1) :
    (∏ j, (zeta j * theta j) ^ (2 * l)) =
      ∏ j, theta j ^ (2 * l) := by
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [mul_pow, hzeta j, one_mul]

theorem weightedProduct_pow_twoL
    {M : Type u} [CommMonoid M] {ι : Type*} [Fintype ι]
    (l : Nat) (zeta theta : ι -> M) (a : ι -> Nat)
    (hzeta : ∀ j, zeta j ^ (2 * l) = 1) :
    (weightedProduct (phaseAction zeta theta) a) ^ (2 * l) =
      (weightedProduct theta a) ^ (2 * l) := by
  rw [weightedProduct_phaseAction]
  -- The phase factor has (2l)-th power one; the remaining factor is theta.
  have hphase : (∏ j, zeta j ^ a j) ^ (2 * l) = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one ?_
    intro j _
    rw [← pow_mul, mul_comm (a j) (2 * l), pow_mul, hzeta j, one_pow]
  rw [mul_pow, hphase, one_mul]

/-- Readout ledger: the 2l-th power multiplies the real logarithm by 2l. -/
theorem log_readout_pow_twoL {x : Real} (_hx : 0 < x) (l : Nat) :
    Real.log (x ^ (2 * l)) = (2 * (l : Real)) * Real.log x := by
  rw [Real.log_pow]
  norm_num

#print axioms independent_phase_invariant_iff
#print axioms phase_product_pow_twoL
#print axioms weightedProduct_pow_twoL
#print axioms log_readout_pow_twoL

end LeanFormal.IUT.XiFPaper.Mzk1PhaseEquivarianceActual
