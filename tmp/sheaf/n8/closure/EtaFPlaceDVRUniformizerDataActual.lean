import tmp.sheaf.n8.closure.EtaValuedRankLeOneActual
import tmp.sheaf.n8.closure.EtaUniformizerHaarActualAtF
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# EtaFPlaceDVRUniformizerDataActual

Actual F-place DVR uniformizer data using the now-actual DVR instance:
irreducible π, exponent n, unit u, factorization p = u * π^n, n ≠ 0, unit
norm-one, and the unit fixes the integral unit ball.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarActualAtF
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- A completion-integer unit fixes the integral unit ball in K. -/
theorem integersUnit_smul_integers (u : (Integers (Kf X))ˣ) :
    (Units.map (algebraMap (Integers (Kf X)) (Kf X)) u : (Kf X)ˣ) •
      (Integers (Kf X) : Set (Kf X)) = (Integers (Kf X) : Set (Kf X)) := by
  ext x
  simp only [Set.mem_smul_set, Units.smul_def]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Integers (Kf X)).mul_mem u.val.property hy
  · intro hx
    refine ⟨((u⁻¹ : (Integers (Kf X))ˣ).val : Kf X) * x,
      (Integers (Kf X)).mul_mem (u⁻¹).val.property hx, ?_⟩
    change (u.val : Kf X) * (((u⁻¹).val : Kf X) * x) = x
    have h2 : (u.val : Kf X) * ((u⁻¹).val : Kf X) = 1 := by
      exact_mod_cast u.val_inv
    rw [← mul_assoc, h2, one_mul]

noncomputable def chosenPi : Integers (Kf X) :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (Integers (Kf X)))

theorem chosenPi_irreducible : Irreducible (chosenPi X) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Integers (Kf X)))

noncomputable def pFactorData :
    { d : ℕ × (Integers (Kf X))ˣ //
      fPlacePInt X = d.2 * chosenPi X ^ d.1 } :=
  let hfac := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := fPlacePInt X) (fPlacePInt_ne_zero X) (chosenPi_irreducible X)
  ⟨(Classical.choose hfac, Classical.choose (Classical.choose_spec hfac)),
    Classical.choose_spec (Classical.choose_spec hfac)⟩

noncomputable def pExponent : ℕ := (pFactorData X).1.1
noncomputable def pDVRUnit : (Integers (Kf X))ˣ := (pFactorData X).1.2

theorem pDVRUnit_factor :
    fPlacePInt X = pDVRUnit X * chosenPi X ^ pExponent X :=
  (pFactorData X).2

theorem fPlacePInt_not_isUnit : ¬ IsUnit (fPlacePInt X) := by
  rw [Valued.integer.isUnit_iff_norm_eq_one]
  intro h
  apply fPlaceP_norm_ne_one X
  simpa [fPlacePInt, fPlaceP] using h

theorem pExponent_ne_zero : pExponent X ≠ 0 := by
  intro hn
  have hfac := pDVRUnit_factor X
  rw [hn, pow_zero] at hfac
  have hunit : IsUnit (fPlacePInt X) := by
    rw [hfac]
    simpa using (pDVRUnit X).isUnit
  exact fPlacePInt_not_isUnit X hunit

/-- Actual F-place DVR uniformizer data. -/
noncomputable def fPlaceDVRUniformizerData :
    FPlaceDVRUniformizerData X where
  pi := chosenPi X
  irreducible := chosenPi_irreducible X
  exponent := pExponent X
  exponent_ne_zero := pExponent_ne_zero X
  unit := pDVRUnit X
  factor := pDVRUnit_factor X
  unit_norm_one := norm_unit_eq_one (pDVRUnit X)
  unit_fixes_integers := integersUnit_smul_integers (X := X) (pDVRUnit X)

theorem fPlaceDVRUniformizerData_nonempty :
    Nonempty (FPlaceDVRUniformizerData X) :=
  ⟨fPlaceDVRUniformizerData X⟩


end LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
