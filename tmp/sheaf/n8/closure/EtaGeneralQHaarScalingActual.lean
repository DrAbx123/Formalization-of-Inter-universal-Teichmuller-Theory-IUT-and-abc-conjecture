import tmp.sheaf.n8.closure.EtaUniformizerFieldRelationActual
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# EtaGeneralQHaarScalingActual

Actual DVR decomposition of an arbitrary nonzero q: using
`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`,
`q = u * π^z` with z : ℤ and u a completion-integer unit (norm-one, fixing O).

The remaining general-q Haar scaling equality is recorded as the exact target;
no arbitrary decomposition is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable def qORegion (q : Kf X) : Set (Kf X) :=
  (fun y : Integers (Kf X) => q * (y : Kf X)) ''
    (Set.univ : Set (Integers (Kf X)))

/-- Actual z^exponent decomposition data for a nonzero field unit. -/
structure QDecomposition (q : (Kf X)ˣ) where
  z : ℤ
  u : (Integers (Kf X))ˣ
  q_eq : (q : Kf X) = u •
    (algebraMap (Integers (Kf X)) (Kf X) (fPlaceDVRUniformizerData X).pi) ^ z
  u_norm_one : ‖(u : Kf X)‖ = 1
  u_fixes_integers :
    (Units.map (algebraMap (Integers (Kf X)) (Kf X)) u : (Kf X)ˣ) •
      (Integers (Kf X) : Set (Kf X)) = (Integers (Kf X) : Set (Kf X))

/-- Actual DVR decomposition of q. -/
noncomputable def qDecomposition (q : (Kf X)ˣ) : QDecomposition X q := by
  haveI : IsFractionRing (Integers (Kf X)) (Kf X) :=
    inferInstanceAs (IsFractionRing (NormedField.valuation (K := Kf X)).integer (Kf X))
  let hex := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := Integers (Kf X)) (K := Kf X)
    (fPlaceDVRUniformizerData X).irreducible (Units.ne_zero q)
  let z : ℤ := Classical.choose hex
  let u : (Integers (Kf X))ˣ := Classical.choose (Classical.choose_spec hex)
  let hu := Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨z, u, ?_, norm_unit_eq_one u,
    integersUnit_smul_integers (X := X) u⟩
  dsimp only [fPlaceDVRUniformizerData]
  exact hu

/-- Exact general-q Haar scaling target. -/
def GeneralQHaarScalingTarget
    (μ : Measure (Kf X)) [μ.IsAddHaarMeasure] : Prop :=
  ∀ q : (Kf X)ˣ,
    μ (qORegion X q) =
      ENNReal.ofReal (‖(q : Kf X)‖ ^ Module.finrank ℚ_[nativePrime X] (Kf X)) *
        μ (Integers (Kf X) : Set (Kf X))

end LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual