import tmp.sheaf.n8.closure.EtaUniformizerHaarActualAtF

/-!
# EtaUniformizerRelationActual

Actual attempt at the F-place uniformizer relation `π^e = pUnit * u`.

The rational prime element, its norm and integrality are actual.  The next
production dependency is missing: the tree has **no**
`IsDiscreteValuationRing (Integers K)` instance for the completion integer
ring (recorded in `IntegralLogShellIndexResidueFormula` as an explicit missing
Mathlib interface).  Consequently the DVR factorization
`p = u * π^n` and its unit properties cannot be constructed here.

The exact target (DVR factorization plus norm-one/O-fixing unit) is recorded
as a named gap.  No arbitrary π/u is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarActualAtF
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable def fPlaceP : Kf X := algebraMap ℚ_[nativePrime X] (Kf X) (nativePrime X)

theorem fPlaceP_norm : ‖fPlaceP X‖ = ((nativePrime X : ℝ))⁻¹ := by
  rw [fPlaceP, norm_algebraMap']
  exact Padic.norm_p

theorem fPlaceP_ne_zero : fPlaceP X ≠ 0 := by
  rw [← norm_ne_zero_iff, fPlaceP_norm]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime (nativePrime X)).ne_zero)

theorem fPlaceP_mem_integers : fPlaceP X ∈ Integers (Kf X) := by
  rw [mem_integers_iff, fPlaceP_norm]
  rw [inv_le_one₀ (by exact_mod_cast (Fact.out : Nat.Prime (nativePrime X)).pos)]
  exact_mod_cast (Fact.out : Nat.Prime (nativePrime X)).one_lt.le

noncomputable def fPlacePInt : Integers (Kf X) :=
  ⟨fPlaceP X, fPlaceP_mem_integers X⟩

theorem fPlacePInt_ne_zero : fPlacePInt X ≠ 0 := by
  intro h
  exact fPlaceP_ne_zero X (congrArg Subtype.val h)

/-- Exact missing DVR uniformizer data: irreducible π in the completion
integers, exponent n, unit u, factorization of the rational prime, and the
unit is norm-one and fixes the integral unit ball in K. -/
structure FPlaceDVRUniformizerData (X : N8NativeInput l) where
  pi : Integers (Kf X)
  irreducible : Irreducible pi
  exponent : ℕ
  exponent_ne_zero : exponent ≠ 0
  unit : (Integers (Kf X))ˣ
  factor : fPlacePInt X = unit * pi ^ exponent
  unit_norm_one : ‖((Units.map (algebraMap (Integers (Kf X)) (Kf X)) unit :
    (Kf X)ˣ) : Kf X)‖ = 1
  unit_fixes_integers :
    (Units.map (algebraMap (Integers (Kf X)) (Kf X)) unit : (Kf X)ˣ) •
      (Integers (Kf X) : Set (Kf X)) = (Integers (Kf X) : Set (Kf X))

def FPlaceDVRUniformizerDataExists (X : N8NativeInput l) : Prop :=
  Nonempty (FPlaceDVRUniformizerData X)

end LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual