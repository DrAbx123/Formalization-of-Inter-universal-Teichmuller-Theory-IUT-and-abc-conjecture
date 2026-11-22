import tmp.sheaf.n8.closure.EtaUniformizerRelationActual

/-!
# EtaNontriviallyNormedKfActual

Actual `NontriviallyNormedField (Kf X)` instance from the rational-prime
element `fPlaceP`, whose norm is `p⁻¹ ≠ 1`.

Then test whether the production `Valued.v` instance inherits
`IsNontrivial`/`RankOne`.  If not, that normalized-valuation comparison is the
exact remaining gap; no arbitrary instance is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem fPlaceP_norm_ne_one : ‖fPlaceP X‖ ≠ 1 := by
  rw [fPlaceP_norm]
  have hp1 : (1 : ℝ) < (nativePrime X : ℝ) :=
    by exact_mod_cast (Fact.out : Nat.Prime (nativePrime X)).one_lt
  exact ne_of_lt (inv_lt_one_of_one_lt₀ hp1)

/-- Actual nontrivially normed field structure at Kf. -/
noncomputable instance nontriviallyNormedFieldKf : NontriviallyNormedField (Kf X) :=
  NontriviallyNormedField.ofNormNeOne (𝕜 := Kf X)
    ⟨fPlaceP X, fPlaceP_ne_zero X, fPlaceP_norm_ne_one X⟩

end LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual