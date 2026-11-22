import tmp.sheaf.n8.closure.EtaPStepNormLink
import tmp.sheaf.n8.closure.EtaUniformizerCharRootActual

/-!
# EtaUniformizerHaarActualAtF

Closure at the native F-place: use the actual p-step normalization (proved in
`EtaPStepNormLink`) and the uniformizer root theorem to derive

  distribHaarChar K π = toNNReal (‖π‖ ^ d)

for K = CommonPrimeCompletion (nativeFPlaceAtPrime X), d = finrank Qp K,
under the actual uniformizer relation `π^e = pUnit * u` with `u` norm-one and
fixing the integral unit ball.

Then the general-q decomposition `q = u * π^n` is recorded as the exact
remaining scaling step; no arbitrary decomposition/root is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUniformizerHaarActualAtF

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.N8Closure.EtaUniformizerCharRootActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal Pointwise ENNReal

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

local notation "dF" => Module.finrank ℚ_[nativePrime X] (Kf X)

/-- Actual F-place uniformizer Haar character, from the p-step normalization
and the uniformizer relation. -/
theorem distribHaarChar_uniformizer_at_F
    (μ : Measure (Kf X)) [μ.IsAddHaarMeasure] [μ.Regular]
    (π u : (Kf X)ˣ) (e : ℕ) (he : e ≠ 0)
    (hrel : π ^ e = pUnit (p := nativePrime X) (K := Kf X) * u)
    (huO : u • (Integers (Kf X) : Set (Kf X)) = (Integers (Kf X) : Set (Kf X)))
    (hu_norm : ‖(u : Kf X)‖ = 1)
    (h0 : μ (Integers (Kf X) : Set (Kf X)) ≠ 0)
    (hfin : μ (Integers (Kf X) : Set (Kf X)) ≠ ∞) :
    distribHaarChar (Kf X) π = Real.toNNReal ((‖(π : Kf X)‖) ^ dF) := by
  exact uniformizer_char_eq_norm_pow_d (K := Kf X)
    μ π (pUnit (p := nativePrime X) (K := Kf X)) u e (dF) he
    (distribHaarChar_nativePUnit_eq_toNNReal_norm_pow (X := X) μ h0 hfin)
    hrel huO hu_norm h0 hfin

end LeanFormal.IUT.N8Closure.EtaUniformizerHaarActualAtF