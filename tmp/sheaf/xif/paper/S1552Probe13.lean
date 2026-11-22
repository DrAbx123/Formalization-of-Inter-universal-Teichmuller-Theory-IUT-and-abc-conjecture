import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace S1552Probe13
variable (P : NumberField.FinitePlace ℚ)

local instance completionMeasurableSpace : MeasurableSpace (Completion P) := borel (Completion P)
local instance completionBorelSpace : BorelSpace (Completion P) := ⟨rfl⟩

local instance instAlgebraRatCompletionAux : Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)

local instance factTargetPrime : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

example : Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal : Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val])

example : Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] := by
  let pP : ℕ := (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val
  haveI : Fact (Nat.Prime pP) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal : Completion P ≃+* ℚ_[pP])

end S1552Probe13
