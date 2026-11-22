import tmp.sheaf.n8.closure.PaperKfQOScalingGeneral
import tmp.sheaf.n8.closure.EtaUniformizerCharRootActual

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# PaperKf Haar norm: actual p-unit and uniformizer steps

Actual generic p-unit norm `mK(pUnit)=||pUnit||^d` from
`EtaHaarCharNormIdentification.haarNorm_pUnit`, and the actual uniformizer
step from a DVR relation `pi^e = pUnit * u` with integral unit u.  The
existence of that relation and the general-q decomposition are recorded as
exact generic gaps; no native X and no arbitrary uniformizer are used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperKfHaarNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassTransport
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
open LeanFormal.IUT.N8Closure.EtaUniformizerCharRootActual
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise NNReal

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩

noncomputable def paperPrimeUnit : (PaperKf S)ˣ :=
  primeUnit (K := PaperKf S) (p := pNat S)

theorem paperKf_localDimension_eq_d :
    localDimension (K := PaperKf S) (p := pNat S) = C7QPilotMassActual.d S := rfl

theorem paperKf_mK_primeUnit :
    mK (K := PaperKf S) (paperPrimeUnit S) =
      ‖((paperPrimeUnit S : (PaperKf S)ˣ) : PaperKf S)‖ ^
        C7QPilotMassActual.d S := by
  simpa [paperPrimeUnit, paperKf_localDimension_eq_d S] using
    haarNorm_pUnit (K := PaperKf S) (p := pNat S)

theorem paperKf_distribHaarChar_primeUnit :
    distribHaarChar (PaperKf S) (paperPrimeUnit S) =
      Real.toNNReal
        ((‖((paperPrimeUnit S : (PaperKf S)ˣ) : PaperKf S)‖) ^
          C7QPilotMassActual.d S) := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (pow_nonneg (norm_nonneg _) _)]
  exact paperKf_mK_primeUnit S

/-- Actual uniformizer norm step from the DVR relation `pi^e = pUnit * u`. -/
theorem paperKf_mK_uniformizer_of_relation
    (π u : (PaperKf S)ˣ) (e : ℕ) (he : e ≠ 0)
    (hrel : π ^ e = paperPrimeUnit S * u)
    (huO : u • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S)))
    (hunorm : ‖(u : PaperKf S)‖ = 1) :
    mK (K := PaperKf S) π =
      ‖(π : PaperKf S)‖ ^ C7QPilotMassActual.d S := by
  have hO := measure_localIntegers_pos_lt_top
    (K := PaperKf S) (Measure.addHaar : Measure (PaperKf S))
  have hchar := uniformizer_char_eq_norm_pow_d
    (K := PaperKf S) (μ := (Measure.addHaar : Measure (PaperKf S)))
    π (paperPrimeUnit S) u e (C7QPilotMassActual.d S) he
    (paperKf_distribHaarChar_primeUnit S) hrel huO hunorm
    hO.1.ne' hO.2.ne
  unfold mK
  rw [hchar]
  rw [Real.coe_toNNReal _ (pow_nonneg (norm_nonneg _) _)]

/-- Exact generic DVR relation target: an arbitrary completion uniformizer
is linked to the rational p-unit by a positive power and an integral unit. -/
def MissingUniformizerRelation : Prop :=
  ∀ (π : (PaperKf S)ˣ),
    ∃ (e : ℕ) (u : (PaperKf S)ˣ), e ≠ 0 ∧
      π ^ e = paperPrimeUnit S * u ∧
      u • (Integers (PaperKf S) : Set (PaperKf S)) =
        (Integers (PaperKf S) : Set (PaperKf S)) ∧
      ‖(u : PaperKf S)‖ = 1

/-- Exact generic general-q decomposition target: every q is an integral
unit times an integral power of a fixed uniformizer. -/
def MissingGeneralQDecomposition : Prop :=
  ∃ (π : (PaperKf S)ˣ),
    ∀ q : (PaperKf S)ˣ, ∃ (z : ℤ) (u : (PaperKf S)ˣ),
      q = u * π ^ z ∧
      u • (Integers (PaperKf S) : Set (PaperKf S)) =
        (Integers (PaperKf S) : Set (PaperKf S)) ∧
      ‖(u : PaperKf S)‖ = 1

end LeanFormal.IUT.N8Closure.PaperKfHaarNormActual

end