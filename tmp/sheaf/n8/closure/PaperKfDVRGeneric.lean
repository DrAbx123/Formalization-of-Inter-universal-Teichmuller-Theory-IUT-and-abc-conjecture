import tmp.sheaf.n8.closure.PaperKfHaarNormActual
import tmp.sheaf.n8.closure.EtaUniformizerHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# Generic DVR decomposition for PaperKf

Actual DVR decomposition q = u * pi^z for an arbitrary unit q, using Mathlib's
exists_units_eq_smul_zpow_of_irreducible with a chosen actual irreducible
uniformizer.  The integral unit u has norm one and fixes the integer ball.
The uniformizer relation pi^e = pUnit * u with positive e is recorded as the
exact remaining positivity/power relation; no arbitrary uniformizer and no
native X.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperKfDVRGeneric

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperKfHaarNormActual
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarScaling
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise NNReal

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance : IsDiscreteValuationRing (Integers (PaperKf S)) :=
  LeanFormal.IUT.LocalFieldLogarithm.isDiscreteValuationRingIntegers (K := PaperKf S) (p := pNat S)

/-- Actual chosen irreducible uniformizer in the completion integers. -/
noncomputable def paperUniformizer : Integers (PaperKf S) :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible
    (Integers (PaperKf S)))

theorem paperUniformizer_irreducible : Irreducible (paperUniformizer S) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
    (Integers (PaperKf S)))

theorem paperUniformizer_ne_zero : (paperUniformizer S : PaperKf S) ≠ 0 := by
  intro h
  exact (paperUniformizer_irreducible S).ne_zero (Subtype.ext h)

noncomputable def paperUniformizerUnit : (PaperKf S)ˣ :=
  Units.mk0 (paperUniformizer S : PaperKf S) (paperUniformizer_ne_zero S)

/-- Actual DVR decomposition of any field unit by the chosen uniformizer:
q = u * pi^z with integral unit u. -/
theorem exists_paperQ_decomposition (q : (PaperKf S)ˣ) :
    ∃ (z : ℤ) (u : (PaperKf S)ˣ),
      q = u * paperUniformizerUnit S ^ z ∧
      u • (Integers (PaperKf S) : Set (PaperKf S)) =
        (Integers (PaperKf S) : Set (PaperKf S)) ∧
      ‖(u : PaperKf S)‖ = 1 := by
  haveI : IsFractionRing (Integers (PaperKf S)) (PaperKf S) :=
    inferInstanceAs (IsFractionRing
      (NormedField.valuation (K := PaperKf S)).integer (PaperKf S))
  obtain ⟨z, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := Integers (PaperKf S)) (K := PaperKf S)
    (paperUniformizer_irreducible S) (Units.ne_zero q)
  let uK : (PaperKf S)ˣ := integerUnitInK (K := PaperKf S) u
  refine ⟨z, uK, ?_, ?_, ?_⟩
  · apply Units.ext
    have halg : (algebraMap (Integers (PaperKf S)) (PaperKf S))
        (u : Integers (PaperKf S)) = (u : PaperKf S) := rfl
    have halgπ : (algebraMap (Integers (PaperKf S)) (PaperKf S))
        (paperUniformizer S) = (paperUniformizer S : PaperKf S) := rfl
    have hu' : (q : PaperKf S) =
        ((u : Integers (PaperKf S)) : PaperKf S) *
          ((paperUniformizer S : PaperKf S)) ^ z := by
      simpa [Units.smul_def, Algebra.smul_def, halg, halgπ] using hu
    simpa [uK, paperUniformizerUnit, integerUnitInK, Units.val_mul,
      Units.val_zpow_eq_zpow_val] using hu'
  · exact integerUnit_smul_O (K := PaperKf S) u
  · exact norm_unit_eq_one (K := PaperKf S) u

/-- The general-q decomposition target is now actual. -/
theorem missingGeneralQDecomposition_actual :
    MissingGeneralQDecomposition S := by
  refine ⟨paperUniformizerUnit S, ?_⟩
  intro q
  rcases exists_paperQ_decomposition S q with ⟨z, u, hq, huO, hunorm⟩
  exact ⟨z, u, hq, huO, hunorm⟩

end LeanFormal.IUT.N8Closure.PaperKfDVRGeneric

end