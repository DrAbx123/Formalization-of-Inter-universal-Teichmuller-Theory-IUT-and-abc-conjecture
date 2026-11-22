import tmp.sheaf.n8.closure.EtaRouteInterface
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Extended-log scalar observations including zero

Uses `ENNReal.log` (extended real log, with `log 0 = ⊥` and `log ⊤ = ⊤`) on
`ENNReal.ofReal ‖·‖`.  The resulting scalar observations are total on
Rval = preLogShell and Rss = logShell, including the zero element, and satisfy
the global multiplicative square identities.  The extension is the canonical
extended logarithm, not an arbitrary convention.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRouteInterface
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaScalarZeroExtension

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance nativeShellNormedField : NormedField (NativeShell X).K :=
  inferInstanceAs (NormedField (CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)))

/-- Extended-log scalar of an element of K: `log (ofReal ‖x‖)` in EReal. -/
noncomputable def extScalar (x : (NativeShell X).K) : EReal :=
  ENNReal.log (ENNReal.ofReal ‖x‖)

/-- Extended-log scalar of the actual pStar element. -/
noncomputable def pStarScalar : EReal :=
  extScalar (X := X) ((NativeShell X).pStar : (NativeShell X).K)

/-- Total scalar observation on Rval = preLogShell. -/
noncomputable def rvalScalar (a : Rval X) : EReal :=
  extScalar (X := X) a.1

/-- Total scalar observation on Rss = logShell. -/
noncomputable def rssScalar (b : Rss X) : EReal :=
  extScalar (X := X) b.1

theorem extScalar_mul (x y : (NativeShell X).K) :
    extScalar (X := X) (x * y) =
      extScalar (X := X) x + extScalar (X := X) y := by
  unfold extScalar
  rw [norm_mul]
  have h : ENNReal.ofReal (‖x‖ * ‖y‖) =
      ENNReal.ofReal ‖x‖ * ENNReal.ofReal ‖y‖ :=
    ENNReal.ofReal_mul (norm_nonneg x)
  rw [h]
  exact ENNReal.log_mul_add

theorem extScalar_pStar_inv :
    extScalar (X := X) (((NativeShell X).pStar : (NativeShell X).K)⁻¹) =
      - pStarScalar (X := X) := by
  unfold extScalar pStarScalar
  have hp : ((NativeShell X).pStar : (NativeShell X).K) ≠ 0 :=
    SourceLogShellDatum.pStar_ne_zero_cast (NativeShell X)
  rw [norm_inv, ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hp)]
  exact ENNReal.log_inv

/-- Global etaQ scalar square, valid at zero too. -/
theorem etaQ_scalar_square (a : Rval X) :
    rssScalar X (EtaQ X a) = - pStarScalar X + rvalScalar X a := by
  unfold rssScalar rvalScalar EtaQ
  change extScalar (X := X)
      (((NativeShell X).pStar : (NativeShell X).K)⁻¹ * a.1) =
    - pStarScalar (X := X) + extScalar (X := X) a.1
  rw [extScalar_mul, extScalar_pStar_inv]

/-- Global etaAnab scalar square, valid at zero too. -/
theorem etaAnab_scalar_square (b : Rss X) :
    rvalScalar X (EtaAnab X b) = pStarScalar X + rssScalar X b := by
  unfold rvalScalar rssScalar EtaAnab
  change extScalar (X := X)
      (((NativeShell X).pStar : (NativeShell X).K) * b.1) =
    pStarScalar (X := X) + extScalar (X := X) b.1
  rw [extScalar_mul]
  rfl

end LeanFormal.IUT.N8Closure.EtaScalarZeroExtension

end