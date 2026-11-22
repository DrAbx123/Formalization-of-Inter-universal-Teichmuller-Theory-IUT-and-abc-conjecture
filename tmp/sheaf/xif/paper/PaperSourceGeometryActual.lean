import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-! # Completion-valued source geometry

This is the first source-model change authorized by the user.  Instead of an
abstract value monoid `Mon v` with no completion-valued map, the local value
carrier is the actual unit group of the actual finite-place completion.  The
identity/coercion is then a genuine monoid map to the completion, and the
degree is the actual p-adic norm logarithm. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The actual local value carrier: units of the actual completion. -/
abbrev CompletionValueCarrier : Type u := (CommonPrimeCompletion place)ˣ

/-- The actual value-to-completion map: coercion of units. -/
def completionValueToCompletion :
    CompletionValueCarrier place →* CommonPrimeCompletion place :=
  Units.coeHom (M := CommonPrimeCompletion place)

theorem completionValueToCompletion_apply (u : CompletionValueCarrier place) :
    completionValueToCompletion place u = (u : CommonPrimeCompletion place) := rfl

theorem completionValueToCompletion_injective :
    Function.Injective (completionValueToCompletion place) := by
  intro u v h
  change ((u : CommonPrimeCompletion place) = (v : CommonPrimeCompletion place)) at h
  exact Units.ext h

theorem completionValueToCompletion_ne_zero (u : CompletionValueCarrier place) :
    completionValueToCompletion place u ≠ 0 := by
  change ((u : CommonPrimeCompletion place) ≠ 0)
  exact Units.ne_zero u

/-- The actual p-adic degree of a value unit. -/
def completionValueDegree :
    CompletionValueCarrier place →* Multiplicative Real where
  toFun u := Multiplicative.ofAdd (Real.log ‖(u : CommonPrimeCompletion place)‖)
  map_one' := by
    change Multiplicative.ofAdd (Real.log ‖(1 : CommonPrimeCompletion place)‖) = 1
    rw [norm_one, Real.log_one, ofAdd_zero]
  map_mul' := by
    intro u v
    change Multiplicative.ofAdd
        (Real.log ‖((u * v : CompletionValueCarrier place) : CommonPrimeCompletion place)‖) =
      Multiplicative.ofAdd (Real.log ‖(u : CommonPrimeCompletion place)‖) *
        Multiplicative.ofAdd (Real.log ‖(v : CommonPrimeCompletion place)‖)
    rw [Units.val_mul, norm_mul, Real.log_mul]
    · rfl
    · exact norm_ne_zero_iff.mpr (Units.ne_zero u)
    · exact norm_ne_zero_iff.mpr (Units.ne_zero v)

theorem completionValueDegree_apply (u : CompletionValueCarrier place) :
    completionValueDegree place u =
      Multiplicative.ofAdd (Real.log ‖(u : CommonPrimeCompletion place)‖) := rfl

/-- The actual completion-valued source geometry over a supplied family of
places.  No abstract value monoid remains: value data are actual units of the
actual completions, and the completion map is their coercion. -/
structure CompletionValuedSourceGeometry {l : PrimeGeFive} (V : Type uv) where
  /-- The actual local completion place at each source place. -/
  place : V → FinitePlaceAtPrime K p
  /-- Actual q unit in each local completion. -/
  qUnit : (v : V) → CompletionValueCarrier (place v)
  /-- Actual finite theta packet. -/
  thetaPacket : FiniteThetaPacket l
  /-- The theta packet q is the actual norm of the q unit. -/
  thetaPacket_q_eq : ∀ v : V,
    thetaPacket.q = ‖(qUnit v : CommonPrimeCompletion (place v))‖

namespace CompletionValuedSourceGeometry

variable {V : Type uv} (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

abbrev valueCarrier (v : V) : Type u :=
  CompletionValueCarrier (G.place v)

def valueToCompletion (v : V) :
    valueCarrier G v →* CommonPrimeCompletion (G.place v) :=
  completionValueToCompletion (G.place v)

def valueDegree (v : V) :
    valueCarrier G v →* Multiplicative Real :=
  completionValueDegree (G.place v)

theorem valueToCompletion_injective (v : V) :
    Function.Injective (valueToCompletion G v) :=
  completionValueToCompletion_injective (G.place v)

theorem valueToCompletion_ne_zero (v : V) (x : valueCarrier G v) :
    valueToCompletion G v x ≠ 0 :=
  completionValueToCompletion_ne_zero (G.place v) x

end CompletionValuedSourceGeometry

end LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual

end
