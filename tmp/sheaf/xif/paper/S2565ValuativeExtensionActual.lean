import tmp.sheaf.xif.paper.S2564TauCetiInstanceSkeletonActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.S2564TauCetiInstanceSkeletonActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S2565ValuativeExtensionActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev e : ℕ :=
  (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.asIdeal.ramificationIdx'
    (nativeFPlaceOverBad X).maximalIdeal.asIdeal

@[implicit_reducible]
noncomputable def S2565ValuativeExtensionOfPos
    (he : 0 < e X) :
    letI := relativeCompletionAlgebra (X := X)
    ValuativeExtension (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := by
  letI A : Algebra (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := relativeCompletionAlgebra (X := X)
  refine { vle_iff_vle := ?_ }
  intro a b
  change (Valued.v (algebraMap (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) a) : WithZero (Multiplicative Int)) ≤
      Valued.v (algebraMap (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) b) ↔
    (Valued.v a : WithZero (Multiplicative Int)) ≤ Valued.v b
  change Valued.v (completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a) ≤
      Valued.v (completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) b) ↔
    Valued.v a ≤ Valued.v b
  rw [← valuation_completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a,
    ← valuation_completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) b]
  have ha : (0 : WithZero (Multiplicative Int)) ≤ Valued.v a := zero_le
  have hb : (0 : WithZero (Multiplicative Int)) ≤ Valued.v b := zero_le
  exact pow_le_pow_iff_left₀ ha hb he.ne'

theorem S2565_ramificationIdx_pos : 0 < e X := by
  unfold e
  have hp : (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.asIdeal ≠ ⊥ :=
    (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.ne_bot
  have hlies :
      (nativeFPlaceOverBad X).maximalIdeal.asIdeal.LiesOver
        (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.asIdeal :=
    inferInstance
  exact Nat.pos_iff_ne_zero.mpr
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      (nativeFPlaceOverBad X).maximalIdeal.asIdeal hp)

attribute [instance] relativeCompletionAlgebra

noncomputable instance S2565ValuativeExtension :
    ValuativeExtension (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) :=
  S2565ValuativeExtensionOfPos X (S2565_ramificationIdx_pos X)

#check S2565ValuativeExtension
#check S2565_ramificationIdx_pos
#check S2565ValuativeExtensionOfPos
#print axioms S2565ValuativeExtensionOfPos
#print axioms S2565ValuativeExtension
end LeanFormal.IUT.XiFPaper.S2565ValuativeExtensionActual
end