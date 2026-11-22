/- 共享 localOrderAt（kurt J1-M / ord tower）: 理想层 order。
  localOrderAt v I := (normalizedFactors I).count v.maximalIdeal.asIdeal。
  对 x∈𝓞K 用 localOrderAt v (Ideal.span {x}) 即 ord_v(x)。
  乘性/幂性见 Mzk1ULOrdTowerActual。 -/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalOrderActual

open NumberField
open UniqueFactorizationMonoid

noncomputable def localOrderAt {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (I : Ideal (𝓞 K)) : ℕ :=
  (normalizedFactors I).count (v.maximalIdeal.asIdeal)

theorem localOrderAt_def {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (I : Ideal (𝓞 K)) :
    localOrderAt v I = (normalizedFactors I).count (v.maximalIdeal.asIdeal) := rfl

theorem localOrderAt_nonneg {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (I : Ideal (𝓞 K)) : 0 ≤ localOrderAt v I :=
  Nat.zero_le _

theorem localOrderAt_span {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) (x : 𝓞 K) :
    localOrderAt v (Ideal.span {x}) = (normalizedFactors (Ideal.span {x})).count
      (v.maximalIdeal.asIdeal) := rfl

#print axioms localOrderAt_def
#print axioms localOrderAt_nonneg
#print axioms localOrderAt_span

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalOrderActual