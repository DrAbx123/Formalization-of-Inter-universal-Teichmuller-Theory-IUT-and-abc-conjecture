/-
  # P-adic analytic local inverses

  Task-132 foundation: specialize Mathlib's analytic inverse function theorem
  (AnalyticAt.analyticAt_localInverse) to complete nontrivially normed fields,
  in particular to the p-adic fields Q_p.  The theorem is an actual consequence
  of Mathlib's analytic local inverse theorem; no new analytic input is assumed.

  Also records the exact missing analytic input for the Tate q-series j-function
  at q = 5: analyticity of the Lambert-series j(q) at q = 5 and nonvanishing of
  its derivative there.  Those are NOT proved by this file; the local inverse
  construction in TateQSeriesAnalytic is conditional on them.
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.NumberTheory.Padics.PadicNumbers

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.PAdicAnalytic

open AnalyticAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]

/-- The local inverse of a complete nontrivially normed field analytic function
at a point with nonzero derivative is analytic at the image point. -/
theorem analyticAt_localInverse
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x) :=
  hf.analyticAt_localInverse hf'

/-- The p-adic specialization: for a prime p, the local inverse of an analytic
function Q_p -> Q_p at a point with nonzero derivative is analytic. -/
theorem padic_analyticAt_localInverse
    (p : ℕ) [Fact (Nat.Prime p)]
    {f : ℚ_[p] → ℚ_[p]} {x : ℚ_[p]}
    (hf : AnalyticAt ℚ_[p] f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt ℚ_[p]
      (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x) :=
  analyticAt_localInverse (𝕜 := ℚ_[p]) hf hf'

/-- Ball form: the analytic local inverse exists on some open neighborhood of
the image point.  This restates the local nature of the theorem; no global
inverse is claimed. -/
theorem exists_analytic_localInverse_ball
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g (f x) :=
  ⟨hf.hasStrictDerivAt.localInverse _ _ _ hf',
    hf.analyticAt_localInverse hf'⟩

local instance fivePrimeFactALI : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The exact missing analytic input for the Tate q-series j-function: at
q = 5 in Q_5, the Lambert-series j(q) is analytic and its derivative is
nonzero.  This is a Prop interface; no inhabitant is constructed here. -/
def TateJAnalyticAtFive (tateJ : ℚ_[5] → ℚ_[5]) : Prop :=
  AnalyticAt ℚ_[5] tateJ 5 ∧ deriv tateJ 5 ≠ 0


/-- The concrete analytic local inverse from Mathlib's HasStrictDerivAt.localInverse. -/
noncomputable def analyticLocalInverse
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) : 𝕜 → 𝕜 :=
  hf.hasStrictDerivAt.localInverse f (deriv f x) x hf'

/-- The analytic local inverse is analytic at the image point. -/
theorem analyticLocalInverse_analytic
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (analyticLocalInverse hf hf') (f x) :=
  hf.analyticAt_localInverse hf'

/-- The analytic local inverse is a strict derivative inverse at the image. -/
theorem analyticLocalInverse_hasStrictDerivAt
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    HasStrictDerivAt (analyticLocalInverse hf hf') ((deriv f x)⁻¹) (f x) :=
  hf.hasStrictDerivAt.to_localInverse hf'

/-- Eventual left-inverse property near the source point. -/
theorem analyticLocalInverse_eventually_left
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    ∀ᶠ y in nhds x, analyticLocalInverse hf hf' (f y) = y :=
  hf.hasStrictDerivAt.eventually_left_inverse hf'

/-- Eventual right-inverse property near the image point. -/
theorem analyticLocalInverse_eventually_right
    {f : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    ∀ᶠ y in nhds (f x), f (analyticLocalInverse hf hf' y) = y :=
  hf.hasStrictDerivAt.eventually_right_inverse hf'


end LeanFormal.IUT.PAdicAnalytic
