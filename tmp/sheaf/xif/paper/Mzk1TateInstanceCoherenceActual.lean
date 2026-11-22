/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TateComparisonBridgeActual
import tmp.sheaf.xif.paper.Mzk1NormValDictionaryActual
import Mathlib.Tactic

/-! # Mzk1TateInstanceCoherenceActual — instance-coherent Tate bridge (A812, qpilot)

The bridge theorems in `Mzk1TateComparisonBridgeActual` were stated with
`[NontriviallyNormedField K]`, while the finite-place completion carries Mathlib's
noncomputable `NormedField` instance and no `NontriviallyNormedField` instance.

Fix: restate the bridge with the *single* `[NormedField K]` instance (plus
`[IsUltrametricDist K] [CompleteSpace K] [CharZero K]` where needed).  Summability of
the unshifted Lambert series is derived from the vendor's shifted summability via
`summable_nat_add_iff`, so no `NontriviallyNormedField` is used.

Then the bridge applies to the completion with the same NormedField instance used by
`tateParameterOfQCandidate`, unblocking the candidate chain; a `CharZero` instance for
the completion is proved from injectivity of the algebra map.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateInstanceCoherenceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1NormValDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1TateComparisonBridgeActual

universe u

/-! ### 1. Instance-coherent bridge (single NormedField instance) -/

section Coherent

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem eisenstein_eq_lambertSeries' (t : TateCurvesTheta.TateParameter K) (k : Nat)
    (hk : 0 < k) :
    t.eisenstein k = TateCurve.lambertSeries K k (t.q : K) := by
  have hshift : Summable (fun n : Nat =>
      ((n + 1 : Nat) : K) ^ k * (t.q : K) ^ (n + 1) /
        (1 - (t.q : K) ^ (n + 1))) := t.eisenstein_summand_summable k
  have hsum : Summable (fun n : Nat =>
      ((n : K) ^ k * (t.q : K) ^ n / (1 - (t.q : K) ^ n))) := by
    have hs : Summable (fun n : Nat =>
        ((n + 1 : Nat) : K) ^ k * (t.q : K) ^ (n + 1) /
          (1 - (t.q : K) ^ (n + 1))) := hshift
    simpa using (summable_nat_add_iff (f := fun n : Nat =>
      ((n : K) ^ k * (t.q : K) ^ n / (1 - (t.q : K) ^ n))) 1).mp (by
      simpa using hs)
  have h0 : ((0 : Nat) : K) ^ k * (t.q : K) ^ (0 : Nat) /
      (1 - (t.q : K) ^ (0 : Nat)) = 0 := by
    rw [Nat.cast_zero, zero_pow hk.ne', zero_mul, zero_div]
  have h := hsum.tsum_eq_zero_add
  rw [h0, zero_add] at h
  unfold TateCurvesTheta.TateParameter.eisenstein TateCurve.lambertSeries
  exact h.symm

theorem tateA4_eq' [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.a₄ = TateCurve.a4 K (t.q : K) := by
  unfold TateCurvesTheta.TateParameter.a₄ TateCurve.a4
  rw [eisenstein_eq_lambertSeries' t 3 (by norm_num)]

theorem tateA6_eq' [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.a₆ = TateCurve.a6 K (t.q : K) := by
  unfold TateCurvesTheta.TateParameter.a₆ TateCurve.a6
  rw [eisenstein_eq_lambertSeries' t 3 (by norm_num),
    eisenstein_eq_lambertSeries' t 5 (by norm_num)]

theorem tateCurve_eq' [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.tateCurve = TateCurve.weierstrassCurve K (t.q : K) := by
  ext <;>
    simp [TateCurvesTheta.TateParameter.tateCurve,
      TateCurve.weierstrassCurve, tateA4_eq', tateA6_eq']

theorem leanformalTateCurve_isElliptic' [CharZero K]
    (t : TateCurvesTheta.TateParameter K) :
    (TateCurve.weierstrassCurve K (t.q : K)).IsElliptic := by
  rw [← tateCurve_eq' t]
  exact t.tateCurve_isElliptic (by norm_num)

end Coherent

/-! ### 2. CharZero instance on the completion -/

variable {F : Type u} [Field F] [NumberField F]

/-- The completion of a number field has characteristic zero. -/
instance completionCharZero (place : NumberField.FinitePlace F) :
    CharZero (Completion place) where
  cast_injective := by
    intro m n h
    have h' : (m : F) = (n : F) := by
      apply (algebraMap F (Completion place)).injective
      simpa only [map_natCast] using h
    exact Nat.cast_injective h'

/-! ### 3. Application to a q-candidate -/

variable (place : NumberField.FinitePlace F)
variable [IsUltrametricDist (Completion place)] [CompleteSpace (Completion place)]

/-- The candidate's vendor Tate curve is the LeanFormal canonical Tate curve, with the
same completion instances on both sides (instance-coherent form). -/
theorem tateParameterOfQCandidate_curve_eq' (parameter : FinitePlaceQCandidate place) :
    (tateParameterOfQCandidate place parameter).tateCurve =
      TateCurve.weierstrassCurve (Completion place) parameter.q := by
  rw [tateCurve_eq' (tateParameterOfQCandidate place parameter)]
  rw [tateParameterOfQCandidate_coe]

/-- The canonical Tate curve at a candidate's `q` is elliptic (instance-coherent form). -/
theorem tateParameterOfQCandidate_canonical_isElliptic'
    (parameter : FinitePlaceQCandidate place) :
    (TateCurve.weierstrassCurve (Completion place) parameter.q).IsElliptic := by
  exact leanformalTateCurve_isElliptic' (tateParameterOfQCandidate place parameter)

/-! ### 4. Rows -/

def coherenceRows : List (String × String) :=
  [ ("coherent eisenstein bridge (single NormedField instance)", "PROVED"),
    ("coherent degree-3/5 coefficient bridge", "PROVED"),
    ("coherent curve equality", "PROVED"),
    ("coherent ellipticity transfer", "PROVED"),
    ("CharZero instance on the completed number field", "PROVED"),
    ("candidate curve = LeanFormal canonical curve (completion instances)", "PROVED"),
    ("candidate canonical curve elliptic", "PROVED") ]

theorem coherenceRows_length : coherenceRows.length = 7 := rfl

#check tateCurve_eq'
#check completionCharZero
#check tateParameterOfQCandidate_curve_eq'
#check coherenceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateInstanceCoherenceActual
end
