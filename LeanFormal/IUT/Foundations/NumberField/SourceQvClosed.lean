import LeanFormal.IUT.Foundations.PAdicAnalytic.TateInverseJNo1728
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterBridge
import LeanFormal.IUT.Foundations.NumberField.SourceIntegerNorm
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Ring.CharZero

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Closed source q_v assembly at a finite place

Scratch.  Copies the public `SourceQv` interface and the helper theorem
`exists_sourceQv` from iplsheapt's scratch file `SourceQvFromGeneral.lean`, then
instantiates `exists_sourceQv_at_finitePlace` WITHOUT `hBridge`/`hint`:
* `hint` is the production theorem
  `LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_natCast_norm_le_one`;
* `hBridge` is the production bridge
  `LeanFormal.IUT.SourceTateParameter.norm_j_gt_one_of_splitMultiplicativeReductionAt`
  plus the completion -> normalized large-j transfer proved below
  (`normalizedCompletion_norm_lt_one_iff` on inverses, j != 0).
No upper Theta, no card.
-/

noncomputable section

namespace LeanFormal.IUT.SourceQvClosed

open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-! ## Copied public interface from iplsheapt's scratch -/

/-- Source q_v witness. -/
structure SourceQv (E : WeierstrassCurve K) (hE : E.IsElliptic) where
  q : K
  q_ne_zero : q ≠ 0
  q_norm_lt_one : ‖q‖ < 1
  canonical_is_elliptic : (TateCurve.weierstrassCurve K q).IsElliptic
  j_eq :
    letI : E.IsElliptic := hE
    letI : (TateCurve.weierstrassCurve K q).IsElliptic := canonical_is_elliptic
    E.j = (TateCurve.weierstrassCurve K q).j

/-- The canonical q-series H(q) = Delta(q)/c4(q)^3. -/
def qSeriesH (q : K) : K :=
  (TateCurve.weierstrassCurve K q).Δ / (TateCurve.weierstrassCurve K q).c₄ ^ 3

theorem tate_j_eq_inv_qSeriesH (q : K)
    (h : (TateCurve.weierstrassCurve K q).IsElliptic) :
    @WeierstrassCurve.j K _ (TateCurve.weierstrassCurve K q) h = (qSeriesH q)⁻¹ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  unfold qSeriesH
  rw [inv_div, div_eq_inv_mul, mul_comm]

lemma qSeriesH_zero : qSeriesH (K := K) 0 = 0 := by
  unfold qSeriesH
  have hΔ : (TateCurve.weierstrassCurve K 0).Δ = 0 := by
    simp [TateCurve.weierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      TateCurve.a4_zero, TateCurve.a6_zero]
  rw [hΔ, zero_div]

/-- Target A and B from the production no-1728 inverse-j theorem plus large j. -/
theorem exists_sourceQv
    (R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (E : WeierstrassCurve K) (hE : E.IsElliptic)
    (hlarge : 1 < ‖E.j‖) :
    Nonempty (SourceQv E hE) := by
  let t : K := (E.j)⁻¹
  have ht0 : t ≠ 0 := by
    dsimp [t]
    exact inv_ne_zero (norm_pos_iff.mp (lt_trans (by norm_num) hlarge))
  have ht1 : ‖t‖ < 1 := by
    dsimp [t]
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hlarge
  obtain ⟨q, hH, hJ, hq1⟩ :=
    exists_tateHK_eq_and_tateJK_eq_inv_no1728 (K := K) hint ht0 ht1
  have ht_ne : t ≠ 0 := ht0
  have hqH : qSeriesH q = t := by
    simpa [qSeriesH, tateHK] using hH
  have hqHne : qSeriesH q ≠ 0 := by
    rw [hqH]
    exact ht_ne
  have hq0 : q ≠ 0 := by
    intro hqzero
    apply hqHne
    subst q
    exact qSeriesH_zero (K := K)
  have hΔ : (TateCurve.weierstrassCurve K q).Δ ≠ 0 := by
    intro hzero
    apply hqHne
    simp [qSeriesH, hzero]
  have hEll : (TateCurve.weierstrassCurve K q).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  refine ⟨⟨q, hq0, hq1, hEll, ?_⟩⟩
  rw [tate_j_eq_inv_qSeriesH q hEll, hqH]
  dsimp [t]
  rw [inv_inv]

/-! ## Finite-place specialization -/

section FinitePlaceSource

variable {F : Type u} [Field F] [NumberField F]

local instance instAlgebraSourceField (v : NumberField.FinitePlace F) :
    Algebra F (NormalizedCompletion v) :=
  inferInstanceAs (Algebra F (Completion v))

local instance instAlgebraCompletionIntegers (v : NumberField.FinitePlace F) :
    Algebra (CompletionIntegers v) (NormalizedCompletion v) :=
  inferInstanceAs (Algebra (CompletionIntegers v) (Completion v))

local instance instIsFractionRingSourceLocalField (v : NumberField.FinitePlace F) :
    IsFractionRing (CompletionIntegers v) (NormalizedCompletion v) :=
  inferInstanceAs (IsFractionRing (CompletionIntegers v) (Completion v))

/-- Copied from iplsheapt's scratch: exact source q_v assembly with explicit
`hBridge` and `hint`. -/
theorem exists_sourceQv_at_finitePlace
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v)
    (hBridge : 1 < ‖@WeierstrassCurve.j (NormalizedCompletion v) _
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic‖)
    (hint : ∀ n : ℕ, ‖(n : NormalizedCompletion v)‖ ≤ 1) :
    Nonempty (SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic) := by
  let E : WeierstrassCurve (NormalizedCompletion v) :=
    (X.baseChange (NormalizedCompletion v)).curve
  let hE : E.IsElliptic := (X.baseChange (NormalizedCompletion v)).isElliptic
  have hlarge : 1 < ‖@WeierstrassCurve.j (NormalizedCompletion v) _ E hE‖ := hBridge
  exact exists_sourceQv (K := NormalizedCompletion v) (R := CompletionIntegers v)
    hint E hE hlarge

/-- Completion -> normalized large-j transfer: if the completion-norm j-invariant
is `> 1`, then the normalized-norm j-invariant is `> 1`.  Uses
`normalizedCompletion_norm_lt_one_iff` on inverses; `j != 0` follows from
`1 < ||j||` in the completion norm. -/
theorem normalized_large_j_of_completion_large_j
    (v : NumberField.FinitePlace F) (x : Completion v)
    (hx0 : x ≠ 0) (hx : 1 < ‖x‖) :
    1 < ‖(show NormalizedCompletion v from x)‖ := by
  have hinv_comp : ‖x⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hx
  have hinv_normed : ‖(show NormalizedCompletion v from x⁻¹)‖ < 1 := by
    have hcomp' :
        ‖(LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionRingEquiv v
          (show NormalizedCompletion v from x⁻¹) : Completion v)‖ < 1 := by
      rw [show (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionRingEquiv v
            (show NormalizedCompletion v from x⁻¹) : Completion v) = x⁻¹ from rfl]
      exact hinv_comp
    exact (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_norm_lt_one_iff
      (K := F) v (show NormalizedCompletion v from x⁻¹)).mp hcomp'
  have hpos : 0 < ‖(show NormalizedCompletion v from x)‖ :=
    norm_pos_iff.mpr hx0
  have hinvlt : ‖(show NormalizedCompletion v from x)‖⁻¹ < 1 := by
    simpa [norm_inv] using hinv_normed
  rcases (inv_lt_one_iff₀ (a := ‖(show NormalizedCompletion v from x)‖)).mp hinvlt with hle | hone
  · exact absurd hle (not_le_of_gt hpos)
  · exact hone

/-- **Closed source q_v theorem**: no `hBridge`, no `hint`. -/
theorem exists_sourceQv_at_finitePlace_closed
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    Nonempty (SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic) := by
  have hcomp :
      1 < ‖(X.baseChange (Completion v)).jInvariant‖ :=
    LeanFormal.IUT.SourceTateParameter.norm_j_gt_one_of_splitMultiplicativeReductionAt
      X v hsplit
  have hx0 : (X.baseChange (Completion v)).jInvariant ≠ 0 := by
    exact norm_pos_iff.mp (lt_trans (by norm_num) hcomp)
  have hsame :
      (X.baseChange (NormalizedCompletion v)).jInvariant
        = (show NormalizedCompletion v from (X.baseChange (Completion v)).jInvariant) := rfl
  have hBridge :
      1 < ‖@WeierstrassCurve.j (NormalizedCompletion v) _
        (X.baseChange (NormalizedCompletion v)).curve
        (X.baseChange (NormalizedCompletion v)).isElliptic‖ := by
    rw [← PuncturedEllipticCurve.jInvariant_spec
      (X.baseChange (NormalizedCompletion v))]
    rw [hsame]
    exact normalized_large_j_of_completion_large_j v
      (X.baseChange (Completion v)).jInvariant hx0 hcomp
  exact exists_sourceQv_at_finitePlace v X hsplit hBridge
    (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_natCast_norm_le_one v)

end FinitePlaceSource

end LeanFormal.IUT.SourceQvClosed

end