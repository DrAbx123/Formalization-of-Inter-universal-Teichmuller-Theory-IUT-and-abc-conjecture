import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.IsSepClosed

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Alignment of the closed source q_v with the canonical q-series Tate parameter

Scratch.  Uses the closed source q_v theorem (production module
`LeanFormal/IUT/Foundations/NumberField/SourceQvClosed.lean`) and aligns its
parameter q with the canonical q-series Tate curve
`TateCurve.weierstrassCurve K q`, recording the exact coordinate-change
normalization over the algebraic closure: the variable change C has
`C • E_local = Tate(q)`, and its unit u normalizes Delta/c4/c6 by the twelfth/
fourth/sixth powers.  No upper Theta, no card.
-/

noncomputable section

namespace LeanFormal.IUT.SourceTateParameterAlignment

open LeanFormal.IUT
open LeanFormal.IUT.SourceQvClosed
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F]

local instance instAlgebraSourceField (v : NumberField.FinitePlace F) :
    Algebra F (NormalizedCompletion v) :=
  inferInstanceAs (Algebra F (Completion v))

/-- `Valued.v q < 1` on the normalized completion is equivalent to the
normalized norm being `< 1`. -/
theorem normalized_valued_lt_one_iff_norm_lt_one
    (v : NumberField.FinitePlace F) (q : NormalizedCompletion v) :
    (Valued.v (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionRingEquiv v q) :
        WithZero (Multiplicative ℤ)) < 1 ↔ ‖q‖ < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff]
  exact (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_norm_lt_one_iff v q)

/-- The canonical q-series Tate curve attached to the source parameter. -/
abbrev canonicalTateCurve (v : NumberField.FinitePlace F)
    (q : NormalizedCompletion v) : WeierstrassCurve (NormalizedCompletion v) :=
  TateCurve.weierstrassCurve (NormalizedCompletion v) q

/-- Alignment data: the closed source q_v together with the canonical q-series
Tate curve and the exact normalized variable change over the algebraic closure. -/
structure AlignedSourceTateParameter (v : NumberField.FinitePlace F)
    (X : PuncturedEllipticCurve F) where
  q : NormalizedCompletion v
  q_ne_zero : q ≠ 0
  q_norm_lt_one : ‖q‖ < 1
  valued_lt_one :
    (Valued.v (LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionRingEquiv v q) :
      WithZero (Multiplicative ℤ)) < 1
  canonical_is_elliptic : (canonicalTateCurve v q).IsElliptic
  local_is_elliptic : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic
  local_j_eq_canonical :
    letI : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic := local_is_elliptic
    letI : (canonicalTateCurve v q).IsElliptic := canonical_is_elliptic
    (X.baseChange (NormalizedCompletion v)).curve.j = (canonicalTateCurve v q).j
  C : WeierstrassCurve.VariableChange (AlgebraicClosure (NormalizedCompletion v))
  coordinateChange :
    C • ((X.baseChange (NormalizedCompletion v)).curve.map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))) =
      (canonicalTateCurve v q).map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))
  delta_normalization :
    ((canonicalTateCurve v q).map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).Δ =
      C.u⁻¹ ^ 12 *
        (((X.baseChange (NormalizedCompletion v)).curve.map
          (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).Δ)
  c4_normalization :
    ((canonicalTateCurve v q).map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).c₄ =
      C.u⁻¹ ^ 4 *
        (((X.baseChange (NormalizedCompletion v)).curve.map
          (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).c₄)
  c6_normalization :
    ((canonicalTateCurve v q).map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).c₆ =
      C.u⁻¹ ^ 6 *
        (((X.baseChange (NormalizedCompletion v)).curve.map
          (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))).c₆)

/-- **Alignment theorem.**  The closed source q_v can be aligned with the
canonical q-series Tate parameter, with the exact coordinate-change normalization
over the algebraic closure. -/
theorem exists_alignedSourceTateParameter
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    Nonempty (AlignedSourceTateParameter v X) := by
  obtain ⟨qv⟩ := exists_sourceQv_at_finitePlace_closed v X hsplit
  let E : WeierstrassCurve (NormalizedCompletion v) :=
    (X.baseChange (NormalizedCompletion v)).curve
  have hE : E.IsElliptic := (X.baseChange (NormalizedCompletion v)).isElliptic
  let T : WeierstrassCurve (NormalizedCompletion v) := canonicalTateCurve v qv.q
  have hT : T.IsElliptic := qv.canonical_is_elliptic
  have hqj :
      (X.baseChange (NormalizedCompletion v)).curve.j =
        (canonicalTateCurve v qv.q).j := by
    letI : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic :=
      (X.baseChange (NormalizedCompletion v)).isElliptic
    letI : (TateCurve.weierstrassCurve (NormalizedCompletion v) qv.q).IsElliptic :=
      qv.canonical_is_elliptic
    exact qv.j_eq
  let Kbar : Type u := AlgebraicClosure (NormalizedCompletion v)
  let f : NormalizedCompletion v →+* Kbar := algebraMap _ _
  let Ebar : WeierstrassCurve Kbar := E.map f
  let Tbar : WeierstrassCurve Kbar := T.map f
  letI : E.IsElliptic := hE
  letI : T.IsElliptic := hT
  letI : Ebar.IsElliptic := inferInstance
  letI : Tbar.IsElliptic := inferInstance
  letI : IsSepClosed Kbar := inferInstance
  have hqj' : E.j = T.j := by
    simpa [E, T, canonicalTateCurve] using hqj
  have heq : Ebar.j = Tbar.j := by
    change (E.map f).j = (T.map f).j
    rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j]
    exact congrArg f hqj'
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (E := Ebar) (E' := Tbar) heq
  have hDelta : Tbar.Δ = C.u⁻¹ ^ 12 * Ebar.Δ := by
    have h := WeierstrassCurve.variableChange_Δ C (W := Ebar)
    rw [hC] at h
    exact h
  have hc4 : Tbar.c₄ = C.u⁻¹ ^ 4 * Ebar.c₄ := by
    have h := WeierstrassCurve.variableChange_c₄ C (W := Ebar)
    rw [hC] at h
    exact h
  have hc6 : Tbar.c₆ = C.u⁻¹ ^ 6 * Ebar.c₆ := by
    have h := WeierstrassCurve.variableChange_c₆ C (W := Ebar)
    rw [hC] at h
    exact h
  refine ⟨{
    q := qv.q
    q_ne_zero := qv.q_ne_zero
    q_norm_lt_one := qv.q_norm_lt_one
    valued_lt_one := (normalized_valued_lt_one_iff_norm_lt_one v qv.q).mpr qv.q_norm_lt_one
    canonical_is_elliptic := hT
    local_is_elliptic := hE
    local_j_eq_canonical := hqj
    C := C
    coordinateChange := hC
    delta_normalization := hDelta
    c4_normalization := hc4
    c6_normalization := hc6 }⟩

end LeanFormal.IUT.SourceTateParameterAlignment

end