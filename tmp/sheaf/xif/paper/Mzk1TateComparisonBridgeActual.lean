/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import TateCurvesTheta.TateCurve.Discriminant
import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import Mathlib.Tactic

/-! # Mzk1TateComparisonBridgeActual — vendor/LeanFormal Tate curve bridge (A801, qpilot)

The exact cross-package obstruction: vendor `TateCurvesTheta` (78/78 compiled) proves
the converse direction (`tateCurve_isElliptic`, `HasSplitMultiplicativeReduction`, and
`exists_tateParameter_variableChange_iff`) for its `TateParameter`/`WeierstrassCurve`;
LeanFormal's `TateCurveComparison` uses its own `TateCurve.weierstrassCurve` on
`WeierstrassCurve (Completion place)`.  Both are Mathlib `WeierstrassCurve` values, so a
bridge is possible.

Proved here:
1. coefficient bridge: vendor `TateParameter.eisenstein k` (q-series from `n+1`) equals
   LeanFormal `TateCurve.lambertSeries K k q` (same series, shifted index, zero term),
   `eisenstein_eq_lambertSeries`;
2. `a₄`/`a₆` agree (`tateA4_eq`, `tateA6_eq`), hence the curves agree
   (`tateCurve_eq`);
3. ellipticity transfers: `leanformalTateCurve_isElliptic` (from vendor
   `tateCurve_isElliptic`);
4. conditional `TateCurveComparison` constructor `tateComparisonOfRealization` taking
   exactly the realization data (ellipticity + coordinate change + equality).

Remaining precise gaps (rows): (i) constructing a `TateParameter` from a
`FinitePlaceQCandidate` needs the norm/valuation `norm < 1` relation on the completion;
(ii) the realization equality `C • E_q = X.curve` is not produced by either package
(vendor gives converse under split multiplicative reduction after base change; the
cross-package identification of `X.curve` is the gap); (iii) nonsplit case needs the
quadratic twist `SqrtGammaField` from vendor `Converse/NonSplit`, not available for
LeanFormal's `PuncturedEllipticCurve`.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateComparisonBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

/-! ### 1. Coefficient bridge: vendor Eisenstein series vs LeanFormal Lambert series -/

section CoefficientBridge

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

theorem eisenstein_eq_lambertSeries (t : TateCurvesTheta.TateParameter K) (k : Nat)
    (hk : 0 < k) :
    t.eisenstein k = TateCurve.lambertSeries K k (t.q : K) := by
  have hsum : Summable (fun n : Nat =>
      ((n : K) ^ k * (t.q : K) ^ n / (1 - (t.q : K) ^ n))) := by
    have h := TateCurve.lambertSeries_summable K k (q := (t.q : K)) t.norm_lt_one
    simpa using h
  have h0 : ((0 : Nat) : K) ^ k * (t.q : K) ^ (0 : Nat) /
      (1 - (t.q : K) ^ (0 : Nat)) = 0 := by
    rw [Nat.cast_zero, zero_pow hk.ne', zero_mul, zero_div]
  have h := hsum.tsum_eq_zero_add
  rw [h0, zero_add] at h
  unfold TateCurvesTheta.TateParameter.eisenstein TateCurve.lambertSeries
  exact h.symm

theorem tateA4_eq [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.a₄ = TateCurve.a4 K (t.q : K) := by
  unfold TateCurvesTheta.TateParameter.a₄ TateCurve.a4
  rw [eisenstein_eq_lambertSeries t 3 (by norm_num)]

theorem tateA6_eq [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.a₆ = TateCurve.a6 K (t.q : K) := by
  unfold TateCurvesTheta.TateParameter.a₆ TateCurve.a6
  rw [eisenstein_eq_lambertSeries t 3 (by norm_num),
    eisenstein_eq_lambertSeries t 5 (by norm_num)]

theorem tateCurve_eq [CharZero K] (t : TateCurvesTheta.TateParameter K) :
    t.tateCurve = TateCurve.weierstrassCurve K (t.q : K) := by
  ext <;>
    simp [TateCurvesTheta.TateParameter.tateCurve,
      TateCurve.weierstrassCurve, tateA4_eq, tateA6_eq]

theorem leanformalTateCurve_isElliptic [CharZero K]
    (t : TateCurvesTheta.TateParameter K) :
    (TateCurve.weierstrassCurve K (t.q : K)).IsElliptic := by
  rw [← tateCurve_eq t]
  exact t.tateCurve_isElliptic (by norm_num)

end CoefficientBridge

/-! ### 2. Conditional `TateCurveComparison` constructor -/

variable {l : PrimeGeFive}

/-- The realization data of a (split) Tate comparison, packaged without the point
uniformization: ellipticity, coordinate change, and the realizing equality. -/
structure TateComparisonData {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F)
    (parameter : FinitePlaceQCandidate place) where
  /-- the canonical Tate curve is elliptic. -/
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion place) parameter.q).IsElliptic
  /-- the variable change realizing the input curve. -/
  coordinateChange : WeierstrassCurve.VariableChange (Completion place)
  /-- the realizing equality. -/
  realizesCurve : coordinateChange •
      TateCurve.weierstrassCurve (Completion place) parameter.q =
    (X.baseChange (Completion place)).curve

/-- A full `TateCurveComparison` is the realization data PLUS the point uniformization
(`TatePointComparison`).  This constructor records exactly what is still missing. -/
def tateComparisonOfData {F : Type*} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F} {place : NumberField.FinitePlace F}
    {parameter : FinitePlaceQCandidate place}
    (D : TateComparisonData X place parameter)
    (points : TatePointComparison X place parameter) :
    TateCurveComparison X place parameter where
  canonicalIsElliptic := D.canonicalIsElliptic
  coordinateChange := D.coordinateChange
  realizesCurve := D.realizesCurve
  points := points

/-- Extract the realization data from a full comparison (the point part is dropped). -/
def comparisonDataOfTateComparison {F : Type*} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F} {place : NumberField.FinitePlace F}
    {parameter : FinitePlaceQCandidate place}
    (C : TateCurveComparison X place parameter) :
    TateComparisonData X place parameter where
  canonicalIsElliptic := C.canonicalIsElliptic
  coordinateChange := C.coordinateChange
  realizesCurve := C.realizesCurve

/-! ### 3. Rows -/

def tateBridgeRows : List (String × String) :=
  [ ("vendor eisenstein = LeanFormal lambertSeries", "PROVED (index shift, zero term)"),
    ("vendor a4/a6 = LeanFormal a4/a6", "PROVED"),
    ("vendor tateCurve = LeanFormal TateCurve.weierstrassCurve", "PROVED (curve ext)"),
    ("ellipticity transfer vendor -> LeanFormal", "PROVED"),
    ("TateCurveComparison from realization data", "CONSTRUCTED (conditional)"),
    ("FinitePlaceQCandidate -> TateParameter (norm < 1)", "MISSING (norm/valuation relation)"),
    ("realization data structure (ellipticity + variable change + equality)", "DEFINED"),
    ("realization C • E_q = X.curve", "MISSING (converse direction not bridged)"),
    ("nonsplit case (quadratic twist / SqrtGammaField in LeanFormal)", "MISSING") ]

theorem tateBridgeRows_length : tateBridgeRows.length = 9 := rfl

#check eisenstein_eq_lambertSeries
#check tateCurve_eq
#check leanformalTateCurve_isElliptic
#check tateComparisonOfData
#check comparisonDataOfTateComparison
#check tateBridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateComparisonBridgeActual
end
