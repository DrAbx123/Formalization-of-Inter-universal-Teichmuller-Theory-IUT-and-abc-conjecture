/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.S1498KSideTateTransportActual
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationBaseChange

/-!
# S1515: the K-side Tate curve realizes the base-changed K-side curve

S1498 defines the actual F-to-K completion map
`s1498CompletionMap = completionMap` and the actual transported coordinate
change `s1498CoordinateChange = C_F.coordinateChange.map s1498CompletionMap`,
where `C_F` is the clause-(b) Tate comparison at the source-designated F-place.
The remaining first transport field is `S1498RealizesCurveTarget`:

```
s1498CoordinateChange • TateCurve.weierstrassCurve (Completion (sectionKPlace T b))
    (sectionQ T b).q
  = ((kSideCurve T).baseChange (Completion (sectionKPlace T b))).curve .
```

This file proves exactly that equality, with no extra hypothesis and no
ambient/proxy comparison.  The proof is the transport of the actual F-side
curve realization along the actual completion map:

* apply `WeierstrassCurve.map (fHom T b)` to the F-side equality
  `C_F.realizesCurve`;
* rewrite the left side by `WeierstrassCurve.map_variableChange`;
* rewrite the canonical q-series curve by `TateCurve.weierstrassCurve_map`
  (whose continuity and norm hypotheses are the actual
  `continuous_completionMap` and `FinitePlaceQCandidate.valuation_lt_one`);
* rewrite the right side by `baseChange_curve_map_eq`, which identifies the two
  ways of extending the coefficient field `F -> K -> K_v` (the equality of the
  two composites uses `completionMap_coe` and the scalar tower
  `F -> K -> Completion (sectionKPlace T b)`).

The same transport also proves `canonicalIsElliptic` for the K-side canonical
curve.  Consequently the remaining field of `S1498RemainingTransport` is
exactly the Tate point comparison `points`; this is recorded in
`s1498RemainingTransport_iff_points`.  No `TatePointComparison` is constructed
or assumed here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open scoped Valued

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual

namespace LeanFormal.IUT.XiFPaper.S1515KSideTateRealizesCurveActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual completion map and its coefficient-field compatibility -/

/-- The actual completion map from the F-place completion to the designated
K-place completion.  This is definitionally `s1498CompletionMap`. -/
abbrev Fv (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :=
  Completion (sectionFPlace T b)

/-- The designated K-place completion. -/
abbrev Kv (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :=
  Completion (sectionKPlace T b)

/-- The actual completion map, written without the S1498 abbreviation. -/
abbrev fHom (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Fv T b →+* Kv T b :=
  completionMap (k := T.arithmetic.F) (sectionKPlace T b)

/-- The S1498 completion map is the actual place-extension completion map. -/
theorem fHom_eq_s1498CompletionMap :
    fHom T b = s1498CompletionMap (T := T) (b := b) := rfl

/-- Continuity of the actual completion map. -/
theorem fHom_continuous : Continuous (fHom T b) :=
  continuous_completionMap (k := T.arithmetic.F) (sectionKPlace T b)

/-- The source q-parameter is a strict contraction for the completion norm. -/
theorem qF_norm_lt_one : ‖(sectionFQ T b).q‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact (sectionFQ T b).valuation_lt_one

/-- On the dense image of `F`, the actual completion map is the algebra map. -/
theorem completionMap_algebraMap_eq (x : T.arithmetic.F) :
    fHom T b (algebraMap T.arithmetic.F (Fv T b) x) =
      algebraMap T.arithmetic.F (Kv T b) x := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact completionMap_coe (k := T.arithmetic.F) (sectionKPlace T b) x

/-- The two composites `F -> F_v -> K_v` and `F -> K -> K_v` agree as ring
homomorphisms. -/
theorem ringHom_comp_eq :
    (fHom T b).comp (algebraMap T.arithmetic.F (Fv T b)) =
      (algebraMap T.arithmetic.K (Kv T b)).comp
        (algebraMap T.arithmetic.F T.arithmetic.K) := by
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [completionMap_algebraMap_eq T b x]
  exact (congrArg (fun z : Kv T b => z.toCompletion)
    (IsScalarTower.algebraMap_apply T.arithmetic.F T.arithmetic.K
      (Kv T b) x)).symm

/-! ## 2. The two base-change layers -/

/-- The canonical q-series curve base changes along the actual completion map
to the K-side Tate curve at the completionMap image of `sectionFQ`. -/
theorem tateCurve_map_eq :
    (TateCurve.weierstrassCurve (Fv T b) (sectionFQ T b).q).map (fHom T b) =
      TateCurve.weierstrassCurve (Kv T b) (sectionQ T b).q := by
  rw [sectionQ_q (T := T) (b := b)]
  exact TateCurve.weierstrassCurve_map (fHom T b)
    (fHom_continuous T b) (qF_norm_lt_one T b)

/-- Base-changing the F-side arithmetic curve through the completion of `F`
and then through the actual completion map is the same as base-changing along
`F -> K` and then to the designated K-place completion. -/
theorem baseChange_curve_map_eq :
    ((T.arithmetic.curve.baseChange (Fv T b)).curve).map (fHom T b) =
      ((kSideCurve (T := T)).baseChange (Kv T b)).curve := by
  simp only [PuncturedEllipticCurve.baseChange_curve, kSideCurve,
    WeierstrassCurve.baseChange]
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  rw [ringHom_comp_eq T b]

/-! ## 3. The realizesCurve equality -/

/-- The exact S1498 realizesCurve target: the actual transported
coordinate change sends the K-side canonical Tate curve to the K-side
base-changed curve. -/
theorem s1498RealizesCurveTarget :
    S1498RealizesCurveTarget (T := T) (b := b) := by
  let C := sectionTateWitness_comparison T b
  have hmap := congrArg
    (fun W : WeierstrassCurve (Fv T b) => W.map (fHom T b)) C.realizesCurve
  rw [← WeierstrassCurve.map_variableChange] at hmap
  rw [tateCurve_map_eq T b, baseChange_curve_map_eq T b] at hmap
  simpa [S1498RealizesCurveTarget, s1498CoordinateChange, s1498CompletionMap,
    C, fHom] using hmap

/-- The named first missing transport field of S1498 is now supplied. -/
theorem s1498FirstMissingTransport :
    S1498FirstMissingTransport (T := T) (b := b) :=
  s1498RealizesCurveTarget T b

/-- The canonical K-side q-series curve is elliptic, transported from the
F-side clause-(b) comparison. -/
theorem canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Kv T b) (sectionQ T b).q).IsElliptic := by
  let C := sectionTateWitness_comparison T b
  haveI : (TateCurve.weierstrassCurve (Fv T b) (sectionFQ T b).q).IsElliptic :=
    C.canonicalIsElliptic
  rw [← tateCurve_map_eq T b]
  exact inferInstanceAs
    ((TateCurve.weierstrassCurve (Fv T b) (sectionFQ T b).q).map
      (fHom T b)).IsElliptic

/-! ## 4. The exact remaining transport field -/

/-- After the two algebraic fields are supplied, the remaining content of
`S1498RemainingTransport` is exactly the Tate point comparison.  This is a
precise statement of what is still missing; no point comparison is constructed. -/
theorem s1498RemainingTransport_iff_points :
    Nonempty (S1498RemainingTransport (T := T) (b := b)) ↔
      Nonempty (TatePointComparison (kSideCurve (T := T))
        (sectionKPlace T b) (sectionQ T b)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.points⟩
  · rintro ⟨points⟩
    exact ⟨{ canonicalIsElliptic := canonicalIsElliptic T b
             realizesCurve := s1498RealizesCurveTarget T b
             points := points }⟩

end LeanFormal.IUT.XiFPaper.S1515KSideTateRealizesCurveActual
end
