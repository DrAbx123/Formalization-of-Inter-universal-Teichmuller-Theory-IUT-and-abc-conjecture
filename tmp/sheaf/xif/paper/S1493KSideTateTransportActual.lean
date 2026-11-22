import tmp.sheaf.xif.paper.S1482KSideTateUniformizationActual
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationBaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # S1493: K-side Tate transport from the F-side comparison

The F-side clause-(b) comparison sectionTateWitness_comparison lives at the
F-place sectionFPlace.  The source-designated K-place sectionKPlace lies over
it, and the K-side q parameter is the actual completionMap image of the F-side
parameter.

This file constructs, unconditionally, the algebraic part of the base-change
transport:

* the canonical Tate curve at the K-place is the base change of the F-side
  canonical Tate curve (tateCurve_map_eq);
* the F-side coordinate change base changes to a K-side coordinate change
  realizing the K-side base-changed curve (baseChange_curve_map_eq, and the
  three fields of S1493CurveTransport);
* the completion extension Completion sectionFPlace ->
  Completion sectionKPlace is algebraic (completion_isAlgebraic), hence the
  two algebraic closures are equivalent over the lower completion
  (sectionClosureEquiv), and this equivalence carries the K-side Tate
  parameter unit to the F-side one
  (sectionClosureEquiv_tateParameterUnit).

What is not constructed is the point-level comparison: the Galois-equivariant
identification of the algebraic-closure point group of the K-side base-changed
curve with the q^Z-quotient at the K-place.  That is the exact points field of
TateCurveComparison, recorded below as S1493KPointTransport.  The construction
of the curve fields does not produce it, and no arbitrary point map is
inserted: the file proves
Nonempty (S1482KSideTateData T b) <-> Nonempty (S1493KPointTransport T b).
-/

noncomputable section
open scoped Valued BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open WeierstrassCurve

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The lower completion, written in the raw adic-completion form used by
completionMap and by the relative-completion algebra instance. -/
abbrev KLowerCompletion (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :=
  (comap (k := T.arithmetic.F) (sectionKPlace T b)).maximalIdeal.adicCompletion T.arithmetic.F

/-- The upper completion, in the same raw form. -/
abbrev KUpperCompletion (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :=
  (sectionKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K

/-- The actual completion embedding on local fields. -/
noncomputable local instance kLowerUpperAlgebra :
    Algebra (KLowerCompletion T b) (KUpperCompletion T b) :=
  (completionMap (k := T.arithmetic.F) (sectionKPlace T b)).toAlgebra

/-- The same algebra structure in the Completion notation used by the target. -/
noncomputable local instance kSectionCompletionAlgebra :
    Algebra (Completion (sectionFPlace T b)) (Completion (sectionKPlace T b)) :=
  inferInstanceAs (Algebra (KLowerCompletion T b) (KUpperCompletion T b))

/-- The completion embedding is a continuous algebra map. -/
local instance kLowerUpperContinuousSMul :
    ContinuousSMul (KLowerCompletion T b) (KUpperCompletion T b) :=
  continuousSMul_of_algebraMap _ _ (by
    rw [show algebraMap (KLowerCompletion T b) (KUpperCompletion T b) =
      completionMap (k := T.arithmetic.F) (sectionKPlace T b) from rfl]
    exact continuous_completionMap (k := T.arithmetic.F) (sectionKPlace T b))

/-! ## The F-side comparison data at the section places -/

/-- The completion map is continuous; this is the actual adic completion
embedding, not an ambient map. -/
theorem completionMap_continuous :
    Continuous (completionMap (k := T.arithmetic.F) (sectionKPlace T b)) :=
  continuous_completionMap (k := T.arithmetic.F) (sectionKPlace T b)

/-- The F-side clause-(b) q parameter is a strict contraction, hence satisfies
the norm hypothesis of the base-change lemmas for the Tate q-series. -/
theorem sectionFQ_norm_lt_one : ‖(sectionFQ T b).q‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact (sectionFQ T b).valuation_lt_one

/-- On the dense base field the completion embedding is the algebra map; this is
the coherence used to identify the two iterated base changes. -/
theorem completionMap_algebraMap_eq (x : T.arithmetic.F) :
    completionMap (k := T.arithmetic.F) (sectionKPlace T b)
        (algebraMap T.arithmetic.F (KLowerCompletion T b) x) =
      algebraMap T.arithmetic.F (KUpperCompletion T b) x := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact completionMap_coe (k := T.arithmetic.F) (sectionKPlace T b) x

/-- The same coherence in the Completion notation. -/
theorem completionMap_algebraMap_eq_completion (x : T.arithmetic.F) :
    completionMap (k := T.arithmetic.F) (sectionKPlace T b)
        (algebraMap T.arithmetic.F (Completion (sectionFPlace T b)) x) =
      algebraMap T.arithmetic.F (Completion (sectionKPlace T b)) x :=
  completionMap_algebraMap_eq T b x

/-- The canonical q-series Tate curve base changes along the actual completion
embedding to the canonical K-side Tate curve at the completed parameter. -/
theorem tateCurve_map_eq :
    (TateCurve.weierstrassCurve (Completion (sectionFPlace T b)) (sectionFQ T b).q).map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b)) =
      TateCurve.weierstrassCurve (Completion (sectionKPlace T b)) (sectionQ T b).q := by
  rw [sectionQ_q (T := T) (b := b)]
  exact TateCurve.weierstrassCurve_map
    (completionMap (k := T.arithmetic.F) (sectionKPlace T b))
    (completionMap_continuous T b) (sectionFQ_norm_lt_one T b)

/-- The composites of the two tower paths agree on coefficients. -/
theorem completionMap_comp_algebraMap_eq_raw :
    (completionMap (k := T.arithmetic.F) (sectionKPlace T b)).comp
        (algebraMap T.arithmetic.F (KLowerCompletion T b)) =
      (algebraMap T.arithmetic.K (KUpperCompletion T b)).comp
        (algebraMap T.arithmetic.F T.arithmetic.K) := by
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [completionMap_algebraMap_eq T b x]
  exact (congrArg (fun z : KUpperCompletion T b => z.toCompletion)
    (IsScalarTower.algebraMap_apply T.arithmetic.F T.arithmetic.K
      (KUpperCompletion T b) x)).symm

/-- The F-side selected curve, base changed to the K-completion, is the K-side
selected curve base changed to its own completion. -/
theorem baseChange_curve_map_eq_raw :
    ((T.arithmetic.curve.baseChange (KLowerCompletion T b)).curve).map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b)) =
      ((kSideCurve (T := T)).baseChange (KUpperCompletion T b)).curve := by
  simp only [PuncturedEllipticCurve.baseChange_curve, kSideCurve,
    WeierstrassCurve.baseChange]
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  rw [completionMap_comp_algebraMap_eq_raw T b]

/-- The curve equality in the Completion notation used by the target. -/
theorem baseChange_curve_map_eq :
    ((T.arithmetic.curve.baseChange (Completion (sectionFPlace T b))).curve).map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b)) =
      ((kSideCurve (T := T)).baseChange (Completion (sectionKPlace T b))).curve :=
  baseChange_curve_map_eq_raw T b

/-! ## The three algebraic fields of the K-side comparison -/

/-- The algebraic fields of S1482KSideTateData, transported from the F-side
clause-(b) comparison. -/
structure S1493CurveTransport where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion (sectionKPlace T b)) (sectionQ T b).q).IsElliptic
  coordinateChange : WeierstrassCurve.VariableChange (Completion (sectionKPlace T b))
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve
        (Completion (sectionKPlace T b)) (sectionQ T b).q =
      ((kSideCurve (T := T)).baseChange (Completion (sectionKPlace T b))).curve

/-- Actual construction of the three algebraic fields from the F-side
comparison. -/
noncomputable def s1493CurveTransport : S1493CurveTransport T b := by
  let C := sectionTateWitness_comparison T b
  haveI : (TateCurve.weierstrassCurve (Completion (sectionFPlace T b))
      (sectionFQ T b).q).IsElliptic := C.canonicalIsElliptic
  refine
    { canonicalIsElliptic := ?_
      coordinateChange := C.coordinateChange.map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b))
      realizesCurve := ?_ }
  · rw [← tateCurve_map_eq T b]
    exact inferInstanceAs ((TateCurve.weierstrassCurve
      (Completion (sectionFPlace T b)) (sectionFQ T b).q).map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b))).IsElliptic
  · have hmap := congrArg
      (fun W : WeierstrassCurve (Completion (sectionFPlace T b)) =>
        W.map (completionMap (k := T.arithmetic.F) (sectionKPlace T b)))
      C.realizesCurve
    rw [← WeierstrassCurve.map_variableChange] at hmap
    rw [tateCurve_map_eq T b, baseChange_curve_map_eq T b] at hmap
    exact hmap

/-! ## Algebraicity of the completion extension -/

/-- The completion extension of a finite-place extension of number fields is
algebraic.  The proof uses that the image of the global finite extension is
dense in the upper completion and that its lower-completion span is a closed,
finite-dimensional subspace; no finiteness of the completed valuation rings is
assumed. -/
theorem completion_isAlgebraic_adic :
    Algebra.IsAlgebraic (KLowerCompletion T b) (KUpperCompletion T b) := by
  classical
  let bK := Module.finBasis T.arithmetic.F T.arithmetic.K
  let V : Submodule (KLowerCompletion T b) (KUpperCompletion T b) :=
    Submodule.span (KLowerCompletion T b)
      (Set.range fun i => algebraMap T.arithmetic.K (KUpperCompletion T b) (bK i))
  have hVfin : FiniteDimensional (KLowerCompletion T b) V :=
    FiniteDimensional.span_of_finite (KLowerCompletion T b) (Set.finite_range _)
  have hVclosed : IsClosed (V : Set (KUpperCompletion T b)) :=
    Submodule.closed_of_finiteDimensional V
  have hmem : forall k : T.arithmetic.K,
      algebraMap T.arithmetic.K (KUpperCompletion T b) k ∈ V := by
    intro k
    have hk : k = ∑ i, bK.repr k i • bK i := (bK.sum_repr k).symm
    have hmap : algebraMap T.arithmetic.K (KUpperCompletion T b) k =
        ∑ i, (algebraMap T.arithmetic.F (KUpperCompletion T b) (bK.repr k i)) *
          algebraMap T.arithmetic.K (KUpperCompletion T b) (bK i) := by
      conv_lhs => rw [hk]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def, map_mul]
      rw [IsScalarTower.algebraMap_apply T.arithmetic.F T.arithmetic.K
        (KUpperCompletion T b)]
    rw [hmap]
    refine Submodule.sum_mem V ?_
    intro i _
    rw [← completionMap_algebraMap_eq T b (bK.repr k i)]
    rw [show completionMap (k := T.arithmetic.F) (sectionKPlace T b) =
        algebraMap (KLowerCompletion T b) (KUpperCompletion T b) from rfl]
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem V _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hdense : DenseRange (algebraMap T.arithmetic.K (KUpperCompletion T b)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      (K := T.arithmetic.K) (v := (sectionKPlace T b).maximalIdeal)
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ closure (Set.range (algebraMap T.arithmetic.K (KUpperCompletion T b))) := by
      rw [hdense.closure_eq]
      exact Set.mem_univ x
    exact (hVclosed.closure_subset_iff.mpr (by
      rintro _ ⟨k, rfl⟩
      exact hmem k)) hx
  have hVtopFin : FiniteDimensional (KLowerCompletion T b)
      (⊤ : Submodule (KLowerCompletion T b) (KUpperCompletion T b)) :=
    hVtop ▸ hVfin
  have hfin : FiniteDimensional (KLowerCompletion T b) (KUpperCompletion T b) :=
    Module.Finite.equiv (Submodule.topEquiv (R := KLowerCompletion T b)
      (M := KUpperCompletion T b))
  exact Algebra.IsAlgebraic.of_finite (KLowerCompletion T b) (KUpperCompletion T b)

/-- Algebraicity in the Completion notation used by the S1482 target. -/
theorem completion_isAlgebraic :
    Algebra.IsAlgebraic (Completion (sectionFPlace T b)) (Completion (sectionKPlace T b)) :=
  completion_isAlgebraic_adic T b

/-! ## The algebraic closure comparison and the q-parameter transport -/

/-- The F_v-algebra equivalence between the two algebraic closures induced by
the algebraic completion extension. -/
noncomputable def sectionClosureEquiv_raw :
    AlgebraicClosure (KUpperCompletion T b) ≃ₐ[KLowerCompletion T b]
      AlgebraicClosure (KLowerCompletion T b) := by
  haveI : Algebra.IsAlgebraic (KLowerCompletion T b) (KUpperCompletion T b) :=
    completion_isAlgebraic_adic T b
  exact IsAlgClosure.equivOfAlgebraic (KLowerCompletion T b) (KUpperCompletion T b)
    (AlgebraicClosure (KUpperCompletion T b))
    (AlgebraicClosure (KLowerCompletion T b))

/-- The same equivalence in the Completion notation. -/
noncomputable def sectionClosureEquiv :
    AlgebraicClosure (Completion (sectionKPlace T b)) ≃ₐ[Completion (sectionFPlace T b)]
      AlgebraicClosure (Completion (sectionFPlace T b)) :=
  sectionClosureEquiv_raw T b

/-- The closure equivalence carries the K-side Tate parameter unit to the
F-side one.  This is the q-parameter half of the transport: it uses that the
K-side q is the completionMap image of the F-side q and that the equivalence is
over the lower completion. -/
theorem sectionClosureEquiv_tateParameterUnit :
    Units.map (sectionClosureEquiv T b).toRingEquiv.toMonoidHom
        (tateParameterUnit (sectionKPlace T b) (sectionQ T b).q
          (sectionQ T b).q_ne_zero) =
      tateParameterUnit (sectionFPlace T b) (sectionFQ T b).q
        (sectionFQ T b).q_ne_zero := by
  apply Units.ext
  have hq : ((sectionQ T b).q : KUpperCompletion T b) =
      algebraMap (KLowerCompletion T b) (KUpperCompletion T b) (sectionFQ T b).q := by
    rw [sectionQ_q (T := T) (b := b)]
    rfl
  change (sectionClosureEquiv_raw T b)
      (algebraMap (KUpperCompletion T b) (AlgebraicClosure (KUpperCompletion T b))
        (sectionQ T b).q) =
    algebraMap (KLowerCompletion T b) (AlgebraicClosure (KLowerCompletion T b))
      (sectionFQ T b).q
  rw [hq]
  rw [← IsScalarTower.algebraMap_apply (KLowerCompletion T b) (KUpperCompletion T b)
    (AlgebraicClosure (KUpperCompletion T b))]
  exact (sectionClosureEquiv_raw T b).commutes (sectionFQ T b).q

/-! ## The exact remaining point transport -/

/-- The exact missing transport: the Galois-equivariant point comparison at the
source-designated K-place.  This is precisely the points field of
TateCurveComparison (kSideCurve T) (sectionKPlace T b) (sectionQ T b); it is
not constructed from the curve transport above. -/
abbrev S1493KPointTransport : Type _ :=
  TatePointComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b)

/-- Assemble S1482KSideTateData from the constructed curve transport and the
exact point transport.  No point data is fabricated. -/
noncomputable def s1493KSideTateDataOfPointTransport
    (P : S1493KPointTransport T b) : S1482KSideTateData T b where
  canonicalIsElliptic := (s1493CurveTransport T b).canonicalIsElliptic
  coordinateChange := (s1493CurveTransport T b).coordinateChange
  realizesCurve := (s1493CurveTransport T b).realizesCurve
  points := P

/-- The target data is exactly the constructed algebraic transport together
with the missing point transport. -/
theorem s1493KSideTateData_iff_pointTransport :
    Nonempty (S1482KSideTateData T b) ↔ Nonempty (S1493KPointTransport T b) :=
  ⟨fun ⟨D⟩ => ⟨D.points⟩, fun ⟨P⟩ => ⟨s1493KSideTateDataOfPointTransport T b P⟩⟩

/-- The three algebraic fields are filled unconditionally. -/
theorem s1493CurveTransport_nonempty : Nonempty (S1493CurveTransport T b) :=
  ⟨s1493CurveTransport T b⟩

end LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual

end
