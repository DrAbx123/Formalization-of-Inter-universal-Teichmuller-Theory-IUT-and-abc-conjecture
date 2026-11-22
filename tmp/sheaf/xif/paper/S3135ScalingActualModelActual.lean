import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-!
# Card (2) at the concrete actual model: `logDegree(scaling) = 0` is a theorem

**task-17 (A).**  The task-11 file proved that the family
`∀ eps > 0, S3135ScalingNormalization eps` is *equivalent* to the scalar equation
`S3135ScalingLogDegreeZero : logDegree_v(scaling) = 0`, and that the abstract
`SourceUnitRegionHaarData` fields only give `logDegree_v(scaling) ≤ 0`.

This file proves the equation **unconditionally on the concrete actual model**
`SourceUnitRegionHaarDataActual.lean` (the value-layer model: nonpositive reals under
addition, `q = 1`, shear prime strips; explicitly not the paper ring-of-integers
carrier).  For *every* Haar datum `D` on that model:

* the monoid unit `1` lies in the actual source holomorphic hull
  (the hull contains the unit because the `q = 1` theta image is the unit), so
  `D.hull_subset_scaledRegionImage` exhibits witnesses `y ∈ D.unitRegion` with
  `1 = D.scaling * y`;
* componentwise, `logDegree(scaling_i) + logDegree(y_i) = 0`; every value of the
  concrete monoid has nonpositive log-degree, so `logDegree(y) ≤ 0` and hence
  `logDegree(scaling) ≥ 0`;
* with the carrier field `logDegree(scaling) ≤ 0` this forces
  `logDegree(scaling) = 0`.

Hence on the concrete actual model both card (2) and its whole `eps`-family hold
**as theorems** (for every `D` and every procession `n`), by
`s3135_normalization_of_scalingLogDegreeZero`.  The paper carrier's scaling is not
constructed in the tree, so for the paper carrier the equation remains the named
normalization input (IUT III Remark 3.9.5, (i); IUT IV section 1, Prop 1.4,
iut4.txt:671-760).

Note: the same concrete model **refutes** the card-(1) faithfulness (see
`S3135LogShellFaithfulnessExpansionActual.lean`): its positive-real action is the
trivial homomorphism (a group can only map trivially into a nonpositive value monoid),
so card (1) is genuinely additional structure, not a consequence of the data.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual

namespace LeanFormal.IUT.XiFPaper.S3135ScalingActualModelActual

universe ua

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{ua} l)
variable (n : ThetaPilotCarrier l)

/-- The monoid unit lies in the actual source holomorphic hull of the concrete
model: the `q = 1` theta-pilot image point is the unit. -/
theorem sourceHaarActual_unit_mem_hull :
    (1 : (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) ∈
      (sourceHaarActualOriginalInput (l := l) S).sourceHolomorphicHull ()
        (sourceHaarActualImageRealization (l := l) S) n := by
  refine subset_holomorphicHull ?_
  refine ⟨zeroSignedLabel, ?_⟩
  ext p
  rfl

/-- **Card (2) on the concrete actual model, unconditionally.**  Every Haar datum on
the concrete value-layer model has normalized scaling log-degree zero. -/
theorem sourceHaarActual_scalingLogDegree_zero
    (D : (sourceHaarActualOriginalInput (l := l) S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n) :
    (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree () D.scaling = 0 := by
  have h1 := sourceHaarActual_unit_mem_hull (l := l) S n
  obtain ⟨y, hy, hxy⟩ :=
    (mem_scaledRegionImage_iff).mp (D.hull_subset_scaledRegionImage h1)
  have hkey : ∀ i : SourceVolumeIndex l,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () (D.scaling i) +
        (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () (y i) = 0 := by
    intro i
    have hi : (1 : (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) i =
        (D.scaling * y) i := congrFun hxy i
    have hprod : D.scaling i * y i = 1 := by
      have := hi.symm
      simpa using this
    have hlog := congrArg
      (fun z => (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () z) hprod
    rw [(sourceHaarActualOriginalInput (l := l) S).logDegreeAt_mul,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt_one] at hlog
    exact hlog
  have hy_nonpos : ∀ i : SourceVolumeIndex l,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () (y i) ≤ 0 := by
    intro i
    rw [sourceHaarActual_logDegreeAt_eq]
    have hx := (Multiplicative.toAdd (y i)).property
    change ((Multiplicative.toAdd (y i) : sourceHaarActualNonpositiveAddSubmonoid) : Real) ≤ 0
    exact hx
  have hsum_le : (∑ i : SourceVolumeIndex l,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () (y i)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hy_nonpos i)
  have hS_eq : (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree () D.scaling =
      - ∑ i : SourceVolumeIndex l,
          (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 () (y i) := by
    unfold sourceLocalLogDegree
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := hkey i
    linarith
  have hS_ge : 0 ≤
      (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree () D.scaling := by
    rw [hS_eq]
    linarith
  exact le_antisymm D.scaling_logDegree_nonpos hS_ge

/-- The scalar card `S3135ScalingLogDegreeZero` holds on the concrete actual
model. -/
theorem sourceHaarActual_scalingLogDegreeZero
    (D : (sourceHaarActualOriginalInput (l := l) S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n) :
    S3135ScalingLogDegreeZero (sourceHaarActualOriginalInput (l := l) S) ()
      (sourceHaarActualImageRealization (l := l) S) n D :=
  sourceHaarActual_scalingLogDegree_zero (l := l) S n D

/-- **The whole card-(2) family holds on the concrete actual model**, by the task-11
equivalence direction (zero log-degree => normalized scaling inequality). -/
theorem sourceHaarActual_normalization_family
    (D : (sourceHaarActualOriginalInput (l := l) S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n) :
    ∀ eps : ℝ, 0 < eps →
      S3135ScalingNormalization (sourceHaarActualOriginalInput (l := l) S) ()
        (sourceHaarActualImageRealization (l := l) S) n D eps :=
  s3135_normalization_of_scalingLogDegreeZero (sourceHaarActualOriginalInput (l := l) S) ()
    (sourceHaarActualImageRealization (l := l) S) n D
    (sourceHaarActual_scalingLogDegreeZero (l := l) S n D)

#check sourceHaarActual_scalingLogDegreeZero
#check sourceHaarActual_normalization_family

end LeanFormal.IUT.XiFPaper.S3135ScalingActualModelActual
end
