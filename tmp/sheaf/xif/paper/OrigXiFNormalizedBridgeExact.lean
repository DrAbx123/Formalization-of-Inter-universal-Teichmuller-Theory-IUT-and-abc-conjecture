import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

/-!
# OrigXiF: exact bridge surface between the normalized E1/E2 scalar and the
  original Theta-link scalar

Layer tags used below (see `coord/XI_F_ORIGINAL_ROUTE.md`):

* **N** = normalized E1/E2 model:
  `PaperLevelXiFTargetActual.ActualPaperXiFTarget T`, i.e.

      actualQPilotSignedLogClassical T <= actualThetaHullLogRoot T.

  The q side is a weighted sum over the native bad places of
  `nativeBadLocalWeight * qVFamNormalizedCoefficient * log (qVFamTensorP)`;
  the Theta side is the weighted normalized log of the root theta closure hull.
  This is *not* the original Theta-link xi-f.

* **O** = original Theta-link layer: `PaperQPilotObject.qPilotLogVolume` and
  `PaperSignedHull.signedHullLogVolume`, compared by
  `ThetaLinkActual.link_implies_inclusion`.

This file audits whether the N scalar can be used as the O scalar.  It does not
construct a `PaperQPilotObject`, a `PaperSignedHull` (beyond the explicitly
synthetic scalar model used for the independence proof), a
`SourcePilotRegionData`, an `OriginalInput`, or any D4-D9 object.  It does not
assert an inhabitant of the exact bridge structure below.

## Result of the audit

The two scalar comparisons are different propositions in the following precise
sense.

1. The N target is an inequality between two real numbers that are functions of
   the native datum `T` alone.  It contains no paper q-pilot object, no paper
   signed hull, and no Theta-link identification.

2. The O comparison is an inequality between the paper q-pilot scalar and the
   paper signed hull scalar.  For every real `q` there is a synthetic
   `PaperSignedHull` whose signed hull scalar is strictly below `q`; hence the
   O comparison is not a tautology and is not implied uniformly by the N target.
   This is proved below (`origXiFNormalizedTarget_not_uniformly_equivalent`,
   `origXiFNormalizedTarget_not_imply_thetaLinkScalar`).

3. Consequently a bridge from N to O cannot be the target inequality itself and
   cannot be the concrete Theta-link identification
   `concreteSourceComparison O P`, which is *equivalent* to the O comparison
   (`origXiFConcreteSourceComparison_iff`).  Such a use would be circular.

4. The exact bridge surface is the pair of scalar identifications

      N.q = O.qPilotLogVolume
      N.Theta = P.signedHullLogVolume

   (`OrigXiFNormalizedBridgeExact`).  Given these equations, the N target is
   equivalent to the O comparison
   (`origXiFNormalizedBridgeExact_iff_target`).  Neither equation is a
   definitional equality or a theorem in the current tree: the q sides are sums
   over different place families with different normalizations, and the Theta
   sides are a native root-closure hull log and a paper IQ/procession hull log.

No `PUnit`, `True`, empty type, axiom, or sorry is used to fill a bridge or
target obligation.  `PUnit` is used only as the (nonempty) label type of the
synthetic scalar model `OrigXiFProbeHull`; that model is never presented as the
paper signed hull.

-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFNormalizedBridgeExact

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open MeasureTheory
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual

universe u v ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- Canonical measurable structure on the qVFam tensor blocks, used only to
state the existing normalized target. -/
local instance origXiFCanonicalMeasurableSpace
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (qVFamTensorBlock T b) :=
  fun b => borel (qVFamTensorBlock T b)

/-- Canonical Borel structure on the qVFam tensor blocks. -/
local instance origXiFCanonicalBorelSpace
    (T : SourceNativeInitialThetaData.{0} l) :
    ∀ b : Bad (nativePlaceSelection T),
      BorelSpace (qVFamTensorBlock T b) :=
  fun _ => ⟨rfl⟩

/-! ## 1. The two scalar packages -/

/-- N-layer q scalar: the signed weighted normalized qVFam scalar. -/
noncomputable def OrigXiFNormalizedQScalar : Real :=
  actualQPilotSignedLogClassical (l := l) T

/-- N-layer Theta scalar: the weighted normalized root theta closure hull log. -/
noncomputable def OrigXiFNormalizedThetaScalar : Real :=
  actualThetaHullLogRoot T

/-- O-layer q scalar: the paper q-pilot object scalar. -/
def OrigXiFThetaLinkQScalar
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) : Real :=
  O.qPilotLogVolume

/-- O-layer Theta scalar: the paper signed hull log-volume. -/
def OrigXiFThetaLinkThetaScalar (P : PaperSignedHull X label) : Real :=
  P.signedHullLogVolume

/-- The N target is exactly the scalar inequality of the N package. -/
theorem origXiFNormalizedTarget_iff_scalar :
    ActualPaperXiFTarget (l := l) T ↔
      OrigXiFNormalizedQScalar T ≤ OrigXiFNormalizedThetaScalar T := by
  unfold ActualPaperXiFTarget OrigXiFNormalizedQScalar
    OrigXiFNormalizedThetaScalar
  rfl

/-- The O comparison is exactly the scalar inequality of the O package. -/
theorem origXiFThetaLinkComparison_iff_scalar
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume ↔
      OrigXiFThetaLinkQScalar O ≤ OrigXiFThetaLinkThetaScalar P := by
  unfold OrigXiFThetaLinkQScalar OrigXiFThetaLinkThetaScalar
  rfl

/-! ## 2. The exact bridge surface

The first field is the q-scalar identification.  The second is the Theta-scalar
identification.  No inhabitant is asserted. -/

/-- Exact N-to-O bridge: the two scalar identifications.  The first field is
the normalized qVFam q scalar = paper q-pilot scalar. -/
structure OrigXiFNormalizedBridgeExact
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) where
  /-- Exact first field: N.q = O.q. -/
  qScalar_eq :
    OrigXiFNormalizedQScalar T = O.qPilotLogVolume
  /-- Exact second field: N.Theta = P.signedHullLogVolume. -/
  thetaScalar_eq :
    OrigXiFNormalizedThetaScalar T = P.signedHullLogVolume

/-- The first field alone, as a named proposition.  It is a genuine real
equality between the native weighted normalized qVFam scalar and the paper
q-pilot scalar; it is not an inequality and it is not assumed elsewhere. -/
def OrigXiFNormalizedQIdentification
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) : Prop :=
  OrigXiFNormalizedQScalar T = O.qPilotLogVolume

/-- The second field alone, as a named proposition. -/
def OrigXiFNormalizedThetaIdentification
    (P : PaperSignedHull X label) : Prop :=
  OrigXiFNormalizedThetaScalar T = P.signedHullLogVolume

/-- Under the exact bridge, the N target and the O comparison are the same
proposition (after the two scalar identifications). -/
theorem origXiFNormalizedBridgeExact_iff_target
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (B : OrigXiFNormalizedBridgeExact T O P) :
    ActualPaperXiFTarget (l := l) T ↔
      O.qPilotLogVolume ≤ P.signedHullLogVolume := by
  change OrigXiFNormalizedQScalar T ≤ OrigXiFNormalizedThetaScalar T ↔
    O.qPilotLogVolume ≤ P.signedHullLogVolume
  rw [← B.qScalar_eq, ← B.thetaScalar_eq]

/-- The sufficiency direction of the exact bridge: N target + the two scalar
identifications gives the O comparison. -/
theorem origXiFNormalizedBridgeExact_implies_thetaLink
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (B : OrigXiFNormalizedBridgeExact T O P)
    (hN : ActualPaperXiFTarget (l := l) T) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (origXiFNormalizedBridgeExact_iff_target T O P B).mp hN

/-- With only the q-scalar identification, the O comparison is equivalent to
the independent inequality `N.q <= P.signedHullLogVolume`, not to the N
target.  The second scalar identification (or at least the inequality
`N.Theta <= P.signedHullLogVolume`) is still needed. -/
theorem origXiFQIdentification_iff_qComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hq : OrigXiFNormalizedQScalar T = O.qPilotLogVolume) :
    (O.qPilotLogVolume ≤ P.signedHullLogVolume) ↔
      OrigXiFNormalizedQScalar T ≤ P.signedHullLogVolume := by
  rw [← hq]

/-- With only the Theta-scalar identification, the O comparison is equivalent to
the independent inequality `O.qPilotLogVolume <= N.Theta`. -/
theorem origXiFThetaIdentification_iff_qComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hTheta : OrigXiFNormalizedThetaScalar T = P.signedHullLogVolume) :
    (O.qPilotLogVolume ≤ P.signedHullLogVolume) ↔
      O.qPilotLogVolume ≤ OrigXiFNormalizedThetaScalar T := by
  rw [← hTheta]

/-- The q-scalar identification plus the missing Theta bound is enough for the
O comparison; the bound is exactly the content that the N target does not
supply. -/
theorem origXiFNormalizedTarget_implies_thetaLink_of_q_and_thetaBound
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hq : OrigXiFNormalizedQScalar T = O.qPilotLogVolume)
    (hN : OrigXiFNormalizedQScalar T ≤ OrigXiFNormalizedThetaScalar T)
    (hThetaBound : OrigXiFNormalizedThetaScalar T ≤ P.signedHullLogVolume) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume := by
  rw [← hq]
  exact le_trans hN hThetaBound

/-! ## 3. The O-layer identification is the comparison, not a scalar bridge

`ConcreteThetaLinkSourceActual.concreteSourceComparison` is the actual
Theta-link identification currently available in the tree.  It is exactly the
O comparison after rewriting `signedHullLogVolume = -procession.average`.
Therefore it cannot be used to derive the O comparison from the N target without
circularity. -/

/-- The concrete Theta-link identification is exactly the O scalar comparison,
not an identification of the N and O scalars. -/
theorem origXiFConcreteSourceComparison_iff
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) :
    concreteSourceComparison O P ↔
      O.qPilotLogVolume ≤ P.signedHullLogVolume := by
  unfold concreteSourceComparison
  rw [PaperSignedHull.signedHullLogVolume_eq_neg_average]
  constructor <;> intro h <;> linarith

/-- The bridge plus the N target gives the concrete Theta-link identification;
this shows that the actual O-layer identification is downstream of the bridge,
not a substitute for it. -/
theorem origXiFNormalizedBridgeExact_to_concreteSourceComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (B : OrigXiFNormalizedBridgeExact T O P)
    (hN : ActualPaperXiFTarget (l := l) T) :
    concreteSourceComparison O P :=
  (origXiFConcreteSourceComparison_iff O P).mpr
    (origXiFNormalizedBridgeExact_implies_thetaLink T O P B hN)

/-! ## 4. The O comparison is not automatic

The following synthetic signed hull has prescribed signed log-volume `-v` for
any `0 <= v`.  It is a scalar model, not the paper carrier.  It only shows
that the O comparison has content not carried by the N target. -/

/-- Synthetic paper signed hull with signed log-volume `-v`.

This is a consistency/independence model for the scalar fields of
`PaperSignedHull`.  It is not constructed from the paper, is not asserted to be
the paper hull, and is not used in any positive bridge theorem. -/
def OrigXiFProbeHull (v : Real) (hv : 0 ≤ v) : PaperSignedHull Real PUnit := by
  classical
  let proc : WeightedValues PUnit :=
    { value := fun _ => v
      weight := fun _ => 1
      weightTotal := 1
      weightTotal_pos := by norm_num
      weightTotal_eq_sum := by simp }
  have hproc : proc.average = v := by
    simp [WeightedValues.average, proc]
  exact
    { ambient :=
        { imageSet := {0}
          hull := {0}
          imageSet_subset_hull := by intro x hx; exact hx
          logVolume := fun S => if S.Nonempty then ENNReal.ofReal v else 0
          logVolume_mono := by
            intro S T hST
            by_cases hS : S.Nonempty
            · have hT : T.Nonempty := by
                rcases hS with ⟨x, hx⟩
                exact ⟨x, hST hx⟩
              simp [hS, hT]
            · simp [hS]
          unitRegion := {0}
          scaleShift := fun x => x
          hull_subset_scaleShift := by
            intro x hx
            exact ⟨x, hx, rfl⟩
          unitRegion_logVolume_lt_top := by
            have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
            show (if ({0} : Set Real).Nonempty then ENNReal.ofReal v else 0) < ⊤
            rw [if_pos h]
            exact ENNReal.ofReal_lt_top
          scaleShift_unitRegion_logVolume_le := by simp }
      procession := proc
      hull :=
        { volume := fun _ => v
          hullVolume := v
          contains := fun _ => le_rfl }
      weighted_matches_hull := by intro i; rfl
      weights_nonnegative := by intro i; simp [proc]
      average_nonneg := by
        rw [hproc]
        exact hv
      hull_logVolume_eq_average := by
        have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
        show (if ({0} : Set Real).Nonempty then ENNReal.ofReal v else 0) =
          ENNReal.ofReal proc.average
        rw [hproc, if_pos h] }

/-- The synthetic hull has ambient hull log-volume `ENNReal.ofReal v`. -/
theorem OrigXiFProbeHull_logVolume_hull (v : Real) (hv : 0 ≤ v) :
    (OrigXiFProbeHull v hv).ambient.logVolume
        (OrigXiFProbeHull v hv).ambient.hull = ENNReal.ofReal v := by
  classical
  have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
  change (if ({0} : Set Real).Nonempty then ENNReal.ofReal v else 0) =
    ENNReal.ofReal v
  rw [if_pos h]

/-- The synthetic hull has signed log-volume `-v`. -/
theorem OrigXiFProbeHull_signedHullLogVolume (v : Real) (hv : 0 ≤ v) :
    (OrigXiFProbeHull v hv).signedHullLogVolume = -v := by
  unfold PaperSignedHull.signedHullLogVolume
  rw [OrigXiFProbeHull_logVolume_hull v hv, ENNReal.toReal_ofReal hv]

/-- For every real `q` there is a synthetic paper signed hull whose signed
hull scalar is strictly below `q`. -/
theorem exists_OrigXiFProbeHull_lt (q : Real) :
    ∃ P : PaperSignedHull Real PUnit, P.signedHullLogVolume < q := by
  let v := max 0 (1 - q)
  have hv : 0 ≤ v := le_max_left 0 (1 - q)
  refine ⟨OrigXiFProbeHull v hv, ?_⟩
  rw [OrigXiFProbeHull_signedHullLogVolume]
  have h : 1 - q ≤ v := le_max_right 0 (1 - q)
  linarith

/-- The O comparison is not automatic: for every paper q-pilot object there is
a synthetic paper signed hull whose signed hull scalar is strictly below the q
scalar. -/
theorem origXiFThetaLinkComparison_not_automatic
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    ∃ P : PaperSignedHull Real PUnit,
      ¬ O.qPilotLogVolume ≤ P.signedHullLogVolume := by
  obtain ⟨P, hP⟩ := exists_OrigXiFProbeHull_lt O.qPilotLogVolume
  exact ⟨P, not_le.mpr hP⟩

/-- The N target cannot be used as a uniform bridge to the O comparison: even
assuming the N target, the O comparison fails for a suitable signed hull. -/
theorem origXiFNormalizedTarget_not_imply_thetaLinkScalar
    (hN : ActualPaperXiFTarget (l := l) T) (q : Real) :
    ¬ (∀ P : PaperSignedHull Real PUnit,
        ActualPaperXiFTarget (l := l) T → q ≤ P.signedHullLogVolume) := by
  intro h
  obtain ⟨P, hP⟩ := exists_OrigXiFProbeHull_lt q
  exact (not_le.mpr hP) (h P hN)

/-- The N target is not equivalent to the O comparison, uniformly over paper
signed hulls: the O comparison can be made false while the N target is true. -/
theorem origXiFNormalizedTarget_not_uniformly_equivalent
    (hN : ActualPaperXiFTarget (l := l) T) (q : Real) :
    ¬ (∀ P : PaperSignedHull Real PUnit,
        ActualPaperXiFTarget (l := l) T ↔
          q ≤ P.signedHullLogVolume) := by
  intro h
  obtain ⟨P, hP⟩ := exists_OrigXiFProbeHull_lt q
  exact (not_le.mpr hP) ((h P).mp hN)

/-- For the actual paper q-pilot object, the O comparison also fails uniformly
over arbitrary synthetic signed hulls; it is therefore not a consequence of the
N target alone. -/
theorem origXiFNormalizedTarget_cannot_choose_hull
    (hN : ActualPaperXiFTarget (l := l) T)
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) :
    ¬ (∀ P : PaperSignedHull Real PUnit,
        ActualPaperXiFTarget (l := l) T →
          O.qPilotLogVolume ≤ P.signedHullLogVolume) := by
  intro h
  obtain ⟨P, hP⟩ := origXiFThetaLinkComparison_not_automatic O
  exact hP (h P hN)

/-! ## 5. Exact obstruction summary

The following theorem records the exact content of the audit as a single
implication-free statement: the two scalar comparisons are not equivalent
uniformly; the only positive bridge is the explicit pair of scalar equations;
and the concrete Theta-link identification is the O comparison itself.
No target is assumed to prove the bridge structure. -/

/-- Exact obstruction surface for the N-to-O bridge, as a conjunction of the
three proved facts:

* the O comparison is not implied by the N target uniformly in the signed hull;
* under the exact bridge equations, N target and O comparison coincide;
* the concrete Theta-link identification is equivalent to the O comparison.

The bridge equations themselves are the two fields of
`OrigXiFNormalizedBridgeExact`; no inhabitant is asserted. -/
theorem origXiFNormalizedBridgeExact_obstruction
    (hN : ActualPaperXiFTarget (l := l) T) :
    (¬ (∀ P : PaperSignedHull Real PUnit,
        ActualPaperXiFTarget (l := l) T → 0 ≤ P.signedHullLogVolume)) ∧
    (∀ (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
       (P : PaperSignedHull X label),
        OrigXiFNormalizedBridgeExact T O P →
          (ActualPaperXiFTarget (l := l) T ↔
            O.qPilotLogVolume ≤ P.signedHullLogVolume)) ∧
    (∀ (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
       (P : PaperSignedHull X label),
        concreteSourceComparison O P ↔
          O.qPilotLogVolume ≤ P.signedHullLogVolume) := by
  refine ⟨?_, ?_, ?_⟩
  · exact origXiFNormalizedTarget_not_imply_thetaLinkScalar T hN 0
  · intro O P B
    exact origXiFNormalizedBridgeExact_iff_target T O P B
  · intro O P
    exact origXiFConcreteSourceComparison_iff O P

/-! ## 6. Axiom probes -/

#print axioms origXiFNormalizedBridgeExact_iff_target
#print axioms OrigXiFProbeHull_signedHullLogVolume
#print axioms origXiFNormalizedTarget_not_uniformly_equivalent
#print axioms origXiFConcreteSourceComparison_iff
#print axioms origXiFNormalizedBridgeExact_obstruction

end LeanFormal.IUT.XiFPaper.OrigXiFNormalizedBridgeExact

end
