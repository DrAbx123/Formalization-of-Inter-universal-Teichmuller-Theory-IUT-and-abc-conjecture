import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance paperHullMeas : MeasurableSpace (C3LogShellTensorBlock C3) :=
  borel _

local instance paperHullBorel : BorelSpace (C3LogShellTensorBlock C3) :=
  ⟨rfl⟩

/-!
# Paper holomorphic hull phi(n,circ U) as actual sets, and its H_C readout

IUT III, Remark 3.9.5, (i), (ii) (pp. 158-160): for a possible-image region
`P` the holomorphic hull is the *smallest* subset of the form `lambda * O`
(each component of `lambda` nonzero) that contains `P`; equivalently, as in
Remark 3.9.5, (ii), the map `phi : P -> H` is characterized uniquely by

* (P1) `phi(H) = H` for every hull `H`;
* (P2) `P subset phi(P)`;
* (P3) `phi(P1) subset phi(P2)` whenever `P1 subset P2`.

The tree has two actual lambda-O hull operators on actual carriers:
`actualHolomorphicHull` on the actual C3 log-shell tensor packet
(`C3LogShellTensorHolomorphicHullActual`) and `literalIQHolomorphicHull` on the
actual completion-packet literal IQ carrier
(`LiteralIQHolomorphicHullActual`).  This module completes the paper
characterization (P1)-(P3) on both actual operators, extracts the actual Haar
log-volume readout of the paper hull on the C3 packet (finiteness,
unit-region equality, real value), and records the exact missing comparison with
the concrete source image (see the final section).

Source: IUT III, Remark 3.9.5, (i), (ii), pp. 158-160; Step (xi-d) of the proof
of Corollary 3.12 (corpus lines 10823-10863: "multiradial construction algorithm
followed by formation of the holomorphic hull ... yields a collection of
possibilities of output data in `1,circ U`").  No inequality is asserted here.
-/

/-- **P1 for the actual C3-packet paper hull.**  Hulling a candidate hull (a
nonzero `lambda * O` region) returns that candidate hull. -/
theorem actualHolomorphicHull_eq_self_of_candidate
    (P H : Set (HullBlock C3))
    (hH : H ∈ actualCandidateHulls C3 P) :
    actualHolomorphicHull C3 H = H := by
  apply Set.Subset.antisymm
  · exact actualHolomorphicHull_subset_candidate C3 H H
      ⟨hH.1, subset_rfl⟩
  · exact actualRegion_subset_hull C3 H

/-- **Least-hull property** for the actual C3-packet paper hull: it is contained
in every candidate `lambda * O` region containing the image set.  This is the
"smallest subset of the form lambda * O containing P" of Remark 3.9.5, (i). -/
theorem actualHolomorphicHull_least
    (P H : Set (HullBlock C3))
    (hH : H ∈ actualCandidateHulls C3 P) :
    actualHolomorphicHull C3 P ⊆ H :=
  actualHolomorphicHull_subset_candidate C3 P H hH

/-- **Paper characterization (P1)-(P3) of the actual C3-packet holomorphic
hull**, Remark 3.9.5, (ii). -/
theorem actualHolomorphicHull_paper_properties (P : Set (HullBlock C3)) :
    (∀ H : Set (HullBlock C3), H ∈ actualCandidateHulls C3 P →
        actualHolomorphicHull C3 H = H) ∧
      P ⊆ actualHolomorphicHull C3 P ∧
      (∀ Q : Set (HullBlock C3), P ⊆ Q →
        actualHolomorphicHull C3 P ⊆ actualHolomorphicHull C3 Q) :=
  ⟨fun _ hH => actualHolomorphicHull_eq_self_of_candidate C3 P _ hH,
    actualRegion_subset_hull C3 P,
    fun _ hPQ => actualHolomorphicHull_monotone C3 hPQ⟩

/-- The actual paper hull of the actual C3 log-shell tensor region is the actual
unit region itself (the unit region is already a `lambda * O` region, namely
`1 * O`). -/
theorem actualPaperHull_eq_unitRegion :
    actualHolomorphicHull C3 (actualUnitRegion C3) = actualUnitRegion C3 :=
  actualHolomorphicHull_unitRegion_eq C3

/-- **Finiteness of the paper-hull Haar log-volume on the actual C3 packet.**
The paper hull of the actual tensor region is the actual compact tensor region,
so its actual Haar volume is finite. -/
theorem actualPaperHull_measure_lt_top :
    actualC3LogShellTensorHaar C3
      (actualHolomorphicHull C3 (actualUnitRegion C3)) < ⊤ := by
  rw [actualPaperHull_eq_unitRegion C3]
  haveI hAdd : Measure.IsAddHaarMeasure (actualC3LogShellTensorHaar C3) :=
    inferInstance
  haveI hFin : IsFiniteMeasureOnCompacts (actualC3LogShellTensorHaar C3) :=
    hAdd.toIsFiniteMeasureOnCompacts
  exact (actualC3LogShellTensorRegion_compact C3).measure_lt_top

/-- The actual Haar log-volume readout of the paper holomorphic hull on the C3
log-shell tensor packet (`-|log(Theta)|`-side input before procession
normalization). -/
noncomputable def paperHullHaarReadout : ENNReal :=
  actualC3LogShellTensorHaar C3
    (actualHolomorphicHull C3 (actualUnitRegion C3))

theorem paperHullHaarReadout_eq_unitRegion :
    paperHullHaarReadout C3 =
      actualC3LogShellTensorHaar C3 (actualUnitRegion C3) := by
  unfold paperHullHaarReadout
  rw [actualPaperHull_eq_unitRegion C3]

/-- The real paper-hull log-volume readout on the actual C3 packet. -/
noncomputable def paperHullRealLogVolume : ℝ :=
  (paperHullHaarReadout C3).toReal

theorem paperHullRealLogVolume_nonneg : 0 ≤ paperHullRealLogVolume C3 :=
  ENNReal.toReal_nonneg

theorem paperHullRealLogVolume_ofReal_eq :
    paperHullHaarReadout C3 = ENNReal.ofReal (paperHullRealLogVolume C3) :=
  (ENNReal.ofReal_toReal (ne_top_of_lt (actualPaperHull_measure_lt_top C3))).symm

/-!
## Exact missing comparison with the concrete source image

Two paper objects remain **not identified** by the tree (records, with source):

1. **Paper IQ carrier.**  The identification of the actual completion-packet
   carriers with the paper inductive-system carrier `IQ(S^+-_{j+1};
   n,circ D^vdash_{vQ})` of IUT III, Proposition 3.2, (i), (ii) (pp. 97-99).
   The actual C3 log-shell tensor packet and the literal IQ carrier are built
   from actual completions, but the source prime-strip index/place comparison
   `V ≃ C3.tensorIndex` with matching tensor places is exactly the existing
   missing record `PrimeStripC3PlaceComparison` / 
   `PrimeStripC3PlaceComparisonRequired` (IUT III, Theorem 3.11, pp. 160-162;
   IUT IV, Theorem 1.10 proof, pp. 26-27).  Not constructed here.

2. **Paper hull vs the concrete source image.**  The paper `n,circ U_{j,vQ}`
   possible-image union inside `IQ(S^+-_{j+1}; n,circ D^vdash_{vQ})` (IUT III,
   Step (xi-d), corpus lines 10823-10863) is not yet identified with the
   concrete source `Q_l` log-shell image `sourceQlHullImage` of
   `S3129IQHullLogVolumeSourceActual`.  What is required is a
   scalar-preserving (multiplicative, componentwise) transport from the concrete
   completion into the paper IQ carrier that carries `sourceQlHullImage` onto
   the paper possible-image union and the actual integral log-shell unit region
   onto the paper `O`; given such a transport, the paper hull `phi` of the
   image is by construction the transport of the concrete hull readout.
   Without it no set-theoretic inclusion between the two carriers is derivable.
-/

end LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual

end