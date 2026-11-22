import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.S1554SignedHullFromQActual
import tmp.sheaf.xif.paper.S1880OriginalXiFActual

/-!
# S1920: paper-level xi-f on the source-faithful O object

Layer: **O** (original Theta-link / xi-f), continuation of S1895.

## Why this file

S1895 rebased the paper O object onto the actual paper `(1,0)` core and proved
the four paper-level identifications for `S1895PaperO D`.  S1880 proved the
xi-f inequality and built the paper Theta-link on `S1880PaperO`, whose strip is
the concrete finite-local strip; S1895 also proved that the F-times-mu bridge
from that strip to the paper core **cannot exist** (the value monoids at the
place 5 differ: `LocalIntegralMonoid 5` has the torsion element `-1`, while
`SourceHaarActualValueMonoid` is torsion-free).  So the S1880 xi-f content had
to be moved onto `S1895PaperO`; this file does exactly that.

## What is constructed here

Given `D : S1895PaperInput` (the paper Definition 3.1 input, the same one that
`S1895PaperO` is built from) and an actual paper signed-hull datum
`D' : OrigXiFPaperSignedHullData X D.l`:

1. `S1920PaperC3 D` -- the actual S1391 L-carrier `S1527C3` at the concrete
   Gaussian place above 5, re-indexed along the definitional identity
   `S1895PaperInput.I D = S1527Input D.l D.R ...`.  Its q is `S1487Cand` and
   its paper q-pilot log-volume is `-localLogMagnitude S1487Cand`
   `= -|log q|` (sections 1).
2. `s1920_paper_thetaLink` -- `OrigXiFThetaLinkActual (S1895PaperO D) D' (S1920PaperC3 D)`,
   from the S1554 producer at the same actual input.  Both exact scalar fields
   are proved, not assumed:
   * `scalar_eq`: the object's q-pilot log-volume is `OrigXiFPaperQPilotLogVolume C3`;
   * `signedHull_le`: `OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D'`.
3. `s1920_paper_linkIdentification` -- the concrete `link_identification` of that
   link, definitionally the S1458 proposition
   `OrigXiFThetaLinkIdentification (S1895PaperO D) D' (S1920PaperC3 D)`.
4. `s1920_paper_xiF_ray` -- the paper ray membership
   `(S1895PaperO D).qPilotLogVolume in hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume`.
5. `s1920_neg_abs_log_q_le_signedHull` -- `-|log q| <= OrigXiFSignedThetaHullLogVolume D'`,
   reusing the S1880 scalar proof/inequality verbatim (`s1880_xiF_inequality_abs`);
   `s1920_paper_qPilotLogVolume_le_signedHull` is the same comparison on the
   object's own scalar, and `s1920_paperC3_le_signedHull` rederives it through
   the C3 route (S1554) for cross-checking.
6. `s1920_paperFaithful_xiF` -- the combined statement: the S1895 four
   paper-level identifications on the source-faithful object, together with the
   Theta-link `link_identification` and the xi-f ray on the same object.  The
   paper-level xi-f therefore lives on the source-faithful `S1895PaperO`, not on
   the impossible S1880 carrier.

## Reuse, not duplication

The scalar content is not reproved: `s1880_xiF_inequality_abs` /
`s1880_xiF_inequality` (the comparison `-|log q| <= -|log Theta|`), the
S1527 arithmetic (`S1527C3_logVolume`, `S1527_sourceBadQAbsLog_eq_localLogMagnitude`),
the S1554 producer (`S1554_origXiFThetaLinkActual`, `S1554_signedHull_le`) and the
S1895 object plus its four identified props are imported and applied.  Nothing is
re-derived by hand.

## Exact remaining interface (no missing object)

For the requested target nothing is missing.  The only inputs are the two
actual objects above:

* `D : S1895PaperInput` -- the paper Definition 3.1 input including the D5-D9
  clause supply `R` and the D9 compatibility pairs.  This is an *input type*
  (S1880 already recorded `S1880FirstMissing` as its D5 torsion clause); the
  xi-f scalar computed below does not depend on the content of `R` (it is
  `-localLogMagnitude S1487Cand` by `s1895PaperO_qPilot_eq`).
* `D' : OrigXiFPaperSignedHullData X D.l` -- the actual paper signed-hull datum
  (itself built from an actual theta hull and an actual determinant procession).

The impossible S1880 route is not resurrected here: `s1895FirstMissing_impossible`
(S1895) remains the exact reason the S1880 carrier cannot carry the paper
identification.

No `sorry`, `axiom`, `True`, `PUnit`, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  Every scalar field is a theorem.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1920PaperFaithfulXiFActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1554SignedHullFromQActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.XiFPaper.S1684ThetaLinkFromActualOActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual

universe uX

/- The concrete Gaussian arithmetic carries its own local instances in the
files that construct it; they are local there, so the field structure of
GaussianField is restated here for the actual completion q (same pattern as
S1880 and S1554). -/
local instance s1920GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1920FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual S1391 C3 on the S1895 paper input -/

/-- The actual S1391 L-carrier C3 of the paper route, over the actual S1527
input of the S1895 paper data.  This is `S1527C3` re-indexed along the
definitional identity `S1895PaperInput.I D = S1527Input D.l D.R ...`. -/
noncomputable abbrev S1920PaperC3 (D : S1895PaperInput) :
    SourcePilotRegionDataL (I := S1895PaperInput.I D) :=
  S1527C3 D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

/-- The paper C3 carries the actual S1487 completion q. -/
theorem s1920PaperC3_q (D : S1895PaperInput) :
    (S1920PaperC3 D).q = S1487Cand :=
  S1527C3_q D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

/-- The paper q-pilot log-volume of the actual C3 is the actual completion
magnitude `-localLogMagnitude S1487Cand`. -/
theorem s1920PaperC3_logVolume (D : S1895PaperInput) :
    OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) = -localLogMagnitude S1487Cand :=
  S1527C3_logVolume D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
    D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

/-- The same scalar in the paper's own `-|log|` form: the C3 q-pilot
log-volume is `-|log q|` for the actual completion q. -/
theorem s1920PaperC3_logVolume_eq_neg_abs (D : S1895PaperInput) :
    OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) =
      -|Real.log ‖S1487Cand.q‖| := by
  rw [s1920PaperC3_logVolume, ← s1880_abs_log_q_eq_magnitude]

/-- The C3 q-pilot scalar evaluated arithmetically: `-(order_C3 * log 5)`. -/
theorem s1920PaperC3_logVolume_eq_neg_order_mul_log_five (D : S1895PaperInput) :
    OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) =
      -((S1487Cand.order : ℝ) * Real.log 5) :=
  S1554_qPilotLogVolume_eq_neg_order_mul_log_five D.l D.R D.redCompat
    D.hredCompat D.torCompat D.htorCompat D.orbCompat D.horbCompat
    D.secCompat D.hsecCompat D.cusCompat D.hcusCompat

/-! ## 2. The paper Theta-link on the source-faithful object -/

/-- **The paper-level original Theta-link on `S1895PaperO`.**  For every actual
paper signed-hull datum `D'` over the paper input `D`, the source-faithful
object `S1895PaperO D` carries `OrigXiFThetaLinkActual` at the actual S1391
L-carrier C3.  Both exact scalar fields are produced by the S1554/S1527
machinery at the same actual input; none is assumed. -/
theorem s1920_paper_thetaLink (D : S1895PaperInput) {X : Type uX} [TopologicalSpace X]
    (D' : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFThetaLinkActual (S1895PaperO D) D' (S1920PaperC3 D) :=
  S1554_origXiFThetaLinkActual D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat (S1895PaperO D) D'

/-- The exact scalar field of the link: the object's q-pilot log-volume is the
actual C3 paper scalar. -/
theorem s1920_paper_scalar_eq (D : S1895PaperInput) {X : Type uX} [TopologicalSpace X]
    (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume = OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) :=
  (s1920_paper_thetaLink D D').scalar_eq

/-- The exact signed-hull comparison field of the link. -/
theorem s1920_paper_signedHull_le (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) ≤
      OrigXiFSignedThetaHullLogVolume D' :=
  (s1920_paper_thetaLink D D').signedHull_le

/-- **The concrete `link_identification` of the paper Theta-link on the
source-faithful object.**  Its type is literally the S1458 proposition
`OrigXiFThetaLinkIdentification (S1895PaperO D) D' (S1920PaperC3 D)`:
the object scalar is the actual paper q-pilot scalar, and it is below the
actual signed theta hull log-volume.  Both conjuncts are proved from S1527 and
S1554; the second is the S1880/S1554 comparison. -/
theorem s1920_paper_linkIdentification (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (s1920_paper_thetaLink D D').link_identification :=
  OrigXiFThetaLinkIdentification_of_fields (S1895PaperO D) D' (S1920PaperC3 D)
    (S1527_origXiFScalarExactField D.l D.R D.redCompat D.hredCompat
      D.torCompat D.htorCompat D.orbCompat D.horbCompat D.secCompat
      D.hsecCompat D.cusCompat D.hcusCompat (S1895PaperO D))
    (S1554_signedHull_le D.l D.R D.redCompat D.hredCompat D.torCompat
      D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
      D.cusCompat D.hcusCompat D')

/-- The link identification is definitionally the S1458 conjunction, recorded
for the consumer. -/
theorem s1920_paper_linkIdentification_eq (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (s1920_paper_thetaLink D D').link_identification =
      OrigXiFThetaLinkIdentification (S1895PaperO D) D' (S1920PaperC3 D) := rfl

/-! ## 3. The xi-f inequality and the paper ray -/

/-- **The xi-f inequality on the paper C3.**  The actual C3 q-pilot scalar is at
most the actual signed theta hull log-volume, via the S1554 comparison at the
same actual input. -/
theorem s1920_paperC3_le_signedHull (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFPaperQPilotLogVolume (S1920PaperC3 D) ≤
      OrigXiFSignedThetaHullLogVolume D' :=
  S1554_signedHull_le D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat
    D.hcusCompat D'

/-- **The requested xi-f inequality** `-|log q| <= -|log Theta|` for every actual
paper signed-hull datum, reusing the S1880 scalar proof verbatim.  It is a
statement about the actual completion q and the actual hull, independent of the
paper input `D`; it is attached below to the object's own scalar. -/
theorem s1920_neg_abs_log_q_le_signedHull {X : Type uX} [TopologicalSpace X]
    {l : PrimeGeFive} (D' : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| ≤ OrigXiFSignedThetaHullLogVolume D' :=
  s1880_xiF_inequality_abs D'

/-- The strict form of the same comparison (S1880). -/
theorem s1920_neg_abs_log_q_lt_signedHull {X : Type uX} [TopologicalSpace X]
    {l : PrimeGeFive} (D' : OrigXiFPaperSignedHullData X l) :
    -|Real.log ‖S1487Cand.q‖| < OrigXiFSignedThetaHullLogVolume D' :=
  s1880_xiF_inequality_strict D'

/-- The object scalar is the paper's `-|log q|`. -/
theorem s1920_paper_qPilotLogVolume_eq_neg_abs (D : S1895PaperInput) :
    (S1895PaperO D).qPilotLogVolume = -|Real.log ‖S1487Cand.q‖| := by
  rw [s1895PaperO_qPilot_eq, ← s1880_abs_log_q_eq_magnitude]

/-- **The xi-f inequality on the source-faithful object's own scalar**:
`(S1895PaperO D).qPilotLogVolume <= OrigXiFSignedThetaHullLogVolume D'`.  The
object scalar is `-localLogMagnitude S1487Cand = -|log q|` by S1895, so this is
the paper inequality at the paper object. -/
theorem s1920_paper_qPilotLogVolume_le_signedHull (D : S1895PaperInput)
    {X : Type uX} [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D' := by
  rw [s1920_paper_qPilotLogVolume_eq_neg_abs D]
  exact s1920_neg_abs_log_q_le_signedHull D'

/-- **The paper xi-f ray membership on the source-faithful object**:
the object's q-pilot scalar lies in the paper ray `R_{<= -|log Theta|}` of the
actual signed hull.  Obtained from the link's `link_implies_inclusion`, i.e. by
the consumer of `link_identification`, with no extra input. -/
theorem s1920_paper_xiF_ray (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume :=
  (s1920_paper_thetaLink D D').link_implies_inclusion
    (s1920_paper_linkIdentification D D')

/-- The same ray membership as the actual signed-hull inequality. -/
theorem s1920_paper_xiF_ray_iff (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume ↔
      (S1895PaperO D).qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D' :=
  OrigXiFThetaLinkRay_iff_le D' _

/-- **The paper xi-f core on the source-faithful object**: the concrete
`link_identification` together with the ray membership, both on
`S1895PaperO`.  This is the S1880 `s1880_paper_xiF_core` content rebased onto
the object whose four paper identifications S1895 proved. -/
theorem s1920_paper_xiF_core (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (s1920_paper_thetaLink D D').link_identification ∧
      (S1895PaperO D).qPilotLogVolume ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume :=
  ⟨s1920_paper_linkIdentification D D', s1920_paper_xiF_ray D D'⟩

/-! ## 4. The paper-level xi-f on the source-faithful object -/

/-- The four paper-level identification obligations of `S1895PaperO D` (with the
two frozen scalar/line-bundle fields), as a proposition.  This is the exact
conjunction proved in S1895 by `s1895PaperO_identifications`. -/
def S1920PaperIdentifications (D : S1895PaperInput) : Prop :=
  (S1895PaperO D).paper_strip_identification ∧
    (S1895PaperO D).paper_logKummer_identification ∧
      ((s1895PaperO_oneColumnLabel D).n = 1 ∧
          (s1895PaperO_oneColumnLabel D).m = 0 ∧
          (s1895PaperO_oneColumnLabel D).carrier = (S1895PaperO D).oneColumn) ∧
        ((S1895PaperO D).strip = sourceQPilotStrip (S1895PaperO D).boundary ∧
            (S1895PaperO D).boundary.target_q =
              (S1895PaperO D).boundary.theater.thetaPacket.q) ∧
          (S1895PaperO D).paper_lineBundle_identification ∧
            (S1895PaperO D).paper_qPilot_log_identification

/-- The S1895 four paper-level identifications, repackaged. -/
theorem s1920_paperIdentifications (D : S1895PaperInput) :
    S1920PaperIdentifications D :=
  s1895PaperO_identifications D

/-- **The paper-level xi-f on the source-faithful object, bundled.**  For every
paper input `D` and every actual paper signed-hull datum `D'`:

* the four paper-level identifications of `S1895PaperO D` (F-times-mu strip,
  full one-column log-Kummer, the S1679 line bundle, the (1,0) label binding and
  the two strip anchors), all proved in S1895;
* the original Theta-link `OrigXiFThetaLinkActual (S1895PaperO D) D' (S1920PaperC3 D)`
  with its `link_identification`;
* the xi-f ray membership and the scalar inequality at the object.

So the paper-level xi-f is attached to the object on which the paper
identifications are actually proved, rather than to `S1880PaperO` (for which
`s1895FirstMissing_impossible` shows the F-times-mu bridge cannot exist). -/
theorem s1920_paperFaithful_xiF (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    S1920PaperIdentifications D ∧
      (s1920_paper_thetaLink D D').link_identification ∧
      (S1895PaperO D).qPilotLogVolume ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume ∧
      (S1895PaperO D).qPilotLogVolume =
        -|Real.log ‖S1487Cand.q‖| ∧
      -|Real.log ‖S1487Cand.q‖| ≤ OrigXiFSignedThetaHullLogVolume D' :=
  ⟨s1920_paperIdentifications D,
    s1920_paper_linkIdentification D D',
    s1920_paper_xiF_ray D D',
    s1920_paper_qPilotLogVolume_eq_neg_abs D,
    s1920_neg_abs_log_q_le_signedHull D'⟩

/-- The scalar half of `s1920_paperFaithful_xiF` on its own: the object scalar
is the paper `-|log q|` and it is below the actual signed hull log-volume. -/
theorem s1920_paperFaithful_scalar (D : S1895PaperInput) {X : Type uX}
    [TopologicalSpace X] (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume = -|Real.log ‖S1487Cand.q‖| ∧
      (S1895PaperO D).qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D' :=
  ⟨s1920_paper_qPilotLogVolume_eq_neg_abs D,
    s1920_paper_qPilotLogVolume_le_signedHull D D'⟩

/-! ## 5. Boundary: the S1880 carrier is not resurrected, and nothing is missing

The paper xi-f chain above uses only `D : S1895PaperInput` and
`D' : OrigXiFPaperSignedHullData X D.l`.  The S1880 route through
`S1880PaperO` stays impossible; this is the S1895 obstruction, recalled here as
the exact reason for the rebasing. -/

/-- The S1880-carrier F-times-mu bridge (the S1880 object's first paper-level
identification) has no inhabitant.  Recalled from S1895: this is why the xi-f
content is attached to `S1895PaperO` here. -/
theorem s1920_s1880_bridge_impossible (D : S1895PaperInput) :
    ¬ Nonempty (S1895S1880FTimesMuBridge D) :=
  s1895FirstMissing_impossible D

/-- No F-prime-strip equivalence exists between the S1880 concrete strip and the
paper (1,0) core (value-monoid obstruction at the place 5).  Recalled from
S1895. -/
theorem s1920_s1880_no_stripEquiv (D : S1895PaperInput) :
    ¬ Nonempty (FPrimeStripEquiv (S1895S1880O D).strip
      (S1895Core (S1895PaperInput.I D))) :=
  s1895S1880_no_stripEquiv D

/-! ## 6. Axiom probes -/

#print axioms s1920PaperC3_logVolume
#print axioms s1920PaperC3_logVolume_eq_neg_abs
#print axioms s1920_paper_thetaLink
#print axioms s1920_paper_scalar_eq
#print axioms s1920_paper_signedHull_le
#print axioms s1920_paper_linkIdentification
#print axioms s1920_paperC3_le_signedHull
#print axioms s1920_neg_abs_log_q_le_signedHull
#print axioms s1920_neg_abs_log_q_lt_signedHull
#print axioms s1920_paper_qPilotLogVolume_le_signedHull
#print axioms s1920_paper_qPilotLogVolume_eq_neg_abs
#print axioms s1920_paper_xiF_ray
#print axioms s1920_paper_xiF_ray_iff
#print axioms s1920_paper_xiF_core
#print axioms s1920_paperFaithful_xiF
#print axioms s1920_paperFaithful_scalar
#print axioms s1920_s1880_bridge_impossible

end LeanFormal.IUT.XiFPaper.S1920PaperFaithfulXiFActual

end
