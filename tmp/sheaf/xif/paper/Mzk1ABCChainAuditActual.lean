/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A838: authoritative audit of the compiled ABC chain (thin; no imports) -/

/- PRECISE STATE (all cited LeanFormal/IUT/ABCBridge files olean=True):

* `IUTToABC.lean`: obligation `cor312ToABCBridge` (status pending) with note:
  'the proved interface theorem cor312ToABCTargetShape_iff_abcConjecture identifies the
  target shape with ABCConjecture using only standard three axioms; what remains is the
  arithmetic estimate'; plus equivalences `abcConjecture_iff_abcLogConjecture` and
  `abcConjecture_iff_abcArithmeticWeightHeightBound`.

* `Cor312ToABCBridgeInterface.lean` (L396-440):
  - `structure Cor312ToABCBridgeInterface` = carrier + `hullData : IQHullLogVolumeInterface`
    + `epsilonComparison : forall epsilon > 0, Cor312EpsilonArithmeticComparison hullData epsilon`;
  - `structure Cor312EpsilonArithmeticComparison` (L224-256) carries the TWO named gaps:
    `height_le_normalizedRegionVolume` (Gap1) and `regionVolume_le_normalizedWeight` (Gap2),
    as fields of the per-epsilon comparison region;
  - **`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`** (docstring L401-403):
    interface inhabited <-> ABCConjecture, i.e. the interface exposes EXACTLY the unproved
    arithmetic content;
  - `cor312ToABCBridge_heightBound (D) : forall eps>0, exists A, forall a b c IsABCTriple a b c,
    logHeight1 <= (1+eps)*arithmeticWeight + A` (L426) — proved from D; no unconditional closure.

* `ABCFrontier.lean`: `ABCFrontier : Prop` (L187), `bridgeInterface_of_frontier` (L199),
  **`abcConjecture_of_frontier (h : ABCFrontier) : ABCConjecture`** (L213);
  `ABCFrontierRealLine` + `ABCFrontier.reduce_realLine`.

* `ThetaBoundToHeightWeight.lean`: `exists_oneAdd_sq_le_oneAdd` (L47) and
  `heightWeightBound_of_normalizedVolumeComparison` (L67) — the re-absorption lemma used by
  the bridge proof.

* `ABCEllipticHeightCriterion.lean`: equivalences `abcConjecture_iff_freyJProductHeightCriterion`
  etc. (L61, L92, L118, L125, L154, L188) — equivalent height criteria, not new closure.

## TwoEstimates files
All `tmp/sheaf/xif/paper/Mzk1ABCTwoEstimates*.lean` files checked have olean=True
(30+ files including AuditCorrectionSha, CanonicalCrossCheckSha, CleanGateQpilot,
ComponentsSha, ConditionalSha, Evidence, GapDecomposition, GapLimitSha, GapShapeAuditSha,
GateVerificationSha, HeightLemmasSha, HeightWeightSha, ModelQpilot, NumericEvidence*,
RealModel*, ReductionInterface, ReductionQpilot, ...).  They formalize the two estimates /
gap decompositions in the abstract model; none provides a `Cor312EpsilonArithmeticComparison`
for the actual carrier (no construction of `Cor312ToABCBridgeInterface` was found in
ABCBridge: only `bridgeInterface_of_frontier` from the `ABCFrontier` hypothesis).

## Pinpoint: ABC is blocked at exactly
`Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume` (Gap1) together with
`regionVolume_le_normalizedWeight` (Gap2), for every `epsilon > 0`, for the actual carrier
(equivalently: a construction of `Cor312ToABCBridgeInterface`, equivalently `ABCFrontier`).
Unconditional `ABCConjecture` is available only from `ABCFrontier` (`abcConjecture_of_frontier`)
or from the interface construction; neither is present.

No sorry/axiom; this is an audit table, no new proof. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCChainAuditActual

def abcChainRows : List (String × String × String × String) :=
  [ ("cor312ToABCTargetShape_iff_abcConjecture", "target shape only", "PROVED (IUTToABC note)", "arithmetic estimate") ,
    ("abcConjecture_iff_abcArithmeticWeightHeightBound", "equivalence", "PROVED", "none") ,
    ("Cor312ToABCBridgeInterface", "carrier+hullData+epsilonComparison", "STRUCTURE (no construction)", "Nonempty = ABCConjecture") ,
    ("Cor312EpsilonArithmeticComparison", "Gap1 + Gap2 fields", "STRUCTURE (no construction)", "both gaps for all eps>0") ,
    ("cor312ToABCBridge_heightBound", "D : interface", "PROVED (conditional)", "interface construction") ,
    ("cor312ToABCBridgeInterface_nonempty_iff_abcConjecture", "iff", "PROVED", "Nonempty interface (open)") ,
    ("abcConjecture_of_frontier", "ABCFrontier", "PROVED (conditional)", "ABCFrontier (open)") ,
    ("heightWeightBound_of_normalizedVolumeComparison", "normalized volume comparison", "PROVED", "actual carrier data") ,
    ("ABCEllipticHeightCriterion equivalences", "height criteria", "PROVED", "none") ,
    ("Mzk1ABCTwoEstimates* (30+ files)", "abstract two estimates/gap decompositions", "GREEN olean=True", "no interface construction") ]

theorem abcChainRows_length : abcChainRows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCChainAuditActual
