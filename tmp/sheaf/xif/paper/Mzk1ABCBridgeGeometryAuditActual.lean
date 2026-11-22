/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A839: audit of ABCBridge/Geometry green layer (thin; no imports) -/

/- Findings (all cited files under LeanFormal/IUT/ABCBridge/, olean=True):

1. IQHullLogVolumeInterface for the finite-place/arithmetic-tuple model IS CONSTRUCTED:
   - `FinitePlaceIQHullInterface.lean:144` `noncomputable def arithmeticTupleIQHullLogVolumeInterface`
     (with existence form `exists_arithmeticTupleIQHullLogVolumeInterface` L104;
      generic `haarLogVolume` + `haarLogVolume_mono` L51-68);
   - scaled-unit variant `arithmeticTupleIQHullLogVolumeInterfaceScaledUnit`
     (FinitePlaceIQHullInterfaceScaledUnit:59), with `hull_lt_top` L89;
   - certificate layer (FinitePlaceIQHullCertificateActual): `arithmeticTupleIQHullTheta` L42,
     `..._nonneg` L46, `arithmeticTupleCanonicalHull_measure_lt_top` L68,
     `...ScaledUnit_hull_logVolume_lt_top` L73, `...ScaledUnit_hull_le_ofReal_theta` L81,
     `...IQHullScaledUnit_hq` L94;
   - signed certificates (FinitePlaceIQHullSignedCertificate): `arithmeticTupleSignedFiniteHull`
     L55, `..._hullVolume` L63, `arithmeticTupleSignedFiniteCertificate` L73,
     `..._thetaSigned` L94, `arithmeticTupleSignedLinkEvidence` L103;
   - NONVACUOUS signed certificate (FinitePlaceIQHullSignedCertificateNonvacuous):
     `arithmeticTupleSignedFloorQ` L55, `..._negative` L60, `..._le_hullLog` L67,
     `..._eq_hullLog_of_hullLog_lt_neg_one` L75, `arithmeticTupleSignedFloorCertificate` L87,
     `..._qSigned` L108;
   - sharp upper bound (FinitePlaceIQHullSharpUpperBound): `arithmeticTupleIQHullUnitRegion` L69
     with measure pos/lt_top/toReal_pos L75-107.

2. **Gap1/Gap2 are NOT closed for that carrier**: the ABCBridge files mentioning
   `Cor312EpsilonArithmeticComparison` are consumers/reducers:
   `Cor312ComparisonGapSupplyLayer:263` `cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound`
   (conditional on a weight bound), `ABCFrontier.lean:78` and `ABCFrontierReductions.lean:253`
   `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
   (conditional on split point/unit-region bounds), `ABCGap2FiniteC3Supply` (finite/C3-side
   supply layer), `Cor312CarrierRealizationSpec`, `Cor312ComparisonGapReduction`,
   `Cor312GapDictionaryLayer`, `Cor312PointwiseResidualSupply` (reduction dictionaries).
   No unconditional `Cor312EpsilonArithmeticComparison` construction for the actual carrier
   was found, and no `Nonempty (Cor312ToABCBridgeInterface)` construction (only the
   docstring/iff at Cor312ToABCBridgeInterface.lean:49).

3. `ABCFrontier.lean`: `FrontierHeightComparisonClause` (L146), `FrontierRegionComparisonClause`
   (L173), `ABCFrontier` (L187), `ABCFrontierRealLine` (L259), ledger obligation L368;
   reductions in `ABCFrontierReductions.lean` (`abcConjecture_of_pointwiseReduced` L314).
   No green provider of the Frontier clauses was found in `ABCBridge/Geometry/`.

4. PRECISE REMAINING: to get `Cor312EpsilonArithmeticComparison` for the finite-place carrier
   one must (i) instantiate the structure with `comparisonRegion`, `height_le_...` and
   `regionVolume_le_...` and (ii) prove Gap1 and Gap2 for all eps>0. Geometry provides the
   IQHull interface + certificates (theta bounds, signed nonvacuous certificate) and
   conditional gap suppliers; the two gaps themselves remain the open arithmetic content.

No sorry/axiom; no new proof. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGeometryAuditActual

def geometryAuditRows : List (String × String × String) :=
  [ ("arithmeticTupleIQHullLogVolumeInterface", "IQHull instance (finite-place model)", "CONSTRUCTED (green)") ,
    ("arithmeticTupleIQHullLogVolumeInterfaceScaledUnit", "scaled-unit IQHull", "CONSTRUCTED (green)") ,
    ("arithmeticTupleIQHullTheta / hull_le_ofReal_theta", "theta bound certificate", "PROVED (green)") ,
    ("arithmeticTupleSignedFloorCertificate", "nonvacuous signed certificate", "PROVED (green)") ,
    ("arithmeticTupleSignedFiniteCertificate_thetaSigned", "thetaSigned data", "PROVED (green)") ,
    ("cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound", "Gap1 given weight bound", "CONDITIONAL (SupplyLayer:263)") ,
    ("cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound", "Gap2 given split/unit bounds", "CONDITIONAL (ABCFrontier:78)") ,
    ("ABCGap2FiniteC3Supply", "C3-side gap2 supply layer", "LAYER (not gap closure)") ,
    ("Cor312EpsilonArithmeticComparison (unconditional)", "needed for interface", "NOT FOUND") ,
    ("Nonempty (Cor312ToABCBridgeInterface)", "equivalent to ABC", "NOT FOUND") ,
    ("FrontierHeightComparisonClause/FrontierRegionComparisonClause", "ABCFrontier clauses", "NO GREEN PROVIDER in Geometry") ]

theorem geometryAuditRows_length : geometryAuditRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGeometryAuditActual
