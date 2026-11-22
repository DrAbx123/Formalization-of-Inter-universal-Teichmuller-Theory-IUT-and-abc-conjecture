/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A841: quantitative proof plan for Gap1/Gap2 (audit + lemma inventory) -/

/- GREEN quantitative volume layer found in ABCBridge (all olean=True):
* FinitePlaceArithmeticIQHullVolume: `arithmeticTensorHullUnitLogVolume` (L58, spec L61,
  `..._eq` L65, `..._nonneg` L77);
* FinitePlaceArithmeticPacketVolume: `fullPrimeArithmeticHullPacketLogVolume` (L50,
  `..._nonneg` L54, `..._eq` L62, `..._mul_prime` L76), dimension L45;
* FinitePlaceSelectedPrimeWeightedVolume: `selectedPrimeWeightedRelativeLogVolume` (L33,
  `..._pi` L41, prime-smul L74);
* FinitePlaceSelectedPrimeWeightedHullVolume: `selectedPrimeWeightedHullLogVolume` (L35,
  `..._nonneg` L41, `..._eq_relativeLogVolume` L53, `..._mul_prime` L74,
  `..._eq_fieldProducts` L98);
* FinitePlaceIQHullSharpUpperBound: `arithmeticTupleIQHullUnitRegion` (L69) with measure facts;
* FinitePlaceStepVRealBound: `stepVPaperCorrectionSum_le` (L25), `stepVPaperLogVolumeBound` (L61);
* FinitePlaceIQHullSignedCertificateNonvacuous: `arithmeticTupleSignedFloorQ` (L55),
  `..._negative` (L60), `..._le_hullLog` (L67), equality case (L75),
  `arithmeticTupleSignedFloorCertificate` (L87), `..._qSigned` (L108) — nonvacuous but no
  Gap1/Gap2 split.

## Gap2 (quantitative): regionVolume <= (1+eps)*arithmeticWeight + hullLogVolume + D
regionVolume candidates: `selectedPrimeWeightedRelativeLogVolume` /
`selectedPrimeWeightedHullLogVolume` (exact field-products form L98) /
`fullPrimeArithmeticHullPacketLogVolume` (exact L62).
Missing lemmas:
- an explicit inequality `selectedPrimeWeightedRelativeLogVolume <= (1+eps)*arithmeticWeight
  + hullLogVolume + D` (none found);
- the combination with `stepVPaperCorrectionSum_le` / `stepVPaperLogVolumeBound`
  (they bound the StepV correction/log-volume, not this region-volume comparison);
- the identification of `arithmeticWeight` with the finite-place weighted sum
  (`arithmeticWeight` is defined on `Rat`; no finite-place dictionary theorem found).

## Gap1 (quantitative): height <= (1+eps)*normalizedRegionVolume
`Height.logHeight₁` has no definition grep hit under ABCBridge; the height side exists as
Frey/Legendre J-invariant height bounds (ABCModelHeightComparison):
`ellipticCurve_j_height_bounds_of_eq_abcJInvariant` (L34),
`..._upper_bound_transfers...` (L52), `rationalFreyWeierstrassCurve_j_height_bounds` (L91),
`abcRationalPoint_legendre_j_height_bounds` (L142), `..._transfer...` (L161).
Missing: the quantitative dictionary from `logHeight1(abcRationalPoint a c)` to the
`selectedPrimeWeightedRelativeLogVolume` + theta-bound form (i.e. the actual
Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume for all eps).

## Frontier clauses
`ABCFrontier.lean`: only two clause defs (`FrontierHeightComparisonClause` L146,
`FrontierRegionComparisonClause` L173) plus `ABCFrontier` L187 / `ABCFrontierRealLine` L259;
no green provider for either clause found; they are exactly the two gaps in split form.

No sorry/axiom; no new proof. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GapQuantitativePlanActual

def gapQuantRows : List (String × String × String) :=
  [ ("arithmeticTensorHullUnitLogVolume", "hull unit log-volume (exact, nonneg)", "GREEN ArithmeticIQHullVolume") ,
    ("fullPrimeArithmeticHullPacketLogVolume", "packet log-volume (exact)", "GREEN ArithmeticPacketVolume:50-76") ,
    ("selectedPrimeWeightedRelativeLogVolume", "weighted relative log-volume (pi/smul laws)", "GREEN SelectedPrimeWeightedVolume:33-74") ,
    ("selectedPrimeWeightedHullLogVolume", "weighted hull log-volume; = field products", "GREEN :35-98") ,
    ("arithmeticTupleIQHullUnitRegion measure facts", "unit region measure pos/finite", "GREEN SharpUpperBound:69-107") ,
    ("stepVPaperCorrectionSum_le", "A/B correction sum bound", "GREEN StepVRealBound:25") ,
    ("stepVPaperLogVolumeBound", "StepV log-volume bound", "GREEN StepVRealBound:61") ,
    ("arithmeticTupleSignedFloorCertificate", "nonvacuous signed certificate (hullLog<-1 case)", "GREEN Nonvacuous:87-108") ,
    ("Gap2 inequality (explicit)", "regionVolume <= (1+eps)weight+hull+D", "MISSING (no theorem)") ,
    ("Gap1 inequality (explicit)", "height <= (1+eps)normalizedRegionVolume", "MISSING (no theorem)") ,
    ("arithmeticWeight dictionary", "Rat arithmeticWeight vs finite-place weighted sum", "MISSING") ,
    ("logHeight1 definition/dictionary", "Height.logHeight1 vs weighted volume", "MISSING in ABCBridge") ,
    ("FrontierHeightComparisonClause", "first split clause", "NO PROVIDER") ,
    ("FrontierRegionComparisonClause", "second split clause", "NO PROVIDER") ]

theorem gapQuantRows_length : gapQuantRows.length = 14 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GapQuantitativePlanActual
