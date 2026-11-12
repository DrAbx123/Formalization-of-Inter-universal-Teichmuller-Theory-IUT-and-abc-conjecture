# GAPS — Cor 3.12 / ABC bridge and T line (2026-11-07)

## A. ABC bridge gaps (target: Cor312ToABCBridgeInterface)

### G0. Carrier normalization (open)
Need a line-bundle IQHull W with:
  X := (SourceLineBundle A)^×
  hull = unitRegion = {1}
  scaleShift = id
  logVolume S := (1/2) * sup_{y in S} Real.log (absNorm y.1)
Status: S2800 ACTUAL conditional assembly (`S2800GlobalData`, `S2800LogVolume =
(1/2)*covolume`, `S2800Bridge`) defines the half-normalized interface, but the
CONCRETE normalized W (covolume/W/logShellPoint fields) is still not supplied.
No unconditional carrier yet; S2781's W is unnormalized.
Source-Haar carrier is NOT usable: S2812DegreeFaithfulSectionActual is ACTUAL and
proves `S2812_sourceHaarActual_no_degreeFaithfulSection` (no degree-faithful
section from the source-Haar datum). S2800's line-bundle route may BYPASS the
source-Haar carrier; it does not provide the concrete normalized W yet.
Owner: logdescent (S2800).

### G1. Region upper bound (open, provable)
Need for every eps>0:
  exists D, forall a b c, ABC ->
    (1+eps) * W.logVolume (normalizedComparisonRegion W point a b c)
      <= (1+eps) * arithmeticWeight x + W.logVolume W.hull + D
Reduction:
  supportIdeal absNorm <= (natRadical (a*b*c))^2
  + qPilot constant
Status: S2795 per-place bound + S2796 product bound pending.
Owner: iplsheapt S2795, logdescent S2796/S2800.
Note: raw S2780RegionWeightGap is FALSE (inert p^2); must use half-normalized W.

### G2. Height comparison (open, ABC-equivalent)
Need for every eps>0:
  forall a b c, ABC ->
    Height.logHeight₁ (abcRationalPoint a c)
      <= (1+eps) * W.logVolume (normalizedComparisonRegion W point a b c)
Status: NOT actual. This is IUT IV height comparison / ABC height bound.
Owner: transport (S2791) then Lead.
Do not substitute pointHeightDictionary (different carrier, opposite direction).

### G3. Bridge assembly (open, mechanical after G0-G2)
Construct:
  epsilonComparison : ∀ eps>0, Cor312EpsilonArithmeticComparison W eps
  Cor312ToABCBridgeInterface
Status: S2800LineBundleCor312BridgeActual is ACTUAL (olean 83168 B,
SHA 50515F1CF783D6D134608B1235ACF0052D7B1BFFD2592B1118DBBA033264870D):
`S2800Bridge` constructs `Cor312ToABCBridgeInterface` from `S2800GlobalData`
plus per-eps `S2800EpsData` fields `hregion` and `hheight`. Assembly is MECHANICAL
and ACTUAL, but it remains conditional on G0-G2; no unconditional bridge.
Owner: logdescent.

### Discarded
- S2772 mixedSpace bridge: VACUOUS (S2777/S2780 no-go).
- S2780 raw line-bundle bridge: raw region volume not correct (inert p^2).
- pointHeightDictionary: different carrier/direction; cannot replace G2.

## B. T / Clause gaps

### G4. Faithful D6 geometric realization (open, hard)
Need:
  fiber := nondegenerate EtaleStackPseudofunctor (actual curve stack)
  isStack, nondegenerate, curvePointRealization surjective
Status: S2811IsPrestackActual ACTUAL (S2811_yoneda_isSheaf). **S2812IsStackActual
is now ACTUAL**: clean compile EXIT=0; src SHA
65BB5200E9C261A3F593B3FA8FA99671E45177562A4C5A871CDF1A58CE4BA832; current olean
200952 B SHA E07573164D5B636E7953B56A607D1632C23F89C795596DA655B1395C52623A3F;
axioms trio for schemeRepresentableEtalePseudofunctor_isStack, essSurj_toDescentData,
isStackFor_sieve, gluedSection. The Subcanonical -> Cat-valued stack step is closed.
**D6 F6 COMPLETE ACTUAL**: nondegeneracy (S2847D6F6Nondegenerate) and zero
preimage (S2845ZeroPreimage) are actual; S2848D6F6CompleteActual builds
`S2848D6 : MissingD6GeometricRealization K` (olean 14640 B, SHA 5C35953D...; axioms
trio). D6 fixed X = E37ProjGluedScheme with S2820 transition iso; S2821 Over
structure is complete. No remaining D6 F6 input.
Owner: multiradial.

### G5. SourceSignQuotientData S (open, depends G4)
30 fields: xF/xF_geometry/signAction/quotient/groups/xK/cK/epsilon + place block.
Status: A5 place block ACTUAL; stack/sign fields missing. S2812 no-go means the
source-Haar carrier cannot supply the missing section; S2798/Q(i) route proceeds
independently.
Owner: multiradial.

### G6. ClauseA hstable (RESOLVED ACTUAL)
Need ∀ P : FinitePlace Q(i), E37Qi.HasStableReductionAt P.
Status: S2798StableEverywhere37Actual is ACTUAL (olean 181272 B,
SHA B3E753CA659A72E460CE9450C42A09C8ECF28B67BD9EF9D1854F2870BDB78226);
`S2798_hasStableReductionEverywhere` supplies hstable. Remaining ClauseA work is
the assembly (G7), not hstable.
Owner: qside (S2798 ACTUAL).

### G7. ClauseA assembly (open, depends G5+G6)
S2797ClauseA (S) (hstable) ACTUAL conditional.
Status: hstable is now ACTUAL (S2798). However S2813ClauseA37ReadyActual is
built on `S2786Arithmetic` (K = Q(i)), which is INVALID for ClauseC; S2813 is an
intermediate/conditional version only, NOT final T. `arithmetic37` is ALSO
invalid for ClauseC (its F = Q(i), E[6] not rational there). The correct A6 is
F = F6 = S2790F6, curve = S2790E.baseChange F6, K = kernel field over F6; qside
is rebuilding in S2847. Still blocked by the missing canonical
SourceSignQuotientData on the correct F6 arithmetic.

### G8. F6 = Q(i,E[6]) (open, definition ACTUAL)
Have S2790F6 definition; Field/Algebra/CharZero.
Missing:
  FiniteDimensional GaussianField S2790F6
  NumberField/IsGalois
  Torsion23Rational
Owner: volumedet.

### G9. ClauseC (open, depends G8 + large image + kernel)
S2774 conditional ClauseC ACTUAL.
Need:
  F6/Torsion23Rational
  imageContainsSL2 actual
  kernelFieldIdentification (rfl if K = kernel field)
Owner: qside.

### G10. ClauseB (open, depends G5+G7+G9)
S2787ClauseB interface ACTUAL.
Need:
  S, C
  multiplicative Lean proof at 37
  qWitness / residueCoprime
Owner: volumedet/primespine.

### G11. ClauseD/E/F (open, depends G5+G7+G9)
E: SourceClauseELocalFamilyUnit actual
F: SourceClauseFBoundaryUnit actual
D: K-side witnesses / groups / cusp
Owner: multiradial + logdescent.

### G12. T assembly (open, depends G7-G11)
SourceClauseAssembly / SourceCompletion / InitialThetaSourceGate.
Owner: Lead.

## Closed actual prerequisites
- Gap1 rank-two torsion S2771.
- SL2(F5) closure S2763.
- large-image consumer S2778.
- quadratic base-change large image S2783.
- 37 places S2786.
- 37 multiplicative model S2794.
- field of moduli/max-solvable S2793.
- clauseA conditional S2797.
- normalized region S2792 (conditional bound).
- pointed region S2781.
- F6 definition S2790 (instances open).
- hstable everywhere S2798.
- subcanonical/yoneda sheaf S2811.
- ClauseA conditional-only-S S2813 (INTERMEDIATE: S2786Arithmetic K=Q(i), NOT final T).
- Correct ClauseC arithmetic: F=S2790F6, curve=S2790E.baseChange F6, K=kernel field over F6; S2847 rebuild in progress.
- `arithmetic37` (K=K37) is also INVALID for ClauseC: F=Q(i), E[6] not rational.
- S2807 SG1 theta-hull volume identity (S2807ThetaHullVolumeIdentityActual).
- source-Haar no-go S2812 (not usable).
- Subcanonical -> Cat stack S2812IsStack ACTUAL (Src 65BB5200..., olean AC0BA608...).
- A6 F6 restatement S2839 ACTUAL.
