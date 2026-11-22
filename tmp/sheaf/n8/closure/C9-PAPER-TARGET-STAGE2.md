# C9 paper target stage-2 design (pending Lean implementation)

Source: C9-PAPER-AUDIT-STAGE1.md; IUT III 10326-10358, 10843-10898.
Not a Lean proof claim; exact target design before implementation.

## Objects

1. QPaper
- qPilotRegion : Set (ThetaPilotPoint v) from the actual q-pilot object at (1,0) on 1,circ U_Q.
- qPilotLogVolume : WithTop Real (paper value in R ∪ {+inf}).
- provenance: Kummer-relative, procession-normalized; NOT subject to Ind1/2/3.
- required donors: actual qPilotRegion + qPilotLogVolume construction; current possibleThetaPilotImageSet is the wrong region.

2. ThetaPaper
- thetaHull : Submonoid/Set of ThetaPilotPoint v = holomorphic hull of union of possible Theta-pilot images.
- thetaLogVolume : WithTop Real; procession-normalized, Kummer-relative; subject to Ind1/2/3.
- required donors: normalized Kummer-relative log-volume plus actual Ind operations; raw sourceRealHullVolume is insufficient.

3. ValuesPaper
- Set of signed normalized log-volumes of actual pilot-object output data after construction/hull/determinant/normalization.
- membership carries provenance witness; not point log-degrees, not Set.Iic ThetaPaper.

4. Direction
- Prove: QPaper ∈ R^{<= ThetaPaper}, hence QPaper <= ThetaPaper, matching 10895-10896.
- Do not use MissingSourceQHullComparison as input; it is the conclusion.

## +inf / archimedean

Keep WithTop Real; do not collapse top via toReal. Separate archimedean source branch.

## Implementation order

1. Define exact stage-2 types for QPaper/ThetaPaper/ValuesPaper (no arbitrary Type/True).
2. Construct qPilotRegion/qPilotLogVolume from actual source q donor, or named theorem-level sorry with exact type.
3. Construct ThetaPaper normalized/Kummer/Ind datum, or named sorry.
4. Construct ValuesPaper from actual output regions, or named sorry.
5. Prove inclusion/direction; compile.

## Status

Old C9Native/C9Proof targets superseded; their named sorries are not valid C9 closure evidence.
## Audit correction (C9ValuesPaper)

`C9ValuesPaper.PilotObjectOutput` carries a free `value : Real` field. This is NOT a valid definition of paper Values: any real can be assigned, and the "provenance" witness does not constrain the value. The file must not be counted as C9 ValuesPaper progress. A valid target needs an actual computation map from C4 output data/witness to a signed normalized log-volume (e.g. via an actual U->IQ/normalization map), or a named theorem-level donor for that map; a free value field is rejected.

## Audit correction (C9Paper.lean)

C9Paper stage2 currently has unconstrained fields: qPilotRegion/qPilotLogVolume/thetaHull/thetaLogVolume/values/provenance. Its `qPaper_nonempty`/`thetaPaper_nonempty`/`valuesPaper_nonempty` only assert inhabitants of arbitrary structures, not paper objects. Rejected as valid stage2 until the fields are constrained by actual source objects (q scalar/region, source hull/possible images, provenance-to-value normalization). The named obligations are not C9 closure evidence.
