# SOURCELINK-ATTACK (A1129)

Status: read-only; no compile.

## 1. PaperXiFSourceLink fields

tmp/sheaf/xif/PaperXiFInclusion.lean:90-104:
structure PaperXiFSourceLink O P C3 where
  source_identifications :
    O.paper_strip_identification and O.paper_lineBundle_identification and
    O.paper_logKummer_identification and O.paper_qPilot_log_identification
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  link_identification : Prop
  link_implies_inclusion : link_identification ->
    O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume

PaperXiFInclusion (lines 106-113) is
  link : PaperXiFSourceLink O P C3
  link_holds : link.link_identification.
Thus the source link structure does NOT require a proof of link_identification;
the inclusion structure DOES.

## 2. Actual providers

### 2.1 thetaSourceComparison

ThetaLinkFromSource.lean:61-72:
def sourceComparison O P : Prop := P.procession.average <= -O.signedQPilotLogVolume.
abbrev thetaSourceComparison O P : Prop := same.
This is a DEFINITION of the missing comparison, not a theorem. There is no
inhabitant in the tree.

### 2.2 actualThetaLink

ThetaLinkFromSource.lean:110-141:
structure ActualThetaLink O P where
  link_identification : Prop
  link_implies_inclusion : link_identification ->
    O.signedQPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume.

def actualThetaLink O P : ActualThetaLink O P where
  link_identification := thetaSourceComparison O P
  link_implies_inclusion := xiFMembership_of_sourceComparison O P.

The definition is green. link_identification is the unproved comparison;
link_implies_inclusion is PROVED (xiFMembership_of_sourceComparison).
So actualThetaLink is a green wrapper, not a green inhabitant of the comparison.

### 2.3 S983 constructor

S983:48-64: paperXiFSourceLinkOfActualTheta takes
- hident : the four source identifications;
- hqpaper : O.qPilotLogVolume = paperQPilotLogVolume C3;
- hq : O.qPilotLogVolume = Oa.signedQPilotLogVolume;
and builds PaperXiFSourceLink with
  link_identification := (actualThetaLink Oa P).link_identification
  link_implies_inclusion := transport of (actualThetaLink Oa P).link_implies_inclusion
    along hq.
This is green conditional on the inputs. It does NOT prove
Oa's / O's link_identification; it only packages the implication.
S983:67-77 proves the identification field equals thetaSourceComparison Oa P (rfl).

### 2.4 S991 filling

S991:44-79:
- s991SourceIdentifications: actual via S622 concrete_source_identifications;
- s991SignedQIdentification: actual from QPilotScalarIdentification given
  hC3 : Oa.line.C3 = C3 and hQ : concreteO.qPilotLogVolume = paperQPilotLogVolume C3;
- s991LinkInputs: S983LinkInputs filled with those;
- s991PaperXiFSourceLink: PaperXiFSourceLink for concreteO, conditional only on
  hC3 and hQ.
Again the link_identification is the unproved thetaSourceComparison.

## 3. Is link_implies_inclusion green?

Yes as a function: xiFMembership_of_sourceComparison / concreteMembership_of_sourceComparison
prove
  comparison -> membership in signed hull ray.
But to get the membership one must apply it to an inhabitant of the comparison,
which is not provided. So link_implies_inclusion is green conditional on
link_identification, exactly as its type says.

## 4. Remaining gaps

To obtain PaperXiFInclusion (not merely the source link structure):
1. hQ : (concreteO l I).qPilotLogVolume = paperQPilotLogVolume C3;
2. hC3 : Oa.line.C3 = C3;
3. a proof of thetaSourceComparison Oa P (equivalently
   P.procession.average <= -Oa.signedQPilotLogVolume);
4. source_identifications for the concrete object are green (S622).
The only mathematical missing item is (3); (1) is the concrete source-q
identification, (2) is a carrier/line identification. S991 keeps (1),(2) as exact
inputs.

## 5. Verdict

- actualThetaLink is a green definition; its link_identification is the unproved
thetaSourceComparison, its link_implies_inclusion is proved.
- S983/S991 can assemble PaperXiFSourceLink conditional on hident, hqpaper, hq;
S991 reduces to hC3 and hQ.
- No green inhabitant of link_identification exists. Therefore PaperXiFInclusion
(which needs link_holds) cannot be assembled directly; it needs hQ, hC3 and a
proof of thetaSourceComparison.
- The concrete route ConcreteCor312Conclusion likewise takes
UnconditionalSourceComparisonObstacle as an explicit input.
- No fake link field; the missing piece is exactly the paper source comparison.
