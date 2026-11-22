# C9 IUT bridge: amplitude and hull_le_theta

Task: task-475. Owner: qside. Date: 2026-10-25.
Bridge note using actual project declarations only; no toy fields; no
sorry or axiom except where an existing audit record documents a boundary.
No mixed/E3; only this file written.

## 0. Verdict

The project has no declaration named Amplitude.  The amplitude card is the
actual declaration CardAMPLThetaBoundSupply in
HolomorphicHull/CardAMPLThetaBoundSupply.lean.

The exact connection to the consumer hull_le_theta slot is:

  CardAMPLThetaBoundSupply.hull_logVolume_le
    -> realVolume_le
    -> certificate.hull_le_theta
    -> linkEvidence.target_le_theta
    -> StepXIContract.target_le_theta
    -> Cor312Conclusion.

This is an interface/certificate-level connection.  It is conditional on the
supply field hull_logVolume_le, which the project records as a discharge
obligation, not as a derived source amplitude.  No actual source
instantiation is constructed, and the value-level source route is recorded as
unsatisfiable under pointwise degree faithfulness.

No sorry or axiom occurs in the bridge files cited below.

## 1. Actual declarations

1.1 Amplitude card.

File HolomorphicHull/CardAMPLThetaBoundSupply.lean
SHA256 7EF3B7233A728299B256E08413777D0058EDE23C9DEB544BFD6344ECA23E08E4

Lines 78-84:

  structure CardAMPLThetaBoundSupply {X : Type u} (W : IQHullLogVolumeInterface X) where
    theta : Real
    theta_nonneg : 0 <= theta
    hull_logVolume_le : W.logVolume W.hull <= ENNReal.ofReal theta

The module doc lines 31-45 says the upper bound is supplied, never derived;
the fields are discharge obligations; no source instantiation is asserted;
and the value-level upper bound is unsatisfiable under pointwise degree
faithfulness.

Audit record cardAMPLThetaBoundSupply lines 214-241 has status
VerificationStatus.interface and notes: fields are discharge obligations, no
source instantiation constructed; NOT proved: a realization of the interface
and of the theta bound for the actual source carrier (Card-HULLREAL).

1.2 Interface.

File HolomorphicHull/SourceHullCompactnessReduction.lean
SHA256 61E0AA011F108F5A410F99AE2111F3E43C69C81FE76D3093F4A04693A3BF237D

IQHullLogVolumeInterface lines 52-81 has fields imageSet, hull,
imageSet_subset_hull, logVolume : Set X -> ENNReal, logVolume_mono,
unitRegion, scaleShift, hull_subset_scaleShift,
unitRegion_logVolume_lt_top, scaleShift_unitRegion_logVolume_le.

Its audit record lines 148-169 says this is conditional data, not the actual
IQ carrier.  So the Card-AMPL supply sits over a conditional interface.

1.3 Consumer certificate.

File HolomorphicHull/Volume.lean
SHA256 0AA5C1C90C92730F3EF2655CD3989E173558EBD224BEB6A740A06B87DBFD8FF4

StepXIFiniteCertificate lines 152-161 has fields:
hull, weighted, weighted_matches_hull, weights_nonnegative,
qSigned, thetaSigned, q_le_hull, hull_le_theta, q_negative.

The field hull_le_theta is the exact consumer slot.  The theorem
StepXIFiniteCertificate.q_le_theta lines 163-167 composes q_le_hull with
hull_le_theta.

1.4 Contract consumer.

File Contract.lean StepXI defines StepXIContract with qSigned, thetaSigned,
targetSigned, q_negative, ipl/she/apt and evidence, q_le_target,
target_le_theta.  Cor312Conclusion contract is qSigned <= thetaSigned.
cor312_of_constructed_stepXI composes q_le_target and target_le_theta.

File FiniteCertificateBridge.lean
SHA256 4C28F1AEC0AC4034FF8464248DDA1CC343803398867AAB2FDADA3AB8B1A805C3

StepXIFiniteCertificate.toContract fills the contract and delegates
targetSigned/q_le_target/target_le_theta to FiniteStepXILinkEvidence.
cor312_of_finite_certificate then gives Cor312Conclusion.

## 2. Exact bridge chain

2.1 Interface-level amplitude to real bound.

CardAMPLThetaBoundSupply.realVolume_le lines 94-96:

  theorem realVolume_le (S : CardAMPLThetaBoundSupply W) :
      iqHullRealVolume W <= S.theta :=
    (iqHullRealVolume_le_theta_iff W (theta := S.theta) S.theta_nonneg).mpr
      S.hull_logVolume_le

This uses the actual equivalence iqHullRealVolume_le_theta_iff in
CertificateHullWiring.lean lines 106-114: ENNReal upper bound iff real upper
bound.

2.2 Certificate generation.

CardAMPLThetaBoundSupply.certificate lines 149-157 calls the actual
iqHullCertificate with theta = S.theta, hTheta = S.hull_logVolume_le,
hTheta0 = S.theta_nonneg, and the lower-side q/hq/hqneg.

iqHullCertificate in CertificateHullWiring.lean lines 155-174 constructs a
StepXIFiniteCertificate and sets

  hull_le_theta := toReal_le_of_le_ofReal hTheta0 hTheta.

Thus the amplitude field becomes exactly the certificate hull_le_theta field.

2.3 thetaSigned identity.

CardAMPLThetaBoundSupply.certificate_thetaSigned lines 161-167 proves

  (S.certificate ...).thetaSigned = S.theta.

This records that the amplitude constant occupies the consumer theta slot.

2.4 Link evidence target_le_theta.

CardAMPLThetaBoundSupply.linkEvidence lines 172-188 sets:
targetSigned := iqHullRealVolume W
target_le_theta := (S.certificate ...).hull_le_theta
q_le_target := (S.certificate ...).q_le_hull.

The q_le_hull side comes from hq : ofReal q <= W.logVolume W.imageSet,
W.imageSet_subset_hull, W.logVolume_mono, and ofReal_le_toReal_of_ne_top;
see iqHullCertificate lines 169-173.

2.5 Contract and conclusion.

linkEvidence fills FiniteStepXILinkEvidence.target_le_theta;
StepXIFiniteCertificate.toContract copies it into StepXIContract.target_le_theta;
cor312_of_finite_certificate / cor312_of_constructed_stepXI gives the ordered
conclusion.  CardAMPLThetaBoundSupply.cor312Conclusion lines 193-203 is
exactly this composition.

## 3. What the bridge is and is not

Is:
- actual interface IQHullLogVolumeInterface;
- actual named supply CardAMPLThetaBoundSupply with amplitude constant and
  hull upper-bound field;
- actual realVolume_le connecting ENNReal field to real field;
- actual certificate / linkEvidence / cor312Conclusion consumer alignment;
- actual StepXIFiniteCertificate.hull_le_theta and
  StepXIContract.target_le_theta;
- no sorry/axiom in CardAMPLThetaBoundSupply.lean or
  CertificateHullWiring.lean (grep clean).

Is not:
- not a derivation of the amplitude upper bound from IUT III source data;
  hull_logVolume_le is a field/discharge obligation; audit status interface;
- not an actual realization of IQHullLogVolumeInterface by the paper IQ
  carrier; SourceHullCompactnessReduction records this as not proved;
- not the value-level source bridge: under pointwise degree faithfulness,
  sourceThetaBound_unsat_of_degreeFaithful in CertificateHullWiring.lean
  lines 299-309 proves there is no real theta upper bound of the
  value-realized hull;
- not a construction of the complete C or P6; the contract audit remains
  pending with no source-facing construction.

## 4. No toy fields

The bridge uses only the actual interface, the actual named supply, the
actual certificate/link/contract declarations, and the actual proofs.
The one-point witness singletonRealWitness/singletonRealSupply is a
non-vacuity check in the source file and is not used in this bridge chain.
No arbitrary toy carrier or free amplitude is substituted.

## 5. Exact gap

The bridge closes the interface-level composition:

  CardAMPLThetaBoundSupply.hull_logVolume_le
    => StepXIFiniteCertificate.hull_le_theta
    => StepXIContract.target_le_theta
    => Cor312Conclusion.

The remaining exact gap is source instantiation:
G1 realization of IQHullLogVolumeInterface by the actual IQ(S+-...; ..., ...)
   carrier;
G2 amplitude bound W.logVolume W.hull <= ofReal theta for that actual carrier,
   i.e. discharge of CardAMPLThetaBoundSupply.hull_logVolume_le;
G3 lower-side q/image bound ofReal q <= W.logVolume W.imageSet and q<0 for the
   actual source data;
G4 IPL/SHE/APT evidence for the actual source;
G5 higher Step-XI/Card-HULLREAL assembly.

These are the project recorded interface/audit boundaries, not missing algebra
in the bridge.

## 6. Classification

PROVED/ACTUAL DECLARATIONS:
- CardAMPLThetaBoundSupply; realVolume_le; certificate_thetaSigned;
  certificate; linkEvidence; cor312Conclusion.
- CertificateHullWiring iqHullRealVolume_le_theta_iff; iqHullCertificate;
  iqHullLinkEvidence; iqHullCor312Conclusion.
- StepXIFiniteCertificate.hull_le_theta; StepXIContract.target_le_theta;
  Cor312Conclusion.
- No sorry/axiom in the cited bridge files.

CONDITIONAL/INTERFACE:
- IQHullLogVolumeInterface realization.
- CardAMPLThetaBoundSupply fields theta, theta_nonneg, hull_logVolume_le.
- q/image lower bound, q<0, IPL/SHE/APT evidence.
- Source value-level bridge; degree-faithfulness obstruction recorded.

NOT PROVED:
- actual source carrier realization;
- actual amplitude/upper bound for the source hull;
- complete C/P6 from this bridge.

## 7. Conclusion

The amplitude/hull_le_theta connection is exact at the actual project
interface/certificate level:

  Card-AMPL supply field -> realVolume_le -> certificate.hull_le_theta
  -> linkEvidence.target_le_theta -> StepXIContract.target_le_theta
  -> Cor312Conclusion.

It is not a source derivation of amplitude; hull_logVolume_le is an explicit
discharge obligation.  The actual source carrier and its amplitude remain the
recorded Card-HULLREAL/source gap.  No toy fields, no sorry/axiom in the
bridge files, no mixed/E3.

target_accepted=false.

## 8. Sources

- HolomorphicHull/CardAMPLThetaBoundSupply.lean
  SHA256 7EF3B7233A728299B256E08413777D0058EDE23C9DEB544BFD6344ECA23E08E4.
- CertificateHullWiring.lean
  SHA256 FEF2CA985A7010A77B768426FF661DFA3021B621980B14D5202674110C95191A.
- HolomorphicHull/Volume.lean
  SHA256 0AA5C1C90C92730F3EF2655CD3989E173558EBD224BEB6A740A06B87DBFD8FF4.
- FiniteCertificateBridge.lean
  SHA256 4C28F1AEC0AC4034FF8464248DDA1CC343803398867AAB2FDADA3AB8B1A805C3.
- HolomorphicHull/SourceHullCompactnessReduction.lean
  SHA256 61E0AA011F108F5A410F99AE2111F3E43C69C81FE76D3093F4A04693A3BF237D.
- Contract.lean StepXI (StepXIContract, Cor312Conclusion).
