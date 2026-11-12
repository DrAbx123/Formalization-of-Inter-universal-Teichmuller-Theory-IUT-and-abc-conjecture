# HC3-LINKEVIDENCE — hC3 and finite link evidence in the S991/S994/S1004/S995 chain

Status: READ-ONLY audit, 2026-11-12. No compile.
Question: is hC3 : Oa.line.C3 = C3 definitional/easy from the construction of
Oa? Is there a green FiniteStepXILinkEvidence instance in S994/S1004/S995?

Short answer:
- hC3 is NOT rfl for an arbitrary Oa. It becomes rfl only for an explicitly
  constructed Oa whose line.C3 is definitionally C3; no such canonical
  constructor exists in the tree.
- No green FiniteStepXILinkEvidence instance is provided in S994/S1004/S995.
  S995 takes it as an argument. A green conditional builder exists:
  finiteLinkEvidenceOfHullTarget, but it needs a StepXIFiniteCertificate and
  supplied IPLSHEAPTEvidence (or arbitrary Props with proofs). The actual
  certificate is not constructed.

## 1. hC3 exact definition and source

S999HQHC3Actual.lean:
  def S999LineC3Identification : Prop := Oa.line.C3 = C3.
S991S983LinkInputsActual.lean uses hC3 exactly in this form:
  (hC3 : Oa.line.C3 = C3).

Structure PaperQPilotObjectActual (QPilotObjectActual.lean:154-162):
  line : QPilotLineActual (I := I)
  strip : SourceFTimesMuPrimeStrip V
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  logKummer : SourceLogKummerData I line.C1
  logKummer_eq : logKummer = line.C2
  oneZero : OneZeroPoint
  oneZero_eq : oneZero = oneZeroPoint

QPilotLineActual (same file:82-86):
  C1 : SourceInputBinding I
  C2 : SourceLogKummerData I C1
  C3 : SourcePilotRegionData (l := l) (V := V) I.

So Oa.line.C3 is an arbitrary field of an arbitrary QPilotLineActual. The
structure has no constructor taking C3 alone, and concreteO is a
PaperQPilotObject (not PaperQPilotObjectActual), not an Oa provider.

Consequences:
- For arbitrary Oa, hC3 is a genuine equality of two independently supplied
  SourcePilotRegionData values. Not rfl, not derivable from the fields.
- If one constructs Oa with line.C3 := C3 explicitly, then hC3 is rfl. A
  schematic constructor:

  noncomputable def actualOOfLine
      (L : QPilotLineActual (I := I))
      (strip : SourceFTimesMuPrimeStrip V)
      (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
      (oneZero : OneZeroPoint) : PaperQPilotObjectActual (I := I) := ...

  with L.C3 set to C3. Then
  theorem actualOOfLine_hC3 : (actualOOfLine ...).line.C3 = C3 := rfl.
  But this requires C1/C2/C3 and all other fields; it is a constructor
  obligation, not a theorem about an existing Oa.
- If an equality of lines Oa.line = L is available, then
  hC3 = congrArg (fun line => line.C3) hline.
  No such line equality is in the tree.

Verdict for hC3: GAP for arbitrary Oa; rfl only under an explicit construction
with line.C3 := C3. It is not a definitional consequence of the S991/S994
interfaces.

## 2. FiniteStepXILinkEvidence: exact structure

FiniteCertificateBridge.lean:17-27:
  structure FiniteStepXILinkEvidence (certificate : StepXIFiniteCertificate label) where
    targetSigned : Real
    ipl : Prop
    she : Prop
    apt : Prop
    ipl_evidence : ipl
    she_evidence : she
    apt_evidence : apt
    q_le_target : certificate.qSigned <= targetSigned
    target_le_theta : targetSigned <= certificate.thetaSigned.

The fields ipl/she/apt are arbitrary Props with proofs; no source propositions
are fixed by the structure. The two comparison fields are the substantive
arithmetic content.

Green builder (ContractSourceReduction.lean:210-223):
  def finiteLinkEvidenceOfHullTarget
      (certificate : StepXIFiniteCertificate label)
      (ipl she apt : Prop) (ipl_evidence : ipl)
      (she_evidence : she) (apt_evidence : apt) :
      FiniteStepXILinkEvidence certificate where
    targetSigned := certificate.hull.hullVolume
    q_le_target := certificate.q_le_hull
    target_le_theta := certificate.hull_le_theta.
This is green. It shows: once a certificate exists, the finite link's
comparison fields are automatic; only the certificate and arbitrary IPL/SHE/APT
evidence remain.

## 3. Instances in S994/S1004/S995

S994FiniteCarrierCor312Actual.lean:
- S994FiniteLinearization: qVFamTensorBlock ~ Fin d -> Qp via s996QVFamLinearization.
- s994H: finiteLogShellHaarData.
- s994QPilotImage = e '' qPilotPaperRegion; s994Hull = e '' paperRootThetaImageNZ.
- s994Containment: qPilot image <= hull image (green).
- S994PerBInput: linearization + qPilot_pos + hull_finite.
- s994PerBLogComparison: (positive/finite) log comparison.
- S994FiniteInput: per-b positivity/finiteness.
- s994GlobalWeightedInequality: weightedPaperV VR <= VS.
No FiniteStepXILinkEvidence is constructed here. It is the finite certificate
input side only.

S1004QVFamFiniteLinearizationActual.lean:
- s1004E, s1004QPilotImage, s1004Hull, s1004Containment.
- finiteNormalizedLog_mono_qvfam; s1004PerB.
No FiniteStepXILinkEvidence; only per-b qVFam comparison.

S995FiniteCarrierCor312ConclusionActual.lean:
  theorem s995FiniteCarrierCor312Conclusion
    (In : S994FiniteInput T)
    (link : PaperXiFSourceLink O P C3)
    (hlink : link.link_identification)
    (links : FiniteStepXILinkEvidence (paperCertificate ...).toStepXIFiniteCertificate)
    : ... Cor312Conclusion ...
  theorem s995Cor312Conclusion: same, projected.
Thus links is an explicit argument; neither S995 nor its imports produce an
instance. The finite link is assumed, not constructed.

Green conditional builders elsewhere (not S994/S1004/S995):
- S1044GlobalFiniteLinksActual.s1044FiniteLinks:
    hcomp + S1041GlobalQParameterCard + S1044IPLSHEAPTEvidence ->
    FiniteStepXILinkEvidence (s1041GlobalCertificate ...).
- S1054PaperFinalLinksActual.s1054FiniteLinks:
    S994FiniteInput + hullavg + S1051PaperQParameterCard + S1054IPLSHEAPTEvidence.
- S1093PaperAssemblyActual.s1093FiniteLinks:
    S1093PaperComparisonData + S1093IPLSHEAPTEvidence.
All call finiteLinkEvidenceOfHullTarget; all still require a certificate and
an IPLSHEAPTEvidence argument. None supplies an unconditional instance.

Conclusion on finite link:
- There is a green builder, but no green instance in the S994/S1004/S995 chain.
- The builder reduces the link fields to: certificate + arbitrary IPL/SHE/APT
  evidence. If the intended ipl/she/apt are specific source Props, their
  evidence is missing; if they are arbitrary, choosing True is formally
  possible but does not provide a source certificate.
- The real bottleneck remains the actual StepXIFiniteCertificate (hQ/hC3 and
  the source link), not the finite link fields.

## 4. Candidate Lean lemmas

hC3 from an explicit construction (schematic):
  noncomputable def actualOOfC3
      (L : QPilotLineActual (I := I)) (hL : L.C3 = C3)
      (strip oneColumn oneZero) : PaperQPilotObjectActual (I := I) := ...
  theorem actualOOfC3_hC3 ... : (actualOOfC3 ...).line.C3 = C3 := hL
or rfl if the line field is built with C3.

hC3 from line equality:
  theorem hC3_of_line_eq {L} (h : Oa.line = L) : Oa.line.C3 = L.C3 :=
    congrArg (fun line => line.C3) h

Finite link from certificate + evidence (already green):
  finiteLinkEvidenceOfHullTarget certificate ipl she apt ipl_evidence
    she_evidence apt_evidence

Specific source evidence (not green):
  structure IPLSHEAPTEvidence where ipl/she/apt : Prop; proofs ...
  def s99xFiniteLinks (certificate) (E : IPLSHEAPTEvidence) :
    FiniteStepXILinkEvidence certificate := finiteLinkEvidenceOfHullTarget ...

## 5. Exact remaining inputs and paths

hC3:
  path 1: construct Oa with line.C3 := C3 (rfl) — requires other Oa fields.
  path 2: prove Oa.line = concreteLine with C3 — no such equality.
  path 3: keep hC3 as an explicit source identification (current S991/S999).
  Status: GAP; not rfl for arbitrary Oa.

hQ:
  definition: (concreteO I).qPilotLogVolume = paperQPilotLogVolume C3.
  path: ConcreteSourceQIdentification / concreteO_qPilotLogVolume_eq_paper,
  but S999 notes its dependency ConcreteC3DonorActual fails compilation
  (universe/sorry warnings), so it is not used. hQ remains explicit.
  Status: GAP; explicit minimum.

finiteLinkEvidence:
  path: certificate + finiteLinkEvidenceOfHullTarget + IPL/SHE/APT evidence.
  No green instance in S994/S1004/S995. The comparison fields are free once a
  certificate exists; the certificate is the missing input.

positivity/finiteness:
  S994/S1004 already have per-b finite comparison conditional on
  S994FiniteInput (qPilot_pos + hull_finite). These are explicit inputs;
  S990 shows candidate sufficient conditions (interior/source unit-region
  inclusion) but they remain conditional.

## 6. Verdict

- hC3: not rfl/easy for an arbitrary Oa; genuine equality of C3 fields. rfl
  only for a purpose-built Oa with line.C3 := C3, which is a new construction.
- finiteLinkEvidence: green builder exists but no green instance in
  S994/S1004/S995; S995 takes links as a parameter. The only remaining content
  after a certificate is the IPL/SHE/APT evidence (or trivial Props, which
  would not supply source content).
- The S99x chain is genuinely close: S994/S1004 reduce the volume inequality
  to S994FiniteInput, and S995 reduces the final theorem to S994FiniteInput +
  link + hlink + finite links. The exact remaining inputs are hQ, hC3, the
  certificate/link, positivity, finiteness, and the finite link evidence, with
  the certificate/link being the main bottleneck.

No Lean file written; no compile claimed.