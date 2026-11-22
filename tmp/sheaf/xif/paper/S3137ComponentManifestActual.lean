import LeanFormal.IUT.Audit.Status

/-!
# S3137 component manifest: Stage-2 log-theta-lattice / log-shell / log-volume

Per TEAM-BRIEF section 8, every S3137 file is classified as a COMPONENT (not a
paper object) of a specific paper object, with its exact missing
identifications isolated, and a named future consumer.  This file records that
classification as audit metadata; it proves no inequality and constructs no
surrogate.  All listed Lean files are EXIT=0 with fresh oleans and axioms-trio
probes (see the named probe files).

Paper objects served: the [LGP-Gaussian] log-theta-lattice (IUT III, Def 1.4,
Def 3.8, (iii)), the Theta x mu LGP-link (Def 3.8, (ii)), the log-shell and its
log-volume (Def 1.1, Prop 1.2, Prop 3.9), and the q-pilot/Theta-pilot
comparison of Corollary 3.12 (corpus lines 10324--10353).
-/

namespace LeanFormal.IUT.Audit

/-- Component record: the literal oriented graph of the log-theta-lattice.
Component of IUT III, Def 1.4 / Def 3.8(iii); consumer: any lattice-level
construction (Def 3.8(iii); mainline Batch A sign bridge). -/
def s3137LogThetaLatticeSquareComponent : Obligation :=
  { id := "S3137.component.log-theta-lattice-square"
    source := "IUT III, Definition 1.4, pp. 45-46; Definition 3.8, (iii), pp. 113-114; Remark 1.4.1, (i), p. 46"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  Literal nodes/steps/path-endpoint graph, (1,0)/(0,1) path-word distinctness, index swap, actual square composites from the source link family, actual theta q/scale diagonal invariance.  The ring-structure non-commutativity of Remark 1.4.1(i) is NOT claimed (link record carries no ring structure); a general-path equality is not claimed (ill-typed without transport)."
    dependsOn := ["S3137LogThetaLatticeSquareActual", "S3137LogThetaLatticeSquareAxiomsProbe"] }

/-- Component record: the actual Theta x mu LGP arrow relative to the preceding full log-link. -/
def s3137ThetaXMuLGPRelativeComponent : Obligation :=
  { id := "S3137.component.theta-xmu-LGP-relative"
    source := "IUT III, Definition 3.8, (ii)-(iii), pp. 112-114; Remark 1.4.1, (ii), pp. 46-47"
    status := VerificationStatus.sourceProjection
    note := "COMPONENT, NOT PAPER OBJECT.  Actual preceding log-link and horizontal LGP arrow from the source link family, actual value-monoid/Galois/unit-group data with degree/projection/action compatibility, and the (0,0)-(1,1) intertwining square.  Exact Missing: the F^LGP x mu-prime-strip itself and the full poly-isomorphism of Def 3.8(ii) (Audit obligation IUT-III.theta-xmu-LGP-full-poly-isomorphism)."
    dependsOn := ["S3137ThetaXMuLGPRelativeActual", "S3137ThetaXMuLGPAxiomsProbe"] }

/-- Component record: actual log-shell Haar log-volume normalization. -/
def s3137LogShellHaarLogVolumeComponent : Obligation :=
  { id := "S3137.component.log-shell-haar-log-volume"
    source := "IUT III, Proposition 3.9, (i), p. 115; Proposition 1.2, (iii), p. 31"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  For the actual integral log-shell and actual integers: log mu(p . I_v) = log mu(I_v) - [K:Q_p] log p, the packet-normalization identity with the actual logShellIntegerIndex, and the [K:Q_p]=1 case -log p.  No hull normalization to the Theta-packet reading is claimed."
    dependsOn := ["S3137LogShellHaarLogVolumeScalingActual", "S3137LogVolumeAxiomsProbe"] }

/-- Component record: both Kummer images lie in the actual integral log-shell. -/
def s3137LogShellKummerImageComponent : Obligation :=
  { id := "S3137.component.log-shell-kummer-images"
    source := "IUT III, Proposition 1.2, (v), (bnon), (cnon), pp. 31-32; Remark 1.2.2, (i), (ii), p. 36"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  unitLog(O_K^x) subset actual integral log-shell (new; production had only the O_K side) and O_K subset shell."
    dependsOn := ["S3137LogShellKummerImageContainmentActual", "S3137KummerContainmentAxiomsProbe"] }

/-- Component record: log-shell-ready positions of the lattice. -/
def s3137LogShellReadyPositionsComponent : Obligation :=
  { id := "S3137.component.log-shell-ready-positions"
    source := "IUT III, Remark 1.4.1, (ii), pp. 46-47; Remark 3.8.3, p. 115"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  Log-shell-ready positions m>=1; (0,1),(1,1) ready, (0,0),(1,0) not; actual preceding full log-link at every ready node with actual q/scale invariance; comparison positions are vertical log-link targets."
    dependsOn := ["S3137LogThetaLatticeLogShellReadyActual", "S3137LogShellReadyAxiomsProbe"] }

/-- Component record: actual C3 tensor-block p-scaling and packet-normalized log-volume. -/
def s3137C3PacketLogVolumeComponent : Obligation :=
  { id := "S3137.component.C3-packet-normalized-log-volume"
    source := "IUT III, Proposition 3.9, (i), p. 115"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  Actual C3 tensor-block Haar p-scaling law, log form, region finiteness from compactness (positivity is the one ordinary hypothesis), and the packet-normalized log-volume shift -log p."
    dependsOn := ["S3137C3LogShellPacketNormalizedLogVolumeActual", "S3137C3LogVolumeAxiomsProbe"] }

/-- Component record: actual q-pilot and Theta-pilot log-volume readings on one C3 input. -/
def s3137PilotReadingsComponent : Obligation :=
  { id := "S3137.component.q-theta-pilot-readings"
    source := "IUT III, Definition 3.8, (i), p. 112; Proposition 3.9, (i), p. 115"
    status := VerificationStatus.sourceProjection
    note := "COMPONENT, NOT PAPER OBJECT.  q-pilot reading = actual paper q-pilot signed log-volume (-|log q|); Theta-side container = actual lambda-O hull of the actual C3 tensor log-shell region, proved equal to the region, with actual Haar log-volume reading.  Exact Missing: C3.q vs C3.thetaPacket source identification (IUT II Remark 2.5.1(i)); hull normalization to the Theta-packet reading."
    dependsOn := ["S3137QThetaPilotLogVolumeReadingsActual", "S3137QThetaReadingsAxiomsProbe"] }

/-- Component record: p-scaling of the actual Theta-hull reading. -/
def s3137ThetaHullScalingComponent : Obligation :=
  { id := "S3137.component.theta-hull-scaling"
    source := "IUT III, Proposition 3.9, (i), p. 115"
    status := VerificationStatus.provedKernel
    note := "COMPONENT, NOT PAPER OBJECT.  Actual hull container finite Haar measure, log mu(p . hull) = -[block:Q_p] log p + hullReading, and the candidate comparison rewritten as qReading <= actual C3 region log-volume."
    dependsOn := ["S3137ThetaHullVolumeScalingActual", "S3137ThetaHullScalingAxiomsProbe"] }

/-- Component record: Cor 3.12 comparison reduced to the same-C readout identification. -/
def s3137QThetaComparisonComponent : Obligation :=
  { id := "S3137.component.q-theta-comparison-reduction"
    source := "IUT III, Corollary 3.12, corpus lines 10324-10353; Step (xi-f)"
    status := VerificationStatus.conditional
    note := "COMPONENT, NOT PAPER OBJECT.  Pending residual exact; signed comparison and magnitude form proved from the same-C readout identification and mainline's unconditional paper-normalized comparison.  Residuals: two same-C readout equalities (IUT-III.native-to-C3-same-C-readout-identification), Q_p-spectral vs default-residue normalization (IUT-III.q-theta-paper-normalization-bridge)."
    dependsOn := ["S3137QThetaComparisonBridgeActual", "S3137NativeToC3SameCReadoutActual", "S3137QThetaBridgeAxiomsProbe", "S3137SameCIdentificationAxiomsProbe"] }

/-- Component record: LGP value-group refinement of the F^LGP x mu gap. -/
def s3137LGPValueGroupComponent : Obligation :=
  { id := "S3137.component.theta-xmu-LGP-value-group-refinement"
    source := "IUT III, Prop. 3.4, (ii), pp. 102-103; Prop. 3.7, (ii)-(v), pp. 108-112; Def. 3.8, (ii), pp. 112-113; IUT II, Cor. 4.8, (ii)"
    status := VerificationStatus.conditional
    note := "COMPONENT, NOT PAPER OBJECT.  Actual value-group/divisor side: total-exponent hom, single-prime law, label weight vs FiniteThetaPacket.log_scale, closed thetaPacket.logVolume form.  Exact Missing (LGPXMuMissingRefined): unit-group (x mu) portion, local LGP monoids/fractional ideals, Frobenioid isomorphisms, realified LGP presentation, full poly-isomorphism."
    dependsOn := ["S3137ThetaXMuLGPValueGroupRefinementActual", "S3136LGPPhiInputSourceActual", "S3136LGPXMuDegreeActual", "S3137LGPValueGroupAxiomsProbe"] }

end LeanFormal.IUT.Audit
