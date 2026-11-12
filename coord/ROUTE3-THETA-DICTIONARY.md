# ROUTE3-THETA-DICTIONARY — IUT II Remark 2.5.1 source-label dictionary gate

Task: task-81 (R29-stepxi). Status: audit/construction assessment; no repo source edit.
Snapshot: 2026-11-13T03:58:39+08:00 Asia/Shanghai (task time), audit run after.
Deliverable: this file. Scope is the route-three first semantic gate, not a proof of
Corollary 3.12.

## 0. Verdict in one paragraph

The route-three dictionary can be built only at the ROOT-UNIT / mu2l-ORBIT level:
the actual Lean object paperRootThetaUnit is q_v^(j^2) with q_v a chosen 2l-th root
of the actual q parameter, and its independent mu2l orbit is already constructed.
A compiled probe (thetaRootDictionary, see section 4) confirms this construction.
However, the full paper dictionary 'source label j -> actual etale theta value
theta_j(Pi_v-triangle)' is NOT constructed: the root unit is not identified with the
etale theta evaluation/Kummer class, and no such identification exists in the tree.
Therefore the semantic gate is PARTIALLY passed: root-unit dictionary YES, full
actual-theta-value dictionary NO. The q-parameter packet FiniteThetaPacket.scale =
q^(j^2) must not be used as paper theta; paper theta is the root-valued object.

## 1. HANDOFF fact correction: which sections are actually missing

File: D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md (33131 bytes).
The task premise says the body ends at section 5.13 and sections 6-12 are missing.
That is not what the file contains:
- TOC at line 18 lists 12 sections;
- actual H2 headings: section 6 at line 813, section 7 at line 1247;
- section 6.2 (the exact dictionary gate) IS PRESENT at lines 828-858;
- the file ends after section 7.6/7.7 (about line 1354); sections 8-12 are absent.

So the correct statement is: sections 6-7 are present; sections 8-12 are missing.
Impact: the route-three semantic requirement is not lost; section 6.2 gives the
authoritative seven-field dictionary checklist. What is missing is the promised
task-pack/dependency/interface/acceptance material (TOC sections 8-12), so no
route-three implementation schedule or comparator acceptance can be taken from
HANDOFF; those must be reconstructed separately. This does not block the dictionary
check itself.

## 2. Paper source: IUT II Remark 2.5.1 and dependencies

Primary file: D:/lean/papers/motizuki_corpus/text/Inter-universal Teichmuller Theory II.txt
(OCR text; line numbers below are file lines).

- Remark 2.5.1 begins at line 4272 and ends before Remark 2.5.2 at line 4344.
- (i) lines 4272-4288: for j in |F_l|, the set theta_j(Pi_v-triangle) consists
  precisely of the mu2l-orbit of the theta value q_v^(j^2); the exponent 'j'
  denotes the element of {0,1,...,l*} determined by the given j in |F_l|.
  References: [IUTchI], Example 3.2(iv); [EtTh], Proposition 1.4(ii).
- (ii) lines 4291-4321: the reciprocals of the l-th powers of these theta values
  correspond to Theta(+-sqrt(-1)*q_X^(j/2)), j in {0,1,...,l*}; the values are
  separated by periods q_X^(j/2) from +-sqrt(-1), and are computed from the
  functional equations of [EtTh], Proposition 1.4, (ii). This is the precise
  'special value' content; it is not an arbitrary jP evaluation.
- (iii) lines 4322-4343: the mu2l indeterminacies for different j are INDEPENDENT;
  they are not synchronized to a single phase independent of j.

Dependency definitions:
- IUT II Corollary 2.5, (ii), lines 4170-4227: defines the restriction of the
  etale theta functions to Pi_v-triangle, the sets theta_t(Pi_v-triangle), their
  mu2l- and mu-orbits, and writes theta_{|t|}; the sets depend only on the label
  |t| in |F_l| (lines 4215-4227).
- IUT I Example 3.2(iv), file .../Inter-universal Teichmuller Theory I.txt,
  lines 3701-3726: q_v is first the q-parameter, then q_v := q^(1/2l) at
  lines 3711-3719; this root is determined only up to a mu2l(T_X)-multiple
  (lines 3716-3726). The paper's q_v power in Remark 2.5.1 therefore uses the
  root, not the unrooted q-parameter.
- Additional references in the remark: [IUTchI] Example 4.4(i), Corollary 2.3(vi),
  Definition 6.1(iii) for |t|; [EtTh] Proposition 1.4(ii); Kummer map
  K_v^x -> H^1(G_v(Pi_v-triangle),(l*Delta_Theta)(Pi_v-triangle)).

Section 6.2 of HANDOFF lines 828-858 already translates this into the seven fields:
curve/cover, parameter q_v/q_X/root/field, label meaning (point/period/torsion/orbit),
section type (function/line-bundle section/power/reciprocal), scale constants,
mu2l indeterminacy, and the target norm/valuation/determinant reading.

## 3. Our actual Lean objects: what exists and what they mean

### 3.1 Source geometry and q unit
File: tmp/sheaf/xif/paper/PaperSourceGeometryActual.lean:78-87.
  structure CompletionValuedSourceGeometry where
    place : V -> FinitePlaceAtPrime K p
    qUnit : (v : V) -> CompletionValueCarrier (place v)
    thetaPacket : FiniteThetaPacket l
    thetaPacket_q_eq : forall v, thetaPacket.q = norm (qUnit v).
qUnit is the actual q-parameter unit, not a root. thetaPacket is a finite real
packet whose q is the norm of qUnit.

### 3.2 Root-valued paper theta (the correct object)
File: tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean.
- RootExtension v := AlgebraicClosure (CommonPrimeCompletion (place v)) (lines 35-36).
- twoLthRootAt v is a chosen 2l-th root of qUnit in the algebraic closure
  (lines 48-50); theorem twoLthRootAt_pow (lines 52-58).
- paperRootThetaUnit j v := twoLthRootAt v ^ (gaussExponent j.1).toNat
  (lines 61-64), with Gaussian exponent = j^2 (GaussianKernel.lean:23).
- theorem paperRootThetaUnit_pow_twoL (lines 66-72):
  paperRootThetaUnit^(2l) = unitToAlgClosed(qUnit)^(j^2).
- ThetaLabel := positive representatives 0 < j.1 of SignedLabel (line 82);
  thetaLabelToSigned (line 85); paperRootThetaImagePointTheta (lines 109-116).
This is exactly q_v^(j^2) with q_v the chosen root, up to the usual mu2l root
choice. It is the root-valued object, not the q-parameter power.

### 3.3 q-parameter power is explicitly not paper theta
File: tmp/sheaf/xif/paper/PaperC3ThetaValuesActual.lean:1-25.
  The header states: qParameter_j = q^(j^2) are NOT paper theta values;
  paper theta uses the double-underline q_v=q^(1/2l): theta_j=q_v^(j^2).
- paperQParameterThetaValue j v = qUnit^(j^2) (lines 34-39).
- Mu2lRoot/mu2lAction/paperQParameterMu2lOrbit (lines 41-100) construct the
  independent mu2l action, not a paper theta value.
File: tmp/sheaf/xif/paper/PaperThetaNamingActual.lean:1-31 repeats: single-underline
q_v is the q-parameter power (not paper theta); double-underline q_v is the 2l-th
root; paperRootThetaUnit is paper theta.

### 3.4 mu2l orbit/hull and primitive phase
File: tmp/sheaf/xif/paper/PaperC3RootThetaHullActual.lean:1-90.
- paperRootThetaMuPoint m j (lines 34-39): zeta^m * paperRootThetaUnit j.
- paperRootThetaMuOrbit j (lines 41-46); paperRootThetaHull (lines 49-53).
- RootThetaHullLogComparison remains an explicit structure/Prop (lines 77-83),
  not constructed.
File: tmp/sheaf/xif/paper/PaperC3PrimitiveMu2lRootActual.lean:1-60 constructs an
actual primitive 2l-th root of unity in the algebraic closure, so the independent
mu2l phases are available.

### 3.5 Source real-scalar theta packet and its root gap
File: tmp/sheaf/xif/paper/PaperSourceThetaConsistencyActual.lean.
- sourceQVFamilyUnit (lines 47-55), sourceThetaQ = norm of q unit (lines 58-62).
- sourceThetaPacketFromQ = FiniteThetaPacket.ofQ (norm qUnit) (lines 70-72).
- sourceThetaPacketFromQ_scale j = sourceThetaQ^(j^2) (lines 78-80).
  This is the q-parameter power q^(j^2), NOT q_v^(j^2).
- PaperThetaRootGap (lines 95-130) records exactly: root in normalized completion
  (open) vs root in algebraic closure (available); no completion root is asserted.
File: tmp/sheaf/xif/paper/PaperC3SourceDataQConsistencyActual.lean:73-100.
- sourceQRootUnit is the 2l-th root in the algebraic closure (lines 73-90).
- sourcePaperRootThetaUnit uses exponent (gaussExponent j.1).toNat ^ 2
  (lines 93-100). Since gaussExponent j = j^2, this is (j^2)^2 = j^4, not j^2.
  This is an observed code-level mismatch; it is not used by the actual root
  line paperRootThetaUnit and must be corrected/avoided before use.

### 3.6 Analytic theta and missing etale/Kummer identification
File: LeanFormal/IUT/IUTII/Frobenioid/Example36SourceThetaDivisor.lean.
- thetaUnit t j = realThetaValue t.q j = q^(j^2) (lines 57-64, 468);
  thetaRootValue r j = r^(j^2) if r^(2l)=q (lines 69-76, 511-519).
- Explicit missing list lines 97-119:
  (a) two-sided nonarchimedean odd theta series;
  (b) shift law and nonvanishing at i (EtTh Prop 1.4(ii));
  (c) meromorphic continuation and divisor on the Tate curve;
  (d) identification of Kummer classes of Prop 1.3 with theta values, i.e. the
      actual etale theta function (EtTh Prop 1.4(iii)), plus line-bundle section
      and nontrivial Theta-link.
Thus finite real theta values and root values exist; the etale theta evaluation
is explicitly not constructed.

### 3.7 Root card and mu2l ratio
File: LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceQParameterUniformization.lean.
- QParameterTwoLRootCard (lines 196-202): a root in the completion with root^2l=q;
  an instance is genuine Kummer input, not constructed from arithmetic data.
- twoLRoot_ratio_pow_eq_one / twoLRootUnit_ratio_mem_rootsOfUnity (lines 177-189):
  any two roots differ by a mu2l element.
- root in algebraic closure is available; descent to the completion remains open
  (header lines 36-43).

## 4. Construction draft: root-unit mu2l dictionary (COMPILED)

Draft file (outside repo source): D:/iut-audit-20261113/probe_theta_dictionary2.lean.
It imports PaperC3RootThetaHullActual and PaperThetaNamingActual and defines:

  namespace ThetaDictionaryProbe
  variable (G : CompletionValuedSourceGeometry ...)
  noncomputable def thetaRootDictionary :
      ThetaLabel -> Set (RootThetaCarrier G) :=
    fun j => paperRootThetaMuOrbit G j
  theorem thetaRootDictionary_mem (j : ThetaLabel) :
      paperRootThetaImagePointTheta G j ∈ thetaRootDictionary G j

Build evidence:
  command: lake env lean D:/iut-audit-20261113/probe_theta_dictionary2.lean
  exit code: 0 (no sorry/axiom introduced; both checks elaborated).
The same probe #checks paperRootThetaUnit, paperRootThetaUnit_pow_twoL,
paperRootThetaImagePointTheta, sourceThetaPacketFromQ_scale,
sourcePaperRootThetaUnit, paperTheta, sourceQRootUnit_pow.

Meaning: at each place v, label j in ThetaLabel is mapped to the independent
mu2l orbit of q_v^(j^2), with q_v a chosen root of qUnit. This is a real
construction from the existing root/carrier objects, not a point evaluation
jP on an abstract elliptic curve. It is the maximal dictionary currently
constructible without fabrication.

## 5. Acceptance judgment

### 5.1 What CAN be built

A root-unit / mu2l-orbit dictionary:
  ThetaLabel -> Set (RootThetaCarrier G), j |-> paperRootThetaMuOrbit j,
with:
- q_v^(j^2) and paperRootThetaUnit_pow_twoL;
- independent mu2l orbits (paperRootThetaMuOrbit; primitive 2l root);
- label canonical positive representatives 1..l*;
- per-place actual qUnit and algebraic-closure root.
This is already assembled from green declarations and compiles (section 4).

### 5.2 What CANNOT be built now

The full 'source label -> actual special theta value' dictionary in the sense of
IUT II Remark 2.5.1 / Corollary 2.5(ii), i.e. a map
  j |-> theta_j(Pi_v-triangle) (mu2l orbit in the Kummer H^1)
is not constructible. Exact gaps:

G1. No etale theta evaluation/Kummer-class identification:
    Example36SourceThetaDivisor.lean:97-119, especially (d) lines 112-115;
    FiniteThetaPacket.lean:8-17 says it does not identify with etale theta;
    PaperC3ThetaRootActual.lean:4-11 says etale theta function/Hodge-Arakelov
    comparison are not assumed.
G2. Root unit vs line-bundle section: paper theta is a section/cohomology class;
    our paperRootThetaUnit is a unit in AlgebraicClosure; no comparison map.
G3. Completion descent: root in algebraic closure exists, root in normalized
    completion is open (PaperSourceThetaConsistencyActual.lean:36-43, 95-130).
G4. The source real packet scale is q^(j^2) = (q_v^(j^2))^(2l), not q_v^(j^2);
    it cannot replace paper theta (PaperSourceThetaConsistencyActual.lean:70-80).
G5. sourcePaperRootThetaUnit uses exponent (gaussExponent j)^2 = j^4
    (PaperC3SourceDataQConsistencyActual.lean:93-100); observed mismatch,
    not used by paperRootThetaUnit but must not enter the dictionary.
G6. Global q_X/period relation of Remark 2.5.1(ii) is not formalized; the
    values Theta(+-sqrt(-1) q_X^(j/2)) are not constructed.
G7. Target reading: which norm/valuation/determinant enters l_Theta is not
    identified with the root-unit hull (RootThetaHullLogComparison is a Prop,
    PaperC3RootThetaHullActual.lean:77-83).

### 5.3 Do not do

- Do not replace label j by an arbitrary jP on a general elliptic curve
  (HANDOFF section 6.2 lines 838-844; Remark 2.5.1(i)).
- Do not use FiniteThetaPacket.scale or sourceThetaPacketFromQ as paper theta;
  that is the q-parameter power, not q_v^(j^2).
- Do not identify sourcePaperRootThetaUnit (j^4 exponent) with paperRootThetaUnit.
- Do not collapse the independent mu2l phases to one global phase
  (Remark 2.5.1(iii), lines 4322-4343).

## 6. Route-three status and missing HANDOFF sections

Semantic gate: PARTIAL.
- Root-unit dictionary: constructible and compiled.
- Full etale theta-value dictionary: not constructible; route three's first
  acceptance item is not fully passed. Any route-three calculation that consumes
  a 'theta value' must specify whether it means the root unit (available) or the
  etale Kummer class (missing), and must carry the independent mu2l phases.

HANDOFF sections: the file contains sections 1-7, including 6.2; only 8-12 are
missing. The missing sections would have supplied task packs, dependency/order and
acceptance records; their absence does not remove the 6.2 dictionary requirement,
but means route-three cannot claim an implementation schedule or comparator gate
from HANDOFF. The dictionary gap G1 above remains the primary blocker.

## 7. Build evidence summary
- Probe 1: D:/iut-audit-20261113/probe_theta_dictionary.lean, lake env lean, exit 0;
  #checks the root theta/packet/naming declarations.
- Probe 2: D:/iut-audit-20261113/probe_theta_dictionary2.lean, lake env lean, exit 0;
  defines thetaRootDictionary and proves membership.
- No repository source file was modified; only audit/probe files under
  D:/iut-audit-20261113 and this coord document.

End of report.