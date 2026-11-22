# C2 — Source log-Kummer realization: SHEAF stage-1 record

Task ID / group / owner / date: C2 / N8 closure / primespine / 2026-10-22
Goal node / SHEAF stage: C2 SourceLogKummerRealization / stage 1 only.
Files: write tmp/sheaf/n8/closure/C2-STAGE1.md (this file). No Lean file is written or changed.
Integration/build owner: C2 owner; C10 integrator later. Build not applicable to this document.
Shared interfaces/conflicts: C0 allowed input l,V,I : OriginalInput; C1 SourceInputBindingData (to define) is the planning dependency for actual places/completions. Do not edit C0/C1 files. C2 consumers are C4, C5, C9, C10.
Continuation: after stage-1 review, C2 stage 2 statement for the actual local log datum at finite places; C1 stage 2 place binding is a separate node.
Acceptance: stage-1 record only; no Lean compile, no proof claim.

## 1. Mathematical target (objects, quantifiers, hypotheses)

For each allowed input

    l : PrimeGeFive
    V : Type uv
    I : OriginalInput.{u, uv, upi, umon, ui} l V

and each actual finite-place binding supplied by C1:

    v : V
    p : Nat, the residue characteristic at v
    K_v := the actual completion at v (CommonPrimeCompletion / NumberField completion)
    O_v := Integers K_v
    U_v := (O_v)^x
    k_v := residue field

construct the actual local log-Kummer data for v:

1. Actual local log
       log_v : U_v -> Multiplicative K_v
   equal to the constructed unitLog / completionUnitLog at the actual completion,
   not an arbitrary monoid hom.

2. Kernel and image
       T_v := ker(log_v)
       L_v := image(log_v)
   with the exact sequence 1 -> T_v -> U_v -> L_v -> 1. Prove:
       log_v u = 0 iff u is torsion (IsOfFinOrder u);
       the induced map U_v/T_v -> L_v is injective (indeed an equivalence onto
       the range).

3. Principal units
       P_v := principalUnits (K := K_v) = {u : U_v | ||u.val - 1|| < 1}
   with open-subgroup and finite-quotient properties, the uniform exponent
   property, and log_v(P_v) subset L_v (the logarithm on principal units).

4. Kummer arrow
   An actual Kummer map/root-change construction from P_v (or from the actual
   p-power roots in U_v) to the local log/Kummer carrier, compatible with log_v,
   p-star scaling and the actual completion. This must be a source construction,
   not an arbitrary LabelledKummerIso or free bijection.

5. Action descent
   For the actual G_v(†Pi_v)-action on local units/invariant submonoid:
       invariants_v := the actual invariant submonoid of U_v;
       preLogShell_v := log_v(invariants_v) in additive coordinates;
       logShell_v := (p*_v)^(-1) preLogShell_v.
   Prove the invariant submonoid maps into the log-shell, and prove the action
   descent: log/Kummer-compatible maps factor through the kernel and invariants
   as the source requires. The generic quotient criterion descends_iff may be
   used only for the quotient-by-kernel step; it is not the source action
   descent and not a K1/K2 realization.

6. K1/K2 connection
   Connect the actual local log data to the source-facing records
       K1VerticalBoundary P Q
       K2FrobenioidBoundary R K X Y
   for the same I. K1 has the vertical upper-semi correspondence, actual
   nonarchimedean inclusion/archimedean surjection and labelled Kummer data.
   K2 has local/global Frobenioid carriers, mod/MOD maps, degree/realification/
   transport laws, comparison square and upper-semi equality. The connection
   must use actual SourceTheorem311Realization/packet/evaluation data from the
   chain, not arbitrary inhabitants of these records.

7. Multi-place assembly
   Assemble the per-finite-place data over the C1 place binding into one C2
   object indexed by the same I, with consistent p/completion/invariant choices.
   Archimedean places are a separate, currently unformalized branch.

Scope: this stage fixes the nonarchimedean finite-place log-Kummer
construction. The archimedean log-shell (III Def 1.1(ii)) is not formalized in
current donors and remains an explicit gap.

## 2. Paper anchors and route

- coord/N8-CLOSURE-ROUTE.md section 2 choices two/three and section 4 C2:
  actual log, kernel/image, Kummer arrow, action descent and required K1/K2;
  consumers C4/C5/C9.
- IUT III, Definition 1.1(i),(iii); introduction lines 208-226; Proposition
  1.2(v); Proposition 3.2(ii) (anchors recorded in SourceLogShellCarrier).
- IUT II, Example 1.8(ix): log-shell version of the invariant unit image.
- IUT III, Proposition 3.5 and Theorem 3.11(ii); IUT II, Definition 4.9:
  K1 vertical log-Kummer boundary.
- IUT III, Propositions 3.7 and 3.10; Theorem 3.11(i)(c): K2 Frobenioid boundary.

These anchors locate the objects; they do not make the current Lean records
source-faithful. The current K1/K2 records are conditional and reduced, and the
concrete analytic chain is separate from them.

## 3. Allowed input vs C2 must produce

### 3.1 Allowed input

1. C0: l, V, I : OriginalInput.
2. C1: actual place binding to be frozen in C1 stage 2:
   - SourcePlaceRealization I (V equivalent to finite/infinite places);
   - per-place completion and integers;
   - selected finite place/prime p for the local construction.
   C1-STAGE1 currently lists SourcePlaceRealization and strip-fiber comparison
   as gaps; no actual Lean type exists yet. C2 stage 1 may assume these only as
   a planning dependency, not as proved input.

### 3.2 C2 must produce

- Actual unit logarithm at each finite completion and its kernel/image.
- Actual principal-unit subgroup and its quotient/exponent facts.
- Actual invariant submonoid from the G_v(†Pi_v)-action, not top.
- Actual pre-log-shell/log-shell in the local field.
- Actual Kummer arrow/root-change and compatibility with log.
- Actual action descent through kernel/invariants.
- Actual K1/K2 connection fields for the same source realization.
- Multi-place C2 package indexed by the same I.

### 3.3 Forbidden free data

C2 must not:
- rename ind3 or its set image as the local log;
- take an arbitrary SourceLogShellDatum with K, Units, invariants, logMap
  chosen freely as the source log;
- set invariants := top and call it the actual G_v(†Pi_v)-invariant submonoid;
- take a free LabelledKummerIso, free Kummer map, free K1/K2 boundary, or free
  descends_iff witness as the source realization;
- use SourceProposition37Frobenioid.effective := True, arbitrary mod/MOD maps,
  or an arbitrary local/global Frobenioid as K2;
- assume the concrete analytic chain and the abstract K1/K2 records are already
  connected; no file currently provides that connection;
- use Nonempty, True, PUnit, arbitrary Equiv, or arbitrary set maps to replace
  actual local data.

## 4. Existing Lean donors and exact limits

### 4.1 SourceLogShellDatum (SourceLogShellCarrier.lean:86)

Fields:
    p : Nat, hp : Nat.Prime p
    K : Type u, Field K, CharZero K
    Units : Type u, CommGroup Units
    invariants : Submonoid Units
    logMap : Units ->* Multiplicative K

Definitions: pStar, preLogShell, logShell, unitLayer, codomainKummerContained.
Proved: zero/add membership, powers, preLogShell subset logShell/unitLayer,
invariant logs in preLogShell/logShell, codomainKummerContained iff unitLayer
subset logShell, IQ-span facts, nonarchimedean upper-semi construction.

Limits (declared in file):
- ind-topological domain reduced to its log-coordinate field K;
- G_v(†Pi_v)-action reduced to the supplied invariant submonoid;
- logMap is a contract hom, not a constructed p-adic log;
- codomainKummerContained is a named condition, not derived;
- archimedean case not formalized.

Consequence: SourceLogShellDatum is a carrier/law layer, not by itself the
actual C2 source log.

### 4.2 sourceLocalLogShellDatum (SourceLocalLogShellDatum.lean)

For place : FinitePlaceAtPrime K p, it constructs a SourceLogShellDatum with:
    K := CommonPrimeCompletion place
    Units := (Integers (CommonPrimeCompletion place))^x
    invariants := top
    logMap := unitLogHom
and proves:
    preLogShell = range of actual unitLog;
    logShell = actual integralLogShell;
    zero and unitLog(1) membership.

This is a real per-finite-place unit-log bridge. Exact limits for C2:
invariants := top, so it does not encode the actual G_v(†Pi_v)-invariant
submonoid; it has no Kummer arrow, action descent or K1/K2 connection.

### 4.3 IntegralUnitLogarithmKernel (Foundations/LocalFields)

Actual theorems/maps:
    unitLog_eq_zero_iff_exists_pow_eq_one
    unitLog_eq_zero_iff_isOfFinOrder
    unitLogHom_ker_eq_torsion :
      (unitLogHom).ker = CommGroup.torsion (Integers K)^x
    unitLogTorsionQuotientHom :
      ((Integers K)^x / torsion) ->* Multiplicative K
    unitLogTorsionQuotientHom_injective
    unitLogTorsionQuotientEquivRange :
      ((Integers K)^x / torsion) ≃* unitLogHom.range

Actual kernel/image/torsion-quotient donor for a complete ultrametric local
field. No source G_v action, Kummer arrow, K1 or K2.

### 4.4 FinitePlaceSourceLogKernel (ABCBridge/Geometry)

At place : NumberField.FinitePlace K, using actual CompletionIntegers place and
Completion place:
    completionUnitLog_eq_zero_iff_isOfFinOrder
    completionUnitLogHom_ker_eq_torsion
    completionUnitLogTorsionQuotientHom
    completionUnitLogTorsionQuotientHom_injective

Transport of the torsion-kernel theorem through the actual completion
isomorphism. Natural finite-place donor for C2's kernel/image step; still no
action/Kummer/K1/K2 data.

### 4.5 LogCarrierK1K2 (Foundations/AlgebraicGeometry)

At FinitePlaceAtPrime F p:
    completionIsometryEquiv : CommonPrimeCompletion place ≃+* NormalizedCompletion place
    completionIsometryEquiv_isometry
    unitLogToLattice
    K2Map : unitLogLattice Source -> unitLogLattice Target
    K1K2_naturality / K1K2_naturality_mul
    integralUnitMap_mul

Actual local K1/K2 naturality square on unscaled unit-log lattices for the
completion isometry. Not the abstract K1VerticalBoundary/K2FrobenioidBoundary
records and does not by itself produce their fields.

### 4.6 SourceK1K2Construction (IUTIII/Theorem311)

K1VerticalBoundary fields (source-facing):
    vertical : UpperSemiCorrespondence Nat Real
    vertical_monotone
    nonarchimedeanImage / archimedeanImage : Nat -> Set Real -> Set Real
    nonarchimedean_inclusion / archimedean_surjection
    nonarchimedean_profile / archimedean_profile
    labelledKummer : forall c, LabelledKummerIso Choice Choice
    labelled_label
K2FrobenioidBoundary fields:
    localFrobenioid / globalFrobenioid : SourceProposition37Frobenioid
    modMap / MODMap
    mod_degree / MOD_degree / mod_realification / MOD_realification /
    mod_transport / MOD_transport
    comparison / comparison_local/global/lower/upper
    upperSemi / upperSemi_eq_k1
k1OfRealization projects a supplied SourceTheorem311Realization to K1.

Limits: conditional abstract records. K1 image data are Real possible-image
sets, not the local log carrier. K2 Frobenioid fields are reduced
(SourceProposition37Frobenioid has effective := True and abstract
degree/realification/transport); they are not a source comparison. No file
connects the concrete analytic log/torsion chain of 4.3-4.5 to these records.

### 4.7 descends_iff (tmp/sheaf/n8/LogDescentStatement.lean)

Statement: for D : SourceLogShellDatum and f : D.Units -> Y,
    (exists fbar : D.logMap.range -> Y, forall u, fbar (logMap u) = f u)
    iff
    (forall u t, t in logMap.ker -> f (t*u) = f u).

Generic quotient-through-range criterion (Quotient.lift +
quotientKerEquivRange). Valid donor only for the kernel-quotient step. No local
place, actual unit log, G_v action, Kummer arrow or K1/K2. It must not be
reported as the C2 source realization or action descent.

### 4.8 Principal units / unit log donors

- principalUnits (K) in Foundations/LocalFields/IntegralUnits.lean:82:
  actual open subgroup {u | ||u.val - 1|| < 1}, with finite quotient and
  uniform exponent theorem.
- unitLog and its laws in Foundations/LocalFields/IntegralUnitLogarithm.lean;
  unitLog_eq_log1p, unitLog_pow.
- integralLogShell and logShellScale in the local logarithm files, used by
  sourceLocalLogShellDatum.

These give actual principal-unit and log-shell components, but not the source
invariant submonoid, Kummer arrow, action descent or K1/K2 link.

## 5. statement dependencies

| Dependency | Declaration/file | Status |
|---|---|---|
| C0 allowed input | OriginalInput (SourceOriginalInput.lean:41) | exists |
| C1 place binding | SourcePlaceRealization / finite-place binding | to define; C1 gap |
| Actual completion | CommonPrimeCompletion / Completion / FinitePlaceAtPrime | exists donor |
| Actual integral units | (Integers K)^x / CompletionIntegers | exists donor |
| Actual unit log | unitLog / completionUnitLog | exists donor |
| Log-shell carrier | SourceLogShellDatum | exists carrier/law layer |
| Per-finite-place bridge | sourceLocalLogShellDatum | exists; invariants=top |
| Torsion kernel | unitLogHom_ker_eq_torsion / completionUnitLogHom_ker_eq_torsion | proved donor |
| Torsion quotient image | unitLogTorsionQuotientEquivRange / completionUnitLogTorsionQuotientHom | proved donor |
| Principal units | principalUnits | exists donor |
| K1/K2 naturality square | LogCarrierK1K2 | proved local completion square |
| K1 boundary | K1VerticalBoundary | conditional record, not source-linked |
| K2 boundary | K2FrobenioidBoundary | conditional record, not source-linked |
| Generic descent | descends_iff | proved generic criterion only |
| Source action/invariant submonoid | none | gap |
| Kummer arrow | none | gap |
| Actual action descent | none | gap |
| K1/K2 source connection | none | gap |
| Archimedean case | none | gap/out of current scope |

## 6. proof dependencies (proved vs gap)

Proved and reusable:
- kernel of actual unit log = torsion (IntegralUnitLogarithmKernel,
  FinitePlaceSourceLogKernel);
- torsion quotient injective/equiv range;
- principal units open, finite quotient, uniform exponent;
- actual logShell equals integralLogShell in sourceLocalLogShellDatum;
- actual completion isometry and K1/K2 naturality square;
- generic descends_iff quotient criterion;
- SourceLogShellDatum carrier laws (zero, add, powers, pre/log-shell inclusion,
  IQ span, upper-semi construction under codomainKummerContained).

Gap:
- C1 actual place/completion binding;
- actual G_v(†Pi_v)-invariant submonoid and its action;
- actual Kummer arrow/root-change from the source, compatible with log;
- actual action descent, not just the generic quotient criterion;
- connection from local log/torsion data to K1VerticalBoundary;
- connection to K2FrobenioidBoundary and replacement of reduced/free
  Frobenioid fields by source data;
- archimedean log-shell branch;
- multi-place C2 assembly over C1.

## 7. Natural-language proof steps

1. From C1, fix the actual finite place v, residue prime p, completion K_v,
   integers O_v, unit group U_v and residue field k_v.
2. Instantiate the actual local log at K_v: log_v := unitLog (or
   completionUnitLog), not an arbitrary logMap. Build the SourceLogShellDatum
   carrier with K := K_v and Units := U_v, but replace invariants := top by the
   actual G_v(†Pi_v)-invariant submonoid once the action is available.
3. Prove kernel/image and exact sequence:
   T_v = ker log_v = torsion U_v; L_v = range log_v; U_v/T_v ≃* L_v.
   Use IntegralUnitLogarithmKernel and FinitePlaceSourceLogKernel.
4. Construct principal units P_v and prove openness, finite quotient and uniform
   exponent; restrict log_v to P_v and identify its image with the principal
   part of L_v.
5. Construct the actual Kummer arrow from p-power roots/principal units to the
   local Kummer carrier, prove well-definedness, inverse laws where required,
   and compatibility with log_v and pStar scaling. No free LabelledKummerIso.
6. Construct the actual G_v(†Pi_v)-action on U_v/invariants, prove invariants map
   into preLogShell/logShell, and prove action descent through the kernel. Use
   descends_iff only for the quotient-by-range step.
7. Connect actual realization/packet/evaluation data (when C4/C5 provide them)
   to K1VerticalBoundary: populate vertical upper-semi correspondence, image
   operations, inclusion/surjection directions and labelled Kummer fields from
   the actual log/Kummer construction, not arbitrary Real-set fields.
8. Connect to K2FrobenioidBoundary: construct local/global Frobenioid carriers
   with actual degree/realification from the same local log data, prove mod/MOD
   degree, realification and transport laws and the comparison square. Do not
   use SourceProposition37Frobenioid.effective := True as source data.
9. Assemble per-finite-place C2 data over C1 into one C2 object indexed by the
   same I; prove placewise compatibility and p/action compatibility.
10. Record the archimedean branch separately; do not claim it in the finite-place
    C2 package.

## 8. Exact gaps

G1 C1 actual place/completion binding absent. SourcePlaceRealization, finite
place/p identification and prime-strip fiber comparison are C1 gaps; C2 cannot
start from actual source places until C1 stage 2 provides them.

G2 actual invariant submonoid/action absent. sourceLocalLogShellDatum uses
invariants := top. The actual G_v(†Pi_v)-invariant submonoid and its action are
not constructed; without them preLogShell/logShell are only the full unit-log
image, not the paper's log-shell.

G3 actual Kummer arrow absent. SourceLogShellDatum has no Kummer field;
codomainKummerContained is only a containment condition. LabelledKummerIso in
K1 is a free bijection record, not the source root-change/Kummer arrow.

G4 actual action descent absent. descends_iff is only a generic
quotient-through-range criterion. It does not construct the G_v action,
invariance or source descent.

G5 K1/K2 source connection absent. The concrete analytic chain (unit log,
torsion quotient, principal units, completion isometry) and the abstract
K1VerticalBoundary/K2FrobenioidBoundary records are disconnected. K1 image data
are Real possible-image sets; K2 Frobenioid fields are reduced/free. Filling
these records with arbitrary values is forbidden.

G6 archimedean case not formalized. Current log-shell carrier is
nonarchimedean; the archimedean log-shell/subquotient is a separate gap.

G7 multi-place C2 package absent. Only a per-finite-place SourceLogShellDatum
and per-place completion square exist. A single C2 object over the C1 binding
with consistent p/action/completion choices is not yet defined.

G8 source faithfulness of the reduced carrier. SourceLogShellDatum reduces the
ind-topological domain and G_v action; even the per-place donor with actual
unitLog and invariants=top is not yet the paper's invariant log-shell. C2 stage
2 must keep this reduction explicit, not claim the full paper object from the
carrier alone.

G9 K1/K2 universe/index issues. K1/K2 are parameterized by an actual
SourceTheorem311Realization/Packet and arbitrary carrier types; C2 has no actual
realization yet. The K1/K2 connection is downstream of C4/C5 actual source data,
not a standalone local-log theorem.

## 9. Consumers

- C4: uses actual local log/Kummer/action data to build the source-witnessed
  output and Ind operations; C4 must not invent a separate log.
- C5: uses actual log/Kummer and descent to prove IPL/SHE/APT compatibility.
- C9: uses actual local log and q-side data for q values and the final
  Q <= Theta comparison.
- C10: assembles C2 with C1/C3-C9; C2 is the source log-Kummer node, not a free
  parameter.

## 10. Stage-1 acceptance and stop

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes the C2 target, allowed input, produced objects, forbidden
free data, existing donors and exact limits, dependence on C1, generic-only
status of descends_iff, K1/K2 connection gap, and nonarchimedean scope. No Lean
or production file is changed.

Stop after this stage-1 record. The next executable step is C2 stage 2: freeze
the exact SourceLogKummerData fields for one finite place (log, kernel, image,
principal units, invariant submonoid/action, Kummer arrow, descent) using the
actual donors above, and define the K1/K2 bridge interface only as a separate
child node; do not fill K1/K2 from arbitrary data.
