# S729: prismatic cohomology / THH / TC / log-prismatic stacks as tools for
# q[2u], the mu_{2l} root stack, and the paper Theta-pilot hull log

Date: 2026-10-30.
Status: one-shot far-field research memo (task D). No Lean claim, no new Lean
file compiled, no fake object, no surrogate, no target change.

**TL;DR (Chinese).** prismatic cohomology、log-prismatic cohomology、log THH /
TC / infinite root stack 都不能为当前两个 exact 缺口提供 paper-faithful 工具。
理由不是"文献没查够"，而是对象类型不匹配 + 一个已证的 torsor 障碍：

1. 这些理论输出的是上同调群 / 谱 / 栈，paper 需要的是元素（q[2u] 的截面）和
   Haar 测度（Theta-pilot hull 的 log-volume）；
2. 2l-th root 的集合是一个非平凡的 mu_{2l}-torsor：S342 已证 completion 中无根，
   且 q 的 order 与 l 互素，故 q 在 base 中不是 2l 次幂；任何上同调理论都不选出
   一个点，paper 的 q[2u] 是 Hodge theater 里的"选定根"，只能由 paper 的
   O^triangleright 结构（或一个显式 trivialization）提供，而不是由 cohomology 提供；
3. IUT 的 "log" 是 p 进 mono-analytic log（log: O^× -> additive，log-volume 是
   Haar 测度），与 log geometry 的 log structure 同名异义；"q-de Rham" 的 q 是
   形式形变参数，与 IUT 的 q_v 也只是同名。

唯一可接受的副产品是语义性的：log de Rham 的 dlog 归一化
dlog(q[2u]) = (1/(2l)) dlog(q[1u]) 与 paper 系数 order/(2l) 一致；但该归一化
已经由 root^(2l) = q 与 `paperRootCoefficient = order/(2l)` 承载，不产生新定理。
结论：**明确拒绝**这四条路线作为缺口闭合工具；见 §5 表和 §6 的 exact-gap 形式化。

## 0. Frozen target and the two exact gaps in the current repo

Frozen target (FROZEN_TARGET.md): `-|log(Theta)| >= -|log(q)|`.

The two exact gaps named by the parent task, in current repo terms:

### G1. q[2u] / root-stack carrier

* Actual 2l-th root exists only in the algebraic closure of the completion:
  `TwoLthRootKummerActual.hodgeTwoLthRoot` (lines 71-73) with
  `hodgeTwoLthRoot_pow : hodgeTwoLthRoot^(2l) = qVAlgClosedUnit` (lines 82-86).
* The completion has no 2l-th root and no NatRootSystem:
  `S342QVFamilyRootImpossibleActual.natRootSystem_impossible` (line 93),
  `qVFamilyTwoLRootCard_impossible`.  The valuation/order obstruction is
  `Nat.Coprime (qVFamily T b).order l` (S342).
* mu_{2l} orbit and hull are actual: `PaperC3RootThetaHullActual.paperRootThetaMuPoint`
  (line 46), `paperRootThetaMuOrbit` (line 52), `paperRootThetaHull` (line 59).
* Root-stack action groupoid is actual: `S356RootStackActionGroupoidActual`
  (`RootObj` line 33, `rootStackGroupoid` line 44).
* Missing: the "section monoid" (`S392RootStackSectionMonoidActual.SectionCarrier`,
  line 31; `rootStackMonoidSectionCarrier`, line 76) is a function model, not
  paper O^triangleright; no paper q[1u]/q[2u] section equality; no map from the
  extension carrier to the completion/root-stack carrier.

### G2. Paper Theta-pilot hull log

* Actual extension-valued product image hull:
  `PaperRootExtensionThetaHullAuditActual.rootExtensionProductImageHull` (line 54)
  and its actual Haar log `rootExtensionProductImageHullLog` (line 165),
  with the definitional identity at line 169.
* Actual paper-coefficient hull/log on the completion tensor block:
  `BadPlacePaperRootThetaHullActual.paperRootThetaHull` (line 40),
  `paperRootThetaHullLog` (line 45), `paperRootThetaFormulaLog` (line 51),
  conditional identity `paperRootThetaHullLog_eq_formula_of_gap` (line 68)
  from the exact `PaperRootHullFormulaGap` (line 56).
* `PaperRootHullFormulaGap` itself is completion-root impossible (it requires a
  completion generator of norm `p^(-(order/(2l)))`, i.e. a completion 2l-root;
  contradicted by S342).  See PAPER_THETA_NORMALIZATION_STATUS.md and TASK_LEDGER.md
  ("EXACT but completed/obsolete").  Do not fill it.
* Missing: paper hull equality / log-measure equality
  (`rootExtensionProductImageHull` vs the paper holomorphic/lambda-O hull), and
  the qPilot comparison.  Packaged as exact Props:
  `RootThetaExtensionHullCarrierActual.RootThetaToCompletionHullMapGap` (line 110)
  and `S649RootThetaExtensionComparisonActual.S649RootThetaQPilotComparisonRequired`
  (line 65).

Criterion (same as S728 section 0): a far-field direction counts only if it
supplies (a) an actual object with the same Kummer/procession normalization and
(b) a theorem identifying its log with `paperRootThetaHullLog` /
`signedHullLogVolume`, or supplies the actual q[2u] carrier used by
`rootNormedThetaValueInL`.

## 1. Prismatic cohomology (Bhatt-Scholze; Bhatt-Morrow-Scholze)

### 1.1 Concrete objects and theorems

* Bhatt-Scholze, "Prisms and Prismatic Cohomology", arXiv:1905.08229:
  prisms (A, I) with delta-structure, prismatic site of a p-adic formal scheme,
  prismatic cohomology with Hodge-Tate, de Rham, and etale comparisons.
* Bhatt-Morrow-Scholze, "Integral p-adic Hodge theory", arXiv:1602.03148:
  A-Omega complex; the abstract says the theory "can be computed as a
  q-deformation of de Rham cohomology" (the q-de Rham complex; q is a formal
  deformation parameter).
* Bhatt-Morrow-Scholze, "Topological Hochschild homology and integral p-adic
  Hodge theory", arXiv:1802.03261: the motivic filtration on THH and its
  variants, with graded pieces the prismatic / A-Omega complexes; for a
  quasiregular semiperfectoid S, the Nygaard-complete prismatic cohomology
  is `DeltaHat_S := pi_0 TC^-(S; Z_p)` (BMS; recalled in
  Binda-Lundemo-Park-Ostvaer, arXiv:2306.01368, section 1).
* Wagner, "q-Witt vectors and q-Hodge complexes", arXiv:2410.23078: a q-variant
  of Witt vectors / de Rham-Witt complexes, related to the Habiro ring and
  THH(-/ku).  Again q is formal.

### 1.2 Why this cannot close G1 or G2

* **Type mismatch.**  Prismatic cohomology is a functor on p-adic formal
  schemes/rings.  The paper's q[2u] is a *chosen element* (a section of the
  Kummer torsor); the paper's Theta-pilot hull log is a *normalized Haar
  measure* on a subset of a product of completions.  Neither is a cohomology
  group.  There is no construction in Bhatt-Scholze or BMS of a canonical
  2l-th root of a unit, and no measure/log-volume.
* **Torsor obstruction (G1), precise.**  Let K be the local completion and
  q in K^× with |q| < 1.  The set `{r in Kbar^× : r^(2l) = q}` is a
  mu_{2l}-torsor.  It is non-trivial: `val(q) = order` is coprime to l
  (S342, `qVFamily_order_coprime`), so val(q) is not divisible by 2l, and q
  is not a 2l-th power in K.  A canonical root therefore requires a
  trivialization (equivalently a chosen section), which is exactly what the
  paper's Hodge theater / O^triangleright supplies and what the Lean model
  encodes by `qCandidateRootSystem` (tmp/sheaf/n8/closure/C3Roots.lean line 43)
  / `hodgeTwoLthRoot`.  Prismatic cohomology of K or of the Kummer extension
  L = K(q^(1/(2l))) is a complex of L-modules; it does not select a point of
  the torsor.  (It cannot manufacture an element not in the ring.)
* **mu_{2l} root stack.**  The root stack is the quotient of the above torsor;
  prismatic cohomology of B mu_{2l} is group cohomology of mu_{2l}.  The
  paper's mu_{2l} action of Fig. 3.4 is the root-of-unity indeterminacy on the
  theta values, which is exactly the orbit already formalized in
  `paperRootThetaMuOrbit`; it is not a cohomology class.
* **Hull log.**  Prismatic cohomology has no Haar measure, no mono-analytic
  log, and no procession normalization.  There is no theorem of the form
  `paperRootThetaHullLog = log(prismatic object)`; the RHS object does not
  exist.
* **Name collision.**  The q in q-de Rham / q-Witt is a formal deformation
  parameter (q -> 1 recovers de Rham); the IUT q_v is a local parameter with
  |q_v| < 1 and theta values q[2u]^(j^2).  No theorem identifies them.  A
  q-de Rham computation would not compute the finite-label average
  `sum_{j in F_l^x} j^2 = l(l^2-1)/12` (S711); that average is elementary
  finite-group arithmetic.

### 1.3 Lean feasibility

Mathlib (checked in D:\lean\.lake\packages\mathlib\Mathlib) has:

* `RingTheory/Perfectoid/{BDeRham, FontaineTheta, Untilt}.lean` (3 files);
* `RingTheory/WittVector/*` (20 files, classical Witt vectors);
* `RingTheory/AdicCompletion/*`, `FieldTheory/KummerExtension.lean`,
  `NumberTheory/Cyclotomic/*`, Haar measure (`IsAddHaarMeasure` used widely).

Mathlib has **no** prisms, delta-rings, prismatic site, prismatic cohomology,
Nygaard filtration, log structures, log schemes, or root stacks (`grep` counts
0).  The statement of a prismatic theorem is not even typeable now; formalizing
the prerequisites (log schemes, delta-rings, prisms, derived completion, sites)
is a multi-person-year library project, and even then no target theorem exists.

**Verdict: REJECT** for G1/G2.  Not a paper-faithful tool.

## 2. Log prismatic cohomology / log THH / log TC / infinite root stack

This is the closest family: it is literally about Kummer roots, log structures,
root stacks, and TC.

### 2.1 Concrete objects and theorems

* Koshikawa, "Logarithmic Prismatic Cohomology I", arXiv:2007.14037:
  delta_log-rings, the logarithmic prismatic site, log Breuil-Kisin
  cohomology in the semistable case.
* Koshikawa-Yao, "Logarithmic prismatic cohomology II", arXiv:2306.00364:
  log de Rham and log etale comparison (generalizing Bhatt-Scholze), Nygaard
  filtration, F-crystals vs Z_p-local systems in the log setting.
* Binda-Lundemo-Park-Ostvaer, "Logarithmic Prismatic Cohomology via
  Logarithmic THH", arXiv:2306.01368: log THH and its filtrations;
  Nygaard-completed log prismatic cohomology; log THH of quasiregular
  semiperfectoids is a 1-parameter deformation of ordinary (non-logarithmic)
  Hochschild homology; comparison with log (derived) de Rham cohomology.
* Binda-Lundemo-Merici-Park, "Logarithmic TC via the Infinite Root Stack and
  the Beilinson Fiber Square", arXiv:2408.15627: expresses the log cotangent
  complex, Rognes' log TC, and Nygaard-complete log prismatic cohomology via
  the infinite root stack; proves the site-theoretic log prismatic
  cohomology coincides with the log-TC definition; log Beilinson fiber square.
* Talpo-Vistoli, "Infinite root stacks and quasi-coherent sheaves on
  logarithmic schemes", arXiv:1410.1164: the infinite root stack of a log
  scheme; root stacks as log structures.
* Ausoni-Bayindir-Moulinos, "Adjunction of roots, algebraic K-theory and
  chromatic redshift", arXiv:2211.16929: for an E_1-ring A and a class a,
  construct A -> A(a^(1/m)); define log THH; root adjunction is log-THH-etale
  for a suitably tamely ramified extension, giving a formula for
  THH(A(a^(1/m))) in terms of THH and log THH of A.

### 2.2 What it genuinely gives (and what it does not)

Genuine Kummer/root content:

* The 2l-root is **Kummer/log-etale-local**, not a canonical element of the
  base: the log scheme with log structure generated by q is trivialized on the
  Kummer cover; the 2l-root lives on the root stack / Kummer cover.  This
  matches S342 (no completion root) and the extension carrier exactly.
* **dlog normalization.**  In a log de Rham complex,
  dlog(q[2u]) = (1/(2l)) dlog(q[1u]); equivalently the paper's
  `paperRootCoefficient = order/(2l)`.  This is a definition-level
  justification of the 1/(2l), not a theorem about the hull.
* **THH of the root extension.**  For the tame case (p not dividing 2l), the
  root adjunction K -> K(q^(1/(2l))) is log-THH-etale (Ausoni et al.); this is
  a genuine theorem about the ambient of q[2u].

Why it still does not close G1/G2:

* **"log" collision, now the main one.**  Log prismatic / log THH use a log
  structure (a sheaf of monoids mapping to O).  The IUT "mono-analytic log" is
  a homomorphism log: O^× -> additive group (the p-adic logarithm), and the
  "log-volume" is the Haar measure of the log-shell.  The repo already has the
  latter: `IUTII/Kummer/SourceLogShellCarrier.lean`,
  `MonoAnalyticLogShellFormalLogMul.lean` (principal-unit p-adic log, `logOf_mul`,
  `padicIntPrincipalUnitLog`).  Log prismatic cohomology does not produce this
  p-adic log or the Haar log-volume.
* **The root is an input, not an output.**  The Kummer cover L / root stack is
  built from a chosen root (or a tautological section on the root stack); the
  theorem computes cohomology of that cover.  It does not construct the paper's
  chosen q[2u] in O^triangleright, and does not prove the paper q[1u]/q[2u]
  section equality (S392).
* **The infinite root stack computes cohomology, not measures.**  Its points
  include roots, but the theory produces cohomology groups; there is no Haar
  measure, no hull, no procession average, and no theorem identifying a
  log-prismatic group with `paperRootThetaHullLog`.
* **mu_{2l}.**  The root stack's mu_{2l}-gerbe is the Kummer torsor; its
  cohomological shadow is group cohomology of mu_{2l}, not the paper's action
  on theta values.  Fig. 3.4 is the orbit `paperRootThetaMuOrbit` already.

### 2.3 Lean feasibility

Same as section 1.3 plus stacks and log schemes: **not statable**.  Mathlib has
groupoids (`CategoryTheory.Groupoid`, used by S356) and group cohomology
(`RepresentationTheory/Homological/GroupCohomology/*`), but no log schemes,
delta_log-rings, root stacks, infinite root stacks, or log TC.  Formalizing the
infinite root stack and log TC is far outside this project.

**Verdict: REJECT as a gap-closer.**  Accept only as a semantic justification
for (i) Kummer-locality of the 2l-root and (ii) the dlog 1/(2l) normalization —
both already captured by `root^(2l) = q` and the paper coefficient.  A Lean
formalization would add no theorem about the hull log.

## 3. THH / TC

### 3.1 Concrete objects and theorems

* THH(A) is a T-spectrum (circle action); cyclotomic structure (C_{p^n}
  actions plus Frobenius/restriction maps) yields TC^- and TC; cyclotomic trace
  K -> TC.  Standard reference: Nikolaus-Scholze, "On topological cyclic
  homology", arXiv:1707.01799.
* BMS arXiv:1802.03261: motivic filtration on THH/TC^-; graded pieces
  prismatic/A-Omega; `DeltaHat_S := pi_0 TC^-(S; Z_p)` for quasiregular
  semiperfectoid S.
* Hesselholt-Madsen: TC of the algebraic closure of a local field.  This is the
  closest published TC theorem to the actual ambient of q[2u] (a finite
  extension of a p-adic completion inside an algebraic closure), but it
  computes homotopy groups of TR_n(V|K) fixed-point spectra, not a root or a
  measure.

### 3.2 Why this cannot close G1 or G2

* **No root.**  THH/TC are functors of ring spectra.  They do not select a
  2l-th root of q.  The only root-related theorem is the root adjunction
  (section 2.2), which presupposes the root.
* **mu_{2l} vs p-power.**  THH carries a T-action, hence a C_n-action for any
  n; but the cyclotomic structure used to define TC is built from the p-power
  subgroups C_{p^n} of one prime p.  There is no single "mu_{2l}-cyclotomic"
  structure for composite 2l = 2*l, and in any case Fig. 3.4's mu_{2l} is the
  Kummer root ambiguity, not a circle action.  No identification theorem.
* **No measure.**  TC is a spectrum; its homotopy groups are rings/modules,
  not Haar log-volumes.  There is no mono-analytic log or procession
  normalization in TC, and no theorem `paperRootThetaHullLog = trace(TC)`.
  The cyclotomic trace/regulator story (K-theory -> TC, p-adic logarithm) is
  about traces on K-theory, not the Haar measure of a Theta hull.

### 3.3 Lean feasibility

Mathlib has no stable homotopy theory, no spectra, no infinity-categories, no
operads/E_infinity, no THH, no cyclotomic spectra, no TC.  It has simplicial
homotopy, model-category basics, condensed sets/modules, and singular homology
(`AlgebraicTopology/*`), which are far from THH/TC.  Formalizing the
prerequisites is a multi-year project, and even then there is no target
theorem.

**Verdict: REJECT.**

## 4. "q-de Rham / q-Witt / Habiro ring" as a possible q-analog

Objects: BMS q-de Rham complex; Wagner q-Witt vectors/q-Hodge complexes
(arXiv:2410.23078); Habiro ring (Garoufalidis-Scholze-Wheeler-Zagier) and
THH(-/ku).  The q there is a formal deformation parameter (q -> 1 gives de
Rham), not the IUT local parameter q_v.  The Theta labels' exponents j^2 and
the average `sum_j j^2 = l(l^2-1)/12` (S711) are elementary finite-group
arithmetic; no cohomology theory is needed or available for them.  The name
collision is a trap for the formalization, not a tool.

**Verdict: REJECT.**

## 5. Summary table

| direction | q[2u] 2l-root | mu_{2l} root stack | Theta-pilot hull log | Lean feasibility | verdict |
|---|---|---|---|---|---|
| prismatic cohomology (Bhatt-Scholze, BMS) | no canonical root; torsor obstruction | cohomology of B mu_{2l} only | no measure/log-volume | not statable (no prisms/log schemes) | reject |
| log prismatic / log THH / log TC / infinite root stack | root is Kummer-local; root adjunction for tame case | root stack as log stack; no paper action | no measure; infinite root stack gives cohomology | not statable (stacks, log schemes, log TC) | reject (semantic justification only) |
| THH / TC | no root; root adjunction presupposes it | C_n action exists but cyclotomic structure is p-power; no identification | no measure; HM computes TR homotopy groups | not statable (no spectra/THH) | reject |
| q-de Rham / q-Witt / Habiro | no (formal q) | no | no; label average is finite-group arithmetic | not statable (no q-Witt/q-Hodge) | reject |

## 6. The exact gap in Lean-shaped form (no inhabitant claimed)

To use any far-field theory in a paper-faithful way, one would have to produce
one of the following; none exists in the cited literature.

### 6.1 G1: the q[2u] carrier

The paper-faithful carrier is the actual finite extension with the chosen root
(`rootNormedExtension`, `hodgeTwoLthRoot`, `twoLthRootAt`) plus the mu_{2l}
action; the missing pieces are *comparisons*, not a new root:

```lean
-- current exact gap (S649RootThetaExtensionComparisonActual, line 51):
structure S649RootThetaQPilotComparisonData where
  rootHullLogComparison : RootThetaHullLogComparison
  extensionToCompletionHullMap : RootThetaToCompletionHullMapGap
```

A prismatic/log-TC replacement would need a Lean structure of the form

```lean
structure PrismaticRootCarrierBridge where
  Carrier : Type
  root : Carrier                      -- would have to be q[2u], not a cohomology class
  root_pow : (root : ...) ^ (2*l.value) = q[1u]
  toPaper : Carrier -> RootExtensionProductCarrier T
  root_eq : toPaper root = actualRoot  -- paper q[2u]
```

No construction in Bhatt-Scholze, BMS, Koshikawa, Koshikawa-Yao,
Binda-Lundemo-Park-Ostvaer, or Binda-Lundemo-Merici-Park provides `Carrier`,
`root`, or the comparison `toPaper`; the root is always an input/chosen
trivialization.

### 6.2 G2: the paper Theta-pilot hull log

What would be needed is exactly an inhabitant of the existing comparison
interface, e.g. a proof of

```lean
rootExtensionProductImageHullLog T = paperRootThetaHullLog T b mu
-- or, in the S649 packaging:
Nonempty (S649RootThetaQPilotComparisonData)
```

Any far-field bridge would have to supply a carrier, a Haar measure on it, and
the equality of the normalized logs.  No theorem in the four directions
produces a measure on the paper hull or identifies a cohomology group/spectrum
with a normalized Haar log.  The existing actual objects already give the
left-hand side (`rootExtensionProductImageHullLog`); the missing right-hand
side is a paper-level identification, which is analytic/measure-theoretic, not
cohomological.

## 7. Recommendation

1. **Do not** import prismatic/log-prismatic/THH/TC/q-de Rham infrastructure;
   it cannot close G1 or G2, and its Lean prerequisites are absent.
2. **Keep** the actual carriers: `TwoLthRootKummerActual.hodgeTwoLthRoot`,
   `PaperC3ThetaRootActual.twoLthRootAt`, `rootNormedExtension`, and the S356
   action groupoid.  These are the paper-faithful shadow of the Kummer torsor.
3. The remaining exact work is the measure/log bridge
   (`rootExtensionProductImageHullLog` vs the paper hull log) and the qPilot
   comparison (`S649RootThetaQPilotComparisonRequired`), plus the
   `PaperXiFSourceLink` fields.  This is not a cohomology problem.
4. If a normalization record is wanted, the only Lean-feasible addition is a
   `Real.log`-level ratio lemma from S709
   (`rootImageRadius_eq_p_rpow`, line 145:
   `rootImageRadius = p^(-c_norm/(2l))`), i.e. the dlog bookkeeping
   `log(root)/log(q) = 1/(2l)`.  It is definitional bookkeeping, not a gap
   closer.
5. Avoid the two name collisions in any future memo: (i) IUT q_v vs q-de Rham
   formal q; (ii) IUT mono-analytic p-adic log / log-volume vs log geometry
   log structure.

## Sources

* Bhatt-Scholze, Prisms and Prismatic Cohomology: https://arxiv.org/abs/1905.08229
* Bhatt-Morrow-Scholze, Integral p-adic Hodge theory: https://arxiv.org/abs/1602.03148
* Bhatt-Morrow-Scholze, THH and integral p-adic Hodge theory:
  https://arxiv.org/abs/1802.03261
* Nikolaus-Scholze, On topological cyclic homology: https://arxiv.org/abs/1707.01799
* Koshikawa, Logarithmic Prismatic Cohomology I: https://arxiv.org/abs/2007.14037
* Koshikawa-Yao, Logarithmic prismatic cohomology II:
  https://arxiv.org/abs/2306.00364
* Binda-Lundemo-Park-Ostvaer, Logarithmic Prismatic Cohomology via
  Logarithmic THH: https://arxiv.org/abs/2306.01368
* Binda-Lundemo-Merici-Park, Logarithmic TC via the Infinite Root Stack and
  the Beilinson Fiber Square: https://arxiv.org/abs/2408.15627
* Talpo-Vistoli, Infinite root stacks and quasi-coherent sheaves on
  logarithmic schemes: https://arxiv.org/abs/1410.1164
* Ausoni-Bayindir-Moulinos, Adjunction of roots, algebraic K-theory and
  chromatic redshift: https://arxiv.org/abs/2211.16929
* Wagner, q-Witt vectors and q-Hodge complexes:
  https://arxiv.org/abs/2410.23078
* Hesselholt-Madsen, On the topological cyclic homology of the algebraic
  closure of a local field: https://math.mit.edu/~larsh/papers/020/

## Repo files checked

* tmp/sheaf/xif/paper/TASK_LEDGER.md
* tmp/sheaf/xif/paper/FROZEN_TARGET.md
* tmp/sheaf/xif/paper/CURRENT_PATH_NOTES.md
* tmp/sheaf/xif/paper/PAPER_THETA_NORMALIZATION_STATUS.md
* tmp/sheaf/xif/paper/PAPER_EXTENSION_HULL_STATUS.md
* tmp/sheaf/xif/paper/FIVE_PAPER_GAPS_STATUS.md
* tmp/sheaf/xif/paper/S682LogGeometryToolsResearch.md
* tmp/sheaf/xif/paper/S728_TOOLING_MEMO.md
* tmp/sheaf/xif/paper/TwoLthRootKummerActual.lean
* tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean
* tmp/sheaf/xif/paper/PaperC3RootThetaHullActual.lean
* tmp/sheaf/xif/paper/PaperRootThetaHullCarrierGapActual.lean
* tmp/sheaf/xif/paper/RootThetaExtensionHullCarrierActual.lean
* tmp/sheaf/xif/paper/PaperRootExtensionThetaHullAuditActual.lean
* tmp/sheaf/xif/paper/BadPlacePaperRootThetaHullActual.lean
* tmp/sheaf/xif/paper/S342QVFamilyRootImpossibleActual.lean
* tmp/sheaf/xif/paper/S356RootStackActionGroupoidActual.lean
* tmp/sheaf/xif/paper/S392RootStackSectionMonoidActual.lean
* tmp/sheaf/xif/paper/S649RootThetaExtensionComparisonActual.lean
* tmp/sheaf/xif/paper/S709RootImageRadiusFormulaActual.lean
* tmp/sheaf/n8/closure/C3Roots.lean
* LeanFormal/IUT/IUTII/Kummer/{NatRootSystem, TimesMuQuotient, KummerClass,
  TimesMuIsm, SourceLogShellCarrier, MonoAnalyticLogShellPadicLog,
  MonoAnalyticLogShellFormalLogMul}.lean
* Mathlib inventory: RingTheory/Perfectoid, RingTheory/WittVector,
  RingTheory/AdicCompletion, FieldTheory/KummerExtension,
  NumberTheory/Cyclotomic, MeasureTheory (Haar), AlgebraicTopology,
  Condensed, RepresentationTheory/Homological/GroupCohomology.
