# S735 (Task G): perfectoid / Fargues-Fontaine / tilting / nonarch adic geometry versus the paper q[2u] and Theta-pilot hull log

Date: 2026-10-30. Status: research memo. No target change, no fake object, no
surrogate. The only Lean artifact added by this task is
`S735PerfectoidFFToolInventory.lean` (`#check` inventory only, EXIT=0; see
section 8). All mathematical statements below are either quoted from the
project's actual Lean files, standard external theorems, or explicitly marked
as proof sketches / not formalized.

Companion files read first: `TASK_LEDGER.md`,
`PAPER_THETA_NORMALIZATION_STATUS.md`; then `S682LogGeometryToolsResearch.md`,
`S728_TOOLING_MEMO.md`, `S731_EHRHART_TORIC_MEMO.md`, `S711QNormalizationSearch.md`.

## 0. 结论摘要 (Chinese, for the lead)

结论：**perfectoid fields / tilting / Fargues-Fontaine curve / nonarch adic
geometry 都不能为 q[2u] 的 2l-root 与 Theta-pilot hull log 提供 paper-faithful
carrier。** 三个硬阻碍：

1. **value-group / Kummer 阻碍**：q[2u] 的存在要求 v(q) 在 value group 中被
   2l 整除。completion 的 value group 是离散的；perfectoid 只给 p-divisible
   value group（tilt 只把 value group 换成 Gamma[1/p]），对 l != p 的 l-primary
   Kummer class 毫无作用；tilt equivalence 对 finite etale covers 是等价，
   所以“有没有 2l-root”在 K 与 K^flat 中完全一样。
2. **没有 Haar / finrank 阻碍**：paper hull log 是有限维 Q_p 向量空间上的
   normalized Haar log，`Measure.addHaar` 在 Lean 里就需要
   `LocallyCompactSpace`；perfectoid field 不是局部紧的（value group
   p-divisible 且非离散），也不是 Q_p 有限维的（`Module.finrank = 0`）。
   因此 perfectoid / FF untilt / adic 空间上无法定义 paper 的
   `arithmeticTupleNormalizedLogVolume`。
3. **FF 是全局理论、不是 per-b carrier**：FF curve 的 closed points / untilts
   给的是 arithmetic holomorphic structures，q 是 Tate 曲线的 period /
   extension class，不是 FF curve 上的点或 section；2l-root 是 local Kummer
   class，不是 FF 对象。Joshi 的 FF/perfectoid 路线（arXiv:2401.13508）是另一套
   全局 arithmetic Teichmuller 理论，采用它就是换 global setup / source，不是
   本项目的 paper-faithful carrier；而且没有 Lean。

正面结论：**同时满足“exact fractional generator（root 的实际 norm
p^{-c_norm/(2l)}；与 paper n/(2l) 的识别是另一个系数对齐 gap）+ 有限维 Q_p
Haar” 的最小 field carrier 就是 L = K_v(q[2u])（现有
`rootNormedExtension`）**；perfectoid 在 R1 上最好也只能做到 L^perf（先把 root
adjoin 进去再 perfectoidize），而在 R3 上永远失败。L 仍是 AUX（见
`AUXILIARY_BRANCHES.md` / `COMPLETION_ROOT_INVALID_STATUS.md`），不是 paper
O^tri/O^triangle carrier；paper carrier 是 Kummer log étale / root stack（S346），
perfectoid pro-Kummer étale site 只是 ambient topos。

**审计发现（重要，供 lead 决策）**：`BadPlacePaperRootThetaHullActual.PaperRootHullFormulaGap`
的形式陈述只要求 `ArithmeticTuplePureFractionalScalingData`（一个 norm 为
p^{-c} 的 generator）加 hull_eq；它**没有要求这个 generator 等于 q[2u] 的
section，也没有要求 hull 是 theta values 的 image**。因此：

* 若 completion 的 value group 恰好含 n/(2l)（例如 2l | n e_v；其中 e_v 是 K_v/Q_p 的 ramification index），这个
  formal gap 可以被一个与 q 无关的 norm-ball generator 填上，即 surrogate；
* 反之，即使 formal gap 被证，也不能直接当作 paper closure；必须同时证明
  q[2u] section 的 identification（或 hull = Theta-value image）。
  这是把 exact gap 写 paper-faithful 时必须补的字段，不是 fake，也不是换 target。

## 1. Target and the two exact gaps

### 1.1 Target (unchanged)

    -|log Theta| >= -|log q|,

with q[1u] = q_v, q[2u] = q[1u]^(1/(2l)), Theta_j = q[2u]^(j^2), paper local
coefficient `order(q_v)/(2l)` (`qVFamPaperRootCoefficient`,
`QVFamRootFactorCorrectionActual.lean` lines 54-63;
`PAPER_THETA_NORMALIZATION_STATUS.md` lines 5-14).

### 1.2 Current actual objects

* q[2u] root: `hodgeTwoLthRoot T b` in
  `AlgebraicClosure (Completion (qVPlace T b))`,
  `(hodgeTwoLthRoot T b) ^ (2*l) = qVAlgClosedUnit T b`
  (`TwoLthRootKummerActual.lean` lines 66-85). Completion root is impossible
  (S342, `S342QVFamilyRootImpossibleActual.lean` lines 52-97): any completion
  2l-root would force l | order(q_v), contradicting the source clause-(c)
  `Nat.Coprime (qVFamily.order) l`.
* Analytic extension: `rootNormedExtension T b =
  IntermediateField.adjoin (rootBase T b) {rootNormedElement T b}`,
  finite-dimensional over Q_p, nontrivially normed, proper, with additive Haar
  (`PaperRootCompletionTensorActual.lean` lines 54-97;
  `PaperRootExtensionHaarActual.lean`; `PaperRootExtensionValuedActual.lean`).
  Root norm closed form (S709, `S709RootImageRadiusFormulaActual.lean` lines
  56-95 and 144-149):

      rootNormedElementNorm T b
        = p ^ (-(qVFamNormalizedCoefficient T b) / (2*l)),

  and `(rootNormedElementNorm)^(2l) = p^(-qVFamNormalizedCoefficient)`.
* Paper-coefficient per-b hull and its exact gap:
  `paperRootCoefficientFamily T b = fun _ => order(q_v)/(2l)`;
  `paperRootThetaHull T b = rootThetaHull ... paperRootCoefficientFamily`;
  `paperRootThetaFormulaLog T b = -((sum _ : qVFamTensorV,
  order/(2l)) * log p)`;
  `PaperRootHullFormulaGap T b` = scaling data at the paper coefficient +
  hull_eq to `F(paperRootCoefficient) * O_hol`
  (`BadPlacePaperRootThetaHullActual.lean` lines 35-66; decomposition in
  `S719PaperRootHullGapDecompositionActual.lean` lines 30-50).
* Actual theta-hull log used by the current scalar target:
  `paperPerBThetaHullLog = rootThetaHullLog ... rootHalfCoefficient`
  (S716), where `rootHalfCoefficient = c_norm/(2l)`; S726 proves it is
  nonpositive, while the S663 theta-magnitude average is positive, so the
  S663 average is not the hull log
  (`S726PaperHullVsS663GapActual.lean` lines 46-103). This is a separate
  normalization/surrogate issue, not the carrier issue, but it bounds what a
  "carrier replacement" could buy.

### 1.3 What "paper-faithful carrier" must supply

(R1) A root section r with r^(2l) = q[1u], living in the paper carrier (not a
completion 2l-root, not an arbitrary norm-ball generator), together with the
mu_{2l} ambiguity.

(R2) The Theta-values q[2u]^(j^2) and their image hull, identified with the
paper holomorphic/lambda-O hull (not merely a formal scaled region).

(R3) A normalized log-volume: finite-dimensional Q_p vector space, canonical
unit / O_hol, additive Haar, normalization 1/finrank (IUT IV Prop. 1.4(i));
this is exactly `arithmeticTupleNormalizedLogVolume`
(`FinitePlaceNormalizedUnitScalingLogVolume.lean` lines 89-98).

(R4) The mu_{2l} indeterminacy kept, not quotiented away (IUT III Remark 3.11.4:
theta values are considered up to multiplication by 2l-th roots of unity).

(R5) Compatibility with the log-link/Theta-link and Ind1/Ind2/Ind3 (log-shell /
mono-analytic side). This is why the paper's carrier is a log-shell sheaf, not a
field.

Sections 2-5 test the four candidate geometries against R1-R5.

## 2. Perfectoid fields

### 2.1 Definitions and standard facts

A perfectoid field K (Fontaine; Scholze, *Perfectoid spaces*, Publ. IHES 2012)
is a complete nonarchimedean field with residue characteristic p, p-divisible
value group, and surjective Frobenius on O_K/p. Standard facts used below:

(P1) K^x is p-divisible: every element has a p^n-th root, for all n. Only
p-power roots are supplied by perfectoidness; l-primary roots (l != p) are not.

(P2) The tilt K^flat = lim_{x -> x^p} O_K/p is a perfectoid field of
characteristic p, with residue field the same and value group
Gamma_{K^flat} = Gamma_K[1/p] (p-power roots divide valuations by p).

(P3) Tilting equivalence: finite etale K-algebras are equivalent to finite
etale K^flat-algebras (Scholze 2012; Kedlaya-Liu for the relative version). For
n prime to p, Kummer theory gives
K^x/(K^x)^n ~ (K^flat)^x/((K^flat)^x)^n.

(P4) A perfectoid field is not locally compact: a locally compact
nonarchimedean field has value group isomorphic to Z (discrete) and finite
residue field, whereas a nontrivial perfectoid value group is p-divisible, hence
not discrete. A char-0 perfectoid field is also not finite-dimensional over Q_p
(finite-dimensional would force Gamma ~ Z).

### 2.2 Against R1: the l-primary obstruction survives perfectoidization

Let K = K_v be the p-adic completion at the bad place, with value group
Gamma_K = v(varpi)^Z, v(q_v) = n v(varpi), and gcd(n,l) = 1 (S342).

* If l != p: n/(2l) is not in Z[1/p] (its denominator contains l, and l is
  prime to p and to n). Hence q_v^(1/2l) is not in K_v^perf =
  (K_v(p^{1/p^infinity}))^: the p-perfectoidization of the base does not
  contain the l-root. One must adjoin q_v^(1/2l) first; only then does
  L^perf = (L(p^{1/p^infinity}))^ contain it (trivially).
* If l = p: n/(2p) is in Z[1/p] exactly when n is even. If n is even, the
  valuation is p-divisible, and since K_v^perf^x is p-divisible (and is
  2-divisible for p odd because mu_{p'} contains mu_2 and 1+m is 2-divisible),
  q_v^(1/2p) actually lies in K_v^perf. This is the only genuine "perfectoid
  gives the root for free" case. It is still useless for the paper hull log:
  R3 fails (2.3), and the root is non-canonical (a compatible p-power tower
  determines it only up to mu_{2p}).

So "perfectoid field contains the root" is either false (l != p), case-special
(l = p, n even), or achieved only after adjoining the root (L^perf). It never
produces the paper root section in the paper carrier.

### 2.3 Against R3: no Haar, no finrank

This is the decisive obstruction. The paper hull log is

    (1 / finrank_{Q_p} X) * (log mu(S) - log mu(O_hol)),

and in Lean `Measure.addHaar` has an explicit `[LocallyCompactSpace G]`
argument (verified: see the compiled inventory, section 8), while
`Module.finrank` is 0 for an infinite-dimensional module. For a perfectoid
field K:

* `¬ LocallyCompactSpace K` (P4), so there is no additive Haar measure on K;
* `Module.finrank Q_p K = 0` (char-0 perfectoid fields are infinite over Q_p;
  in char p there is no Q_p-structure at all), so the 1/finrank normalization
  is 0/undefined.

Consequently the exact formula `arithmeticTupleNormalizedLogVolume ...` cannot
be instantiated on any perfectoid field, and neither can its product/tensor
version with a finite `Fintype` index of perfectoid factors. The paper's
normalization is intrinsically a finite-dimensional p-adic Lie group measure;
a perfectoid field is at the opposite extreme (infinite-dimensional,
non-locally-compact). Replacing the tensor block by a perfectoid field would
lose the paper normalization, i.e. would be a surrogate.

### 2.4 The honest perfectoid object: L^perf and its tilt

The minimal perfectoid field containing q[2u] is

    L^perf = (L(p^{1/p^infinity}))^,   L = K_v(q[2u]),

where the p-power roots of a pseudo-uniformizer and of O_L are adjoined. Then:

* q[2u] is an element of L^perf, with v(q[2u]) = n/(2l);
* (L^perf)^flat is a char-p perfectoid field, and q[2u] has a tilt (a compatible
  system of p-power roots); the untilt of (L^perf)^flat is L^perf itself;
* L^perf is not locally compact, not finite-dimensional over Q_p, and has no
  Haar/finrank normalization.

So the perfectoid route has exactly one honest object (L^perf, its tilt, and
the corresponding point of the Fargues-Fontaine cover Y), and that object is
obtained by first doing the forbidden step (adjoining the root). It is not a
paper-faithful carrier and cannot replace the finite tensor block.

### 2.5 Verdict and Lean feasibility

Reject as a carrier for q[2u] and for the Theta hull log. Accept only as a
no-go/consistency language: "tilt/perfectoidization does not split the
l-primary Kummer class unless the root is already there" and "the paper Haar
normalization forces finite dimension".

Lean feasibility: none for a positive construction. Mathlib has no
`PerfectoidField`, no tilt functor/equivalence, no perfectoid value-group or
local-compactness API. The only perfectoid-related Mathlib content is
`PreTilt` + `PreTilt.untilt` (a map, explicitly *not* the untilt functor) and
Fontaine theta (section 8). Formalizing even the statement `¬
LocallyCompactSpace K` for a perfectoid field would require the missing
perfectoid-field API first.

## 3. Tilting

### 3.1 Concrete objects and theorems

* Tilt: O_{K^flat} = lim_{x -> x^p} O_K/p, K^flat = Frac(O_{K^flat}) (for K
  perfectoid); tilting equivalence of finite etale algebras (P3).
* Value group: Gamma_{K^flat} = Gamma_K[1/p].
* Kummer class: for n prime to p, the class [q] in H^1(G_K, mu_n) ~
  K^x/(K^x)^n maps isomorphically to the class [q^flat] in
  H^1(G_{K^flat}, mu_n). Hence q has a 2l-th root in K iff q^flat has one in
  K^flat. Since 2l is prime to p when l != p, tilting neither creates nor
  destroys the root. When l = p, the l-primary part is pro-p; the valuation
  still detects the class, and the p-perfectoidization can split it only under
  the 2-divisibility condition of 2.2. In no case does tilting produce the
  paper root in a carrier with Haar.
* The Theta-link/log-link is not the tilt: in the FF picture the Frobenius
  phi of Y moves between untilts (Joshi: phi has the properties of the log-link;
  arXiv:2401.13508). Applying phi does not change the Kummer class inside a
  fixed untilt, so it cannot manufacture q[2u] there.

### 3.2 Verdict and Lean feasibility

Reject. Tilting is a symmetry of the obstruction, not a source of roots, and it
lands in char p / perfectoid fields with no Haar. In Lean, `PreTilt` and
`PreTilt.untilt` exist, but there is no `Tilt` functor, no tilting
equivalence, and no value-group transfer; nothing to build on without new
foundations.

## 4. Fargues-Fontaine curve

### 4.1 Concrete objects and theorems

For a perfectoid field C with tilt C^flat:

* A_inf = W(C^flat) (with the (p,[varpi])-adic topology), Y = Spa(A_inf,
  A_inf^+) (adic/formal version) and X = Y / phi^Z; X is a regular noetherian
  scheme of dimension 1, the "p-adic P^1" (Fargues-Fontaine 2018).
* Closed points of X correspond to untilts of C^flat modulo Frobenius; Y-points
  are untilts themselves, and their residue fields carry naturally normalized
  valuations (Joshi's reason for working with Y rather than X: the closed
  points of X do not come with such natural normalizations).
* Vector bundles on X are classified by slopes (Harder-Narasimhan); O_X is a
  sheaf of Dedekind domains (the local rings are DVRs); H^0(X, O_X) = Q_p.
* The Tate parameter q of E_q: E_q(Kbar) ~ Kbar^x / q^Z, and T_p E_q sits in
  0 -> Z_p(1) -> T_p E_q -> Z_p -> 0. The parameter q is the period/extension
  class of this filtered phi-module (up to the p-adic logarithm); it is not a
  point of X and not a section of a line bundle on X. The 2l-root q^(1/2l) is a
  Kummer class in H^1(G_K, mu_{2l}), not an FF object.

### 4.2 Against R1/R2/R3

* R1: the FF curve knows p-divisible groups / filtered phi-modules and their
  periods; it does not produce a chosen 2l-root per bad place. The Kummer class
  is invisible to the FF classification except through its p-adic completion.
* R3: X and Y are not finite-dimensional Q_p vector spaces; Y-points are
  perfectoid fields (no local compactness, no finrank). The product formula on
  the adelic Y_L is a global normalization (product over all places = 1), not
  the per-b `1/finrank` Haar log of the paper tensor block. These are different
  measures, and no theorem in the repo or the cited literature identifies them.
* R4/R5: FF is a natural home for the Ind1/arithmetic-holomorphic-structure
  discussion, but the paper's Theta-pilot object is a per-b local object; moving
  to the FF curve changes the global setup.

### 4.3 Joshi's arithmetic Teichmuller route

Joshi, *Construction of Arithmetic Teichmuller Spaces III: A "Rosetta Stone" and
a proof of Mochizuki's Corollary 3.12* (arXiv:2401.13508; local copy
`tmp/sheaf/n8/closure/lit/joshi3.html`), builds adelic Fargues-Fontaine curves
Y_L, arithmeticoids and a global product formula, and derives a version of
Cor 3.12 via a Theta-values locus. This is the only serious FF/perfectoid-based
approach to the same inequality. It is nevertheless:

* a different global theory (arithmetic Teichmuller spaces, adelic FF curves),
  not the IUT III per-bad-place Theta-pilot carrier; adopting it would be a
  source/global-setup change, not a carrier for the current target;
* not formalized in Lean (nor is the FF curve itself);
* using the product formula, not the per-b normalized Haar log, so it does not
  supply `paperRootThetaHullLog` even in principle.

Reject as a replacement for the paper carrier; keep as external evidence that
the FF route is global and target-changing.

## 5. Nonarch adic geometry (Huber adic spaces, rigid analytic, Berkovich)

### 5.1 Concrete objects

* Huber adic spaces Spa(A, A^+) and the adic spectrum; perfectoid spaces are
  adic spaces (Scholze); rigid analytic spaces and Berkovich analytification
  are related frameworks.
* Adic generic fiber: for a formal model, the generic fiber is an adic space;
  for a finite extension L/K_v, Spa(L, O_L) is a one-point space.
* Berkovich space M(L) of a complete nonarch field L is a single point; it has
  no skeleton unless one passes to a nontrivial variety.

### 5.2 Against the requirements

* R3: adic spaces are not locally compact in general and carry no canonical
  additive Haar; the finite-dimensional Q_p Haar used by the paper is a
  p-adic Lie group measure, already available on the tensor block. The adic
  generic fiber of the tensor block is an affinoid whose measure is the same
  finite-dimensional Haar; passing to adic spaces adds no normalization.
* R1/R2: the root and the Theta-values are elements/sections of a Kummer
  object; adic spaces do not change the value group or split the Kummer class.
  The hull equality `paperRootThetaHull = F(c) * O_hol` is an equality of
  subsets of a finite-dimensional Q_p vector space; it is not an adic-space
  statement, and generic-fiber passage loses the integral structure/canonical
  unit reference (O_hol) needed for the log.
* S682 already concluded: "Do not import perfectoid/adic spaces for O^triangle;
  they formalize a different topology" (`S682LogGeometryToolsResearch.md`
  lines 121-137). S728 rejected Berkovich skeleta for the hull-log side
  (`S728_TOOLING_MEMO.md` lines 40-85); the one-point Berkovich space of the
  root field is the sharp reason.

### 5.3 Lean feasibility

No Mathlib adic spaces (open draft PR 30978, not in this checkout), no
Berkovich spaces, no Huber rings; only adic completion/topology
(`Mathlib/Topology/Algebra/Nonarchimedean/AdicTopology.lean`,
`Mathlib/RingTheory/Smooth/AdicCompletion.lean`). Formalizing the paper hull
log through adic spaces would be a multi-file new foundations project, and the
mathematical content would still be the finite-dimensional Haar already used.

## 6. The carrier dichotomy (main structural result)

This section isolates why no perfectoid/FF/adic object can satisfy the paper
requirements, and why the finite extension L is the minimal *field* carrier.

### 6.1 Value-group versus Haar

Let K be a finite extension of Q_p with normalized absolute value |.| (so
|p| = p^{-1}), value group Gamma = |K^x| = p^{-(1/e)Z} for some ramification
index e, and O_K = {x : |x| <= 1}. For c in R define the norm ball

    F(c) = {x in K : |x| <= p^{-c}}.

Lemma 6.1 (proof sketch; not formalized).

(i) F(c) is a principal fractional lattice, i.e. exists g with |g| = p^{-c}
    and F(c) = g O_K, iff p^{-c} is in Gamma.
(ii) If p^{-c} is in Gamma, then for any additive Haar mu,
    mu(F(c))/mu(O_K) = p^{-c}.
(iii) If p^{-c} is not in Gamma, then F(c) = F(c') where
    c' = min {gamma in log_p Gamma : gamma >= c}, and
    mu(F(c))/mu(O_K) = p^{-c'} != p^{-c}.

Proof: O_K = {|x| <= 1}; g O_K = {|x| <= |g|}; Gamma is discrete, so the ball
is constant on the interval between consecutive value-group elements; Haar
scales by the modulus, mu(gS) = |g| mu(S).

Tensor version. For the tensor block X = tensor_i K_i with the product Haar and
O_hol = integral closure of Z_p, the pure-tensor generator of
F(c) = tensor_i F_i(c_i) exists iff each p^{-c_i} is in Gamma_i; then
mu(F(c) * O_hol)/mu(O_hol) = p^{-sum_i c_i}. This is exactly the hypothesis of
`ArithmeticTuplePureFractionalScalingData c`
(`FinitePlaceNormalizedUnitScalingLogVolume.lean` lines 133-153): the local
generator of norm p^{-c_i} plus a common exponent is precisely a value-group
integrality condition; the Haar formula
`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`
(lines 379-390) is the "principal" case of Lemma 6.1.

Lemma 6.2 (characterization; forward direction immediate, converse routine via
the production constructor). `ArithmeticTuplePureFractionalScalingData c` is
nonempty iff each p^{-c_i} lies in the normalized value group of the i-th
completion. In particular the formal `PaperRootHullFormulaGap` at
c = order/(2l) reduces to the value-group condition
`n/(2l) in (1/e_v)Z` (plus the hull equality), and does **not** by itself
require a 2l-th root of q.

Remark 6.2.1 (status-doc correction; important for the lead).
`PAPER_THETA_NORMALIZATION_STATUS.md` lines 78-90 says that the local generator
of completion norm p^{-(order/(2l))} is "equivalent to a completion 2l-th root
of q[1u]". That equivalence is not what
`ArithmeticTuplePureFractionalScalingData` requires: the structure records
only the generator's norm (and the principal-lattice relation); it never
asserts that the generator's 2l-th power is q. Even in the normalized-units
case c_norm = n, the 2l-th power is only q times a norm-1 unit, not q. S342 is
the stronger statement that no generator can be *identified* with q[2u]; the
bare norm-ball existence is the value-group condition 2l | n e_v and can be
nonempty in ramified cases. This
does not overturn the no-completion-root conclusion, but it means:

(i) "PaperRootHullFormulaGap is completion-impossible" should be read as
    "impossible for a paper-faithful generator/root", not as a universal
    value-group impossibility;
(ii) the formal gap must be strengthened by the q[2u] identification (section
     0 and 8.4) to be paper-faithful.

### 6.2 Corollary: field carriers

| carrier | R1 root/exact generator at n/(2l) | R3 Haar/finrank | verdict |
|---|---|---|---|
| completion K_v | iff 2l divides n e_v; generator not q[2u] | yes | not paper-faithful |
| L = K_v(q[2u]) | yes (the root itself) | yes (finite over Q_p, proper, Haar) | minimal field carrier; AUX |
| K_v^perf | only l=p and n even (2.2) | no (not locally compact, finrank 0) | reject |
| C_p (completed alg. closure) | yes (alg. closed) | no (not locally compact, infinite residue) | reject |
| L^perf | yes | no | honest perfectoid object; reject for hull |
| FF untilt / Y-point | no chosen root per bad place | no | reject |
| adic generic fiber of L | same as L | same as L (point/affinoid) | no new object |

The dichotomy is sharp: **R1 pushes the carrier to a value group containing
n/(2l); R3 pushes it to a locally compact finite-dimensional Q_p vector space.
If R1 is read weakly as "an exact fractional generator exists", larger finite
extensions with e' divisible by 2l also qualify, but they still do not contain
the root q[2u]; if R1 is read as the paper root section, only finite extensions
containing L qualify.** A perfectoid field satisfies "many roots" but never R3;
the completion satisfies R3 but may fail the root/exact-generator condition;
hence no perfectoid/FF/adic field can replace L, and L itself is not the paper
carrier (next section). Caveat: L realizes the *root* with coefficient
c_norm/(2l) (S709); identifying it with the paper order/(2l) is the separate
coefficient-alignment gap (`BadPlacePaperConstantsActual.lean` lines 64-86,
`s13HalfCoefficient_eq_paperRootCoefficient_of_normalized_eq_order`). The
carrier analysis is independent of that gap, but a paper-faithful statement on
L would need it too.

### 6.3 The paper root stack is not a field

The paper's O^tri / O^triangleright (O^triangle) and O^⊵ carrier is a
Kummer/tempered sheaf, not a field:
* the 2l-root is a *section* of a Kummer cover / root stack, with mu_{2l}
  inertia;
* the Theta-values are sections modulo mu_{2l} (IUT III Remark 3.11.4);
* the log-shell is mono-analytic and Q-valued: fractional exponents such as
  n/(2l) are meaningful by construction, whereas the completion's norm ball
  rounds n/(2l) to the next value-group element (Lemma 6.1(iii)).

This is exactly why the formal completion gap `PaperRootHullFormulaGap` cannot
be the whole paper statement: the paper hull lives on the Q-valued log-shell /
root stack, not on a norm ball in a p-adic field.

## 7. The paper-faithful route: Kummer log etale / root stack

### 7.1 Concrete objects

* Log point: (Spec O_{K_v}, log structure given by the closed point); the
  q-divisor defines a line bundle with section q.
* Kummer log etale cover of degree 2l: adjoining a 2l-th root of q (and the
  roots of unity); the cover is a mu_{2l}-torsor. The root stack
  X_{(q),2l} (the stack of 2l-th roots of the section q) carries the universal
  root section r with r^(2l) = q; its inertia is mu_{2l}. The paper's
  O^triangle (a tempered version of O^x, with the mu_{2l}-indeterminacy) and
  the O^⊵ root section are the units/sections of this stack.
* Pro-Kummer etale site (Scholze, *Etale cohomology of diamonds*): the Kummer
  log point B^{log}; Kummer covers of degree n; the perfectoid pro-Kummer etale
  site is the ambient topos in which the Kummer class becomes locally trivial.
  It is a topos of sheaves, not a perfectoid field; the root is a section of a
  sheaf on the cover, not an element of a field.

### 7.2 Why this is not the perfectoid/FF/adic route

* The root stack is a log/stack object; it exists for every q, regardless of
  whether q has a root in K_v. The universal root is a tautological section of
  the pullback, not a splitting of the Kummer class in K_v.
* The mu_{2l}-gerbe keeps the indeterminacy (R4); a field carrier quotients or
  chooses it away.
* The Q-valued mono-analytic log-shell has fractional exponents by
  construction; no completion root and no perfectoid field is needed.
* The pro-Kummer etale site is used only for the Kummer/cyclotomic bookkeeping;
  it does not supply the Haar log (R3), which remains the finite-dimensional
  tensor block / log-shell measure.

### 7.3 Existing repo objects and the exact missing piece

* S346OrbifoldStructuralSheafActual: spec of the O^triangle carrier and the
  q/root sections (lines 55-69); no inhabitant.
* S356RootStackActionGroupoidActual: actual roots + mu_{2l} action groupoid
  (lines 33-87).
* S392RootStackSectionMonoidActual: function-model section monoid with
  qSection/rootSection and mu_{2l} action (lines 31-87); not the geometric
  O^triangle.
* S680/S688/S691: the missing map from the section monoid to
  `Units (LinearBaseIdentityEndomorphism A)`, with divisor-zero/inverse data
  (`S691RootStackUnitsFieldsActual.lean` lines 29-75,
  `RootStackUnitsFieldsData`). This is the actual paper gap; perfectoid/FF does
  not help with it.

## 8. Lean feasibility

### 8.1 Mathlib inventory (compiled artifact)

`S735PerfectoidFFToolInventory.lean` (this task) compiles EXIT=0. It records:

* `PreTilt` (type), `PreTilt.untilt : PreTilt O p ->* O`,
  `PreTilt.mk_untilt_eq_coeff_zero`,
  `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow`;
* `WittVector.fontaineTheta : WittVector p (PreTilt R p) ->+* R`,
  `WittVector.fontaineThetaModPPow`,
  `surjective_fontaineTheta : Function.Surjective (frobenius (ModP R p) p) ->
  Function.Surjective (fontaineTheta R p)`;
* `MeasureTheory.Measure.addHaar` (requires `LocallyCompactSpace G`),
  `Module.finrank`, `FiniteDimensional.proper` (requires
  `LocallyCompactSpace k`).

Absent (grep 0 in Mathlib): `PerfectoidRing`, `PerfectoidField`, tilt
functor/equivalence, `AdicSpace`/`Spa`, `FarguesFontaine`, Berkovich
spaces. Adic spaces exist only as an open draft PR (mathlib4 PR 30978), adic
completion as PR 31295 (see S682).

### 8.2 What is formalizable now

* The finite-extension/Haar side is already formalized: L is a nontrivially
  normed field, finite-dimensional over Q_p, proper, with Haar
  (`PaperRootCompletionTensorActual.lean`, `PaperRootExtensionHaarActual.lean`,
  `PaperRootExtensionValuedActual.lean`); S709 gives the root norm closed form.
* The completion no-go is formalized (S342) at the level of the Tate parameter
  order; the value-group version (Lemma 6.1) is not in Lean and would need a
  normalized value-group API (the repo has `Valued` instances and
  `normalizedCompletion_norm_*_iff`, but not the discrete value group).
* The root stack is formalized only as an action groupoid / function monoid
  (S356/S392); the geometric O^triangle and the map to O^tri units are missing
  (S691).

### 8.3 What a perfectoid/FF Lean route would require (not present, not run)

* `PerfectoidField` (complete nonarch field, p-divisible value group,
  Frobenius-surjective O/p), the tilt functor and tilting equivalence, the
  value-group formula Gamma_{K^flat} = Gamma_K[1/p], Kummer-class transport,
  local-compactness/finrank absence theorems;
* the FF curve Y/X, untilts, slopes, and the identification of the Tate
  parameter as a period;
* adic spaces (Huber) or Berkovich spaces.
None of these exists in Mathlib; building them is a multi-file foundations
project, and even then the conclusion would be a no-go for the hull log (no
Haar/finrank), not progress on the target inequality.

### 8.4 Proposed exact statements (not compiled; for the lead to decide)

* `PaperRootHullFormulaGap` should be paired with a root identification, e.g.
  an element `rootSection : qVFamTensorBlock T b` (or a section of the root
  stack) whose `(2*l)`-th power is the image of `qVFamily.q`, together with
  `generator = rootSection`; or a separate
  `PaperRootHullImageIdentification : paperRootThetaHull T b =
  image of qVFamPaperThetaValueRoot`. Without it, even a proof of the current
  formal gap does not give the paper statement (see 0 and 6.1).
* A formalizable value-group lemma in the completion:
  `HasExactFractionalGenerator c <-> p^{-c} in normalizedValueGroup`
  (needs the missing API); and the tensor form matching
  `ArithmeticTuplePureFractionalScalingData`.
* A no-go statement for perfectoid carriers (requires the missing perfectoid
  API): `PerfectoidField K -> not LocallyCompactSpace K` and
  `Module.finrank Q_p K = 0`; not run.

## 9. Verdict table

| direction | q[2u] 2l-root | Theta-pilot hull log | Lean feasibility | verdict |
|---|---|---|---|---|
| perfectoid fields | no generic l-root; only p-power roots; C_p/L^perf have it but no Haar | no (no locally compact/finrank) | none (only PreTilt/theta) | reject |
| tilting | invariant Kummer class; Gamma[1/p]; no new root | no | none | reject |
| Fargues-Fontaine | q is a period, not a point; no per-b root | no (global product formula != per-b Haar) | none | reject (different global theory; Joshi 2401.13508) |
| nonarch adic / Berkovich | no | no (no Haar; generic fiber point) | none (draft PR) | reject |
| root stack / Kummer log | yes (universal root, mu_{2l}) | Q-valued log-shell; paper-faithful | missing (log/stack/O^triangle map) | correct route (S346) |
| L = K_v(q[2u]) | yes (actual) | yes (actual Haar/hull log) | actual code | analytic shadow only; AUX |
| completion K_v | no (S342) | Haar yes, but no paper generator/root (surrogate risk) | actual code | not paper |

## 10. Residual exact gaps (unchanged by this memo)

1. O^triangle/root-stack carrier with the q[2u] section and the map to O^tri
   units (S346/S691); no perfectoid/FF/adic shortcut.
2. `PaperRootHullFormulaGap` at c = order/(2l): value-group condition +
   hull equality; plus the root/image identification that makes it
   paper-faithful (audit finding above).
3. The hull-vs-theta-value identification (the hull is currently a formal
   fractional-lattice region, not the image of `qVFamPaperThetaValueRoot`;
   cf. `RootHullContainmentInequalityActual.lean` lines 57-79).
4. The coefficient alignment c_norm vs order (S13 half coefficient vs paper
   root coefficient; `BadPlacePaperConstantsActual.lean` lines 64-86) remains
   a separate normalization gap.
5. Restate the completion obstruction paper-faithfully (Remark 6.2.1): the bare
   `ArithmeticTuplePureFractionalScalingData` is a value-group condition and is
   not equivalent to a completion 2l-root; the paper statement needs the q[2u]
   identification. `PAPER_THETA_NORMALIZATION_STATUS.md` lines 78-90 should be
   corrected accordingly when the ledger is updated.

## 11. References

Internal:
* TASK_LEDGER.md, PAPER_THETA_NORMALIZATION_STATUS.md, COMPLETION_ROOT_INVALID_STATUS.md,
  AUXILIARY_BRANCHES.md, FIVE_PAPER_GAPS_STATUS.md.
* TwoLthRootKummerActual.lean; S342QVFamilyRootImpossibleActual.lean;
  PaperRootCompletionTensorActual.lean; PaperRootExtensionHaarActual.lean;
  PaperRootExtensionValuedActual.lean; S709RootImageRadiusFormulaActual.lean;
  BadPlacePaperRootThetaHullActual.lean; S719PaperRootHullGapDecompositionActual.lean;
  RootNormalizedThetaHullActual.lean; RootHullContainmentInequalityActual.lean;
  S726PaperHullVsS663GapActual.lean; S346OrbifoldStructuralSheafActual.lean;
  S356RootStackActionGroupoidActual.lean; S392RootStackSectionMonoidActual.lean;
  S691RootStackUnitsFieldsActual.lean; S682LogGeometryToolsResearch.md;
  S728_TOOLING_MEMO.md; S731_EHRHART_TORIC_MEMO.md.
* S735PerfectoidFFToolInventory.lean (this task; EXIT=0).

External:
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHES 116 (2012).
* L. Fargues, J.-M. Fontaine, *Courbes et fibres vectoriels en theorie de
  Hodge p-adique*, Asterisque 406 (2018).
* R. Huber, *Etale cohomology of rigid analytic varieties and adic spaces*.
* K. Kedlaya, R. Liu, *Relative p-adic Hodge theory II*.
* K. Joshi, *Construction of Arithmetic Teichmuller Spaces III: A "Rosetta
  Stone" and a proof of Mochizuki's Corollary 3.12*, arXiv:2401.13508.
* Mathlib files: `Mathlib/RingTheory/Perfection.lean`,
  `Mathlib/RingTheory/Perfectoid/Untilt.lean`,
  `Mathlib/RingTheory/Perfectoid/FontaineTheta.lean`,
  `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`,
  `Mathlib/Analysis/Normed/Module/FiniteDimension.lean`.
* Mathlib adic spaces draft PR 30978; adic completion PR 31295 (via S682).

No target change, no fake object, no surrogate. The recommendation is: do not
replace the root-stack/log-shell carrier or `PaperRootHullFormulaGap` by any
perfectoid/FF/adic object; keep L as the analytic shadow only, and put the
engineering effort into S346/S691 and into the paper-faithful identification of
the hull with the actual Theta-value image.
