# S732 memo: noncommutative geometry / spectral triples / cyclic homology / Dixmier trace as a route to IUT III Cor 3.12 — construction vs rejection

Date: 2026-10-30. Task H. Status: research memo + compiled no-go Lean file
tmp/sheaf/xif/paper/S732NCGLogVolumeNoGo.lean (six theorems, axioms
propext/Classical.choice/Quot.sound only).

## 0. Verdict (Chinese summary)

拒绝（rejection），但不是"NCG 无意义"，而是精确的**范畴错误 + 已有结构**：

1. 论文的 log-volume **本来就是** trace 图像：IUT III Remark 3.9.4 (i) 把它定义为
   measure space 上的积分，再取 log（normalize 成"乘 e 加 1"）。也就是说 paper 的
   log-volume 已经是 commutative von Neumann algebra + Haar weight 的 trace；再做一次
   NCG 化不产生新定理，只是换词。
2. **index 不行**：index 是整数、局部常值、活在 realification 之前；paper 的 log-volume
   活在 realified Frobenioid 上（Def 3.8 (i) 的 pilot object 就是 realified 对象）。
   realification 恰好杀掉 index 能看见的整性结构，所以 log-volume = index 是类型错误。
3. **Dixmier trace / trace 不能直接等于 log-volume**：paper 的 log-volume 满足
   scaling law（乘 λ 加 log λ）加平移不变（Haar），这两条与"对不交并集可加"直接矛盾
   （Lean 已证 no_additive_of_scaling_and_translation）。可加性是 trace/index 的定义性质，
   所以只能是 log ∘ trace，即 Haar measure 本身；trace = log-volume 不成立。
4. **trace 对 2l 次根是瞎的**（trace_functional_blind_to_roots）：任何在 μ_n 作用下不变
   的泛函（包括所有由绝对值/谱数据给出的 trace 泛函）无法区分 q[2u] 的 2l 个根。
   因此 NCG 表述**永远看不到 root stack 的 μ_{2l} 结构**；而当前 exact gap 的另一半
   正是 q[2u]/root stack carrier。这是 NCG 不能补当前缺口的决定性理由。
5. **multiradial 不对称**：Cor 3.12 里 Θ 侧 subject to (Ind1)(Ind2)(Ind3)，q 侧不 subject。
   任何"单一 Hilbert 空间/单一 trace"都是一个 common container，而 paper 的整套架构
   恰恰拒绝这个 common container。造出它 = 比 paper 更强的定理（给两个 pilot 一个共同环），
   目前不存在；不造它 = 没有 trace 比较可用。
6. 唯一**真正保留 actual q/Θ 对象**的 NCG 式构造，是把 log-volume 写成
   commutative Haar weight（paper 的积分），再加上 μ_{2l}-root stack 的 Jones index 归一化
   来解释 1/(2l)（见 §5 P2）。这是**已有形式化的换一种说法**，不减少任何 gap。

结论：NCG 路线不产生 paper-faithful 不等式；当前 exact gap（paper Θ-pilot hull log 与
q[2u]/root stack carrier）是 **object-level**（子集/hull 的构造与识别）而不是
**functional-level**（泛函/测度的计算）问题，NCG 是 functional-level 技术，故不能补。

---

## 1. What the paper's log-volume literally is (anchors)

Corpus: papers/motizuki_corpus/text/pagewise/Inter-universal Teichmuller Theory III.pagewise.plain.txt
(pagewise plain text; line numbers below refer to it).

### 1.1 Cor 3.12 (lines 1204-1234)

    -|log(Theta)| in R u {+inf} = the procession-normalized mono-analytic log-volume
    of the holomorphic hull of the union of the possible images of a Theta-pilot
    object, relative to the relevant Kummer isomorphisms, in the multiradial
    representation of Theorem 3.11 (i), regarded as subject to (Ind1), (Ind2), (Ind3).

    -|log(q)| in R = the procession-normalized mono-analytic log-volume of the image
    of a q-pilot object ... which we do NOT regard as subject to (Ind1), (Ind2), (Ind3).

    Then -|log(Theta)| >= -|log(q)|, i.e. C_Theta >= -1 for any C_Theta with
    -|log(Theta)| <= C_Theta * |log(q)|.

So both sides are log-volumes of regions; the difference is only
(i) which object's image, (ii) hull vs no hull, (iii) subject to indeterminacies or not.

### 1.2 The pilots are objects of realified Frobenioids (Def 3.8 (i), lines 6742-6774)

Theta-pilot object = the object of prod_{j in F_l^*} of the (F^circ_MOD)_j (or
(F^circ_mod)_j), as well as its realification, "determined by any collection, indexed by
v in V_bad, of **generators up to torsion** of the monoids Psi^perp_{F_lgp}(...)_v".

q-pilot object = the object of the (global realified) Frobenioid F^vdash_triangle of
[IUTchII] Cor 4.10 (i), "determined by any collection ... of generators up to torsion of
the splitting monoid ... i.e. ... determined by the q_v".

Two consequences, both decisive for task H:

* the pilots are objects of realified Frobenioids, not algebras, not operators, not
  cohomology classes;
* they are defined up to torsion: the μ_{2l}/root ambiguity is quotiented out at the
  level of the object. It survives only at the level of the subsets of the log-shell
  that are the possible images.

### 1.3 Log-volume = log of a measure (Prop 3.9 (i), (ii), lines 6991-7045; Remark 3.9.4 (i), lines 7281-7391)

Prop 3.9 (i): the weights determine log-volumes on "compact closures of nonempty open
subsets", normalized so that (a) the log-volume of the local holomorphic integral
structure O is zero, and (b) "multiplication of an element of M(-) by e = 2.71828...
corresponds to adding 1 = log(e)". Procession-normalization = average over the capsules
(not a weighted average; cf. Remark 3.9.3).

Remark 3.9.4 (i) makes the mechanism explicit: for an ample measure space (M, mu_M),
Fn(M) = nonnegative Borel functions with finite image and relatively compact support,
Sub(M) = characteristic functions, integration gives an R_{>0}-equivariant surjection
from Fn(M) onto R_{>=0}, S |-> mu_M(S), and the quotient Rss(M) (with Rss(M) isomorphic
to R_{>=0}) is called the "realified semi-simplification" of (M, mu_M), "roughly in the
spirit of the Grothendieck group associated to an additive category", "a quotient in the
category of commutative monoids with R_{>0}-action". Additive translates of S (with
respect to an additive structure preserving mu_M) are identified; disjoint unions go to
sums; products of measure spaces go to tensor products of realified monoids
(lines 7364-7391).

Thus: paper log-volume = log of the Haar/integration functional, and the paper says so.

### 1.4 The log-link must preserve volumes (Remark 3.9.4 (ii), lines 7392-7435)

If each log-link dilated volumes by λ != 1, log-volumes would be well-defined only in
R / Z·log(λ), isomorphic to S^1, "a situation which is not acceptable, relative to the
goal of obtaining log-volume estimates". This is exactly the trace-scaling /
modular-cocycle issue of semifinite noncommutative measure theory, and the paper resolves
it by requiring volume preservation.

### 1.5 Hull = λ·O, hence hull log-volume = log|λ| (Remark 3.9.5 (i), lines 7792-7814)

The holomorphic hull of a relatively compact region U is the smallest region of the form

    λ · O_{...},   λ in IQ(-) with every component nonzero,

containing U. Therefore

    mu^log(hull) = mu^log(O) + log|λ| = log|λ|.

Remark 3.9.5 (ii)-(iii) (lines 7815-7885) adds: the hull map phi : P -> H is the unique
map satisfying (P1) phi(H)=H, (P2) P subset phi(P), (P3) monotone, "a sort of integration
operation"; and mu^log(P) <= mu^log(phi(P)), with all indeterminacies compact.

**This is the single most important structural fact for task H**: the paper's signed
quantity -|log(Theta)| is literally the log of one scalar (the scaling of the hull), and
the Cor 3.12 inequality is the comparison of two scalars:

    log|λ_Theta| >= log|λ_q|    <=>    |λ_Theta| >= |λ_q|.

(Lean: PaperLogVolume.logVol_hull, cor312_scaling_iff.)

---

## 2. What an "NCG realization" would have to be, precisely

A realization of the paper log-volume as index/trace/regulator would be data

    (A, H, D, tau, regions S |-> operator or vector a_S)

with tau a trace (Dixmier, Wodzicki, semifinite normal, or a K-theoretic index pairing),
such that one of the following holds:

* (T-log) L(S) := log tau(a_S), with a_S >= 0, and the scaling law of Prop 3.9 (i)
  becomes tau(a_{λS}) = λ·tau(a_S);
* (T-direct) L(S) := tau(a_S) directly, with a_S self-adjoint (signed);
* (I) L(S) := the K_0/K^0 pairing of a projection p_S with a trace (an index);
* (R) L(S) := a regulator of a K-theory class.

The four variants are not equivalent, and the paper's definitions pin down which one can
be faithful. That is what §3 tests.

---

## 3. Framework-by-framework verdict

### 3.1 Dixmier trace / Wodzicki residue

(a) What it computes. For a positive compact operator A with eigenvalue asymptotics
λ_n ~ c/n, the Dixmier trace is Tr_omega(A) = c (the residue at s=1 of the zeta function
Tr(A^s)); it is positive, additive, homogeneous, and omega-independent on the Connes
trace class. It computes a positive volume.

(b) Consequence 1 (T-log is vacuous). A positive trace can only represent the paper's
log-volume as log ∘ tau, and then tau is exactly the Haar measure/integration functional
of Remark 3.9.4 (i). The "Dixmier" vocabulary adds the dimension-residue interpretation
(tau = residue of zeta), which is true but is not used anywhere in Cor 3.12: no zeta
function, no Dirac operator, no spectral dimension occurs in the paper's log-volume
estimates.

(c) Consequence 2 (T-direct fails on the sign). The paper's -|log(Theta)| is <= 0 by
normalization mu^log(O)=0 (the Cor 3.12 proof opens by assuming -|log(Theta)| < 0). A
positive trace is >= 0 on positive operators, so a signed log-volume can only be a
difference of two positive traces. But differences destroy exactly the monotonicity that
produces Cor 3.12: the paper's inequality comes from hull containment (imageSet subset
hull) plus monotonicity of mu^log (Remark 3.9.5 (ii); repo:
IQHullLogVolumeInterface.imageSet_logVolume_le_hull). For a difference tau_+ - tau_- of
positive traces, containment gives tau_+(S) <= tau_+(T) and tau_-(S) <= tau_-(T), hence
no conclusion about the difference. So the trace reformulation either loses the sign or
loses the inequality.

(d) Representability is vacuous; comparison is not. Any finite list of real weights
(c_q, c_Theta) can be realized as Dixmier traces of commuting diagonal operators (scale
the harmonic spectrum). So "log-volume is a Dixmier trace" is true for every assignment
and therefore constrains nothing. The mathematical content of Cor 3.12 lies entirely in
the comparison |λ_Theta| >= |λ_q|, i.e. in the arithmetic identification of the two
hulls; a trace formulation has no access to it, because it does not know which operator
belongs to which object.

(e) omega-dependence. For self-adjoint A in the Dixmier ideal but not in the Connes
trace class, Tr_omega(A) depends on the dilation-invariant mean omega. Remark 3.9.4 (ii)
demands a well-defined element of R (not R/Z·log λ); an omega-dependent functional would
reintroduce exactly the unacceptable ambiguity. Making it omega-independent is an extra
hypothesis, not a consequence.

Verdict: reject as a route; accept only as the (true but empty) statement "log-volume is
log of a Haar/tracial weight".

### 3.2 Spectral triples

A spectral triple (A, H, D) requires an algebra acting on H with D of compact resolvent;
its arithmetic content is concentrated in the global spectral triple of the adele class
space (Connes) and in the scaling-site formalism (Connes-Consani), whose target is the
zeros of zeta, not the local q-parameter log-volumes of IUT III. Three concrete
obstructions:

1. No algebra. The paper's carrier is a mono-analytic module IQ(S^pm; n,circ D^vdash)
   (Prop 3.2, 3.9 (ii)), i.e. an R-vector space with a log-shell and an F_l^*-symmetry.
   A spectral triple needs a multiplication and a Dirac operator; any choice is extra
   structure not present in the paper (and changing the carrier is forbidden).
2. Locality. Cor 3.12 is per-place, per-label, and has an explicit scaling λ_v
   (Remark 3.9.5 (i)); the Dixmier dimension is a global asymptotic invariant of an
   operator, not a per-label scaling comparison.
3. The known analytic difficulty. In the adele class space picture, the "trace formula"
   is a distribution on a restricted test-function space; producing a genuine trace /
   Hilbert-Polya operator is a famous open problem. A route that starts by postulating
   such a trace would import an open problem instead of proving Cor 3.12.

Verdict: reject.

### 3.3 Cyclic homology

For the commutative algebras that occur in the paper (local fields, their rings of
integers, monoid algebras of realified monoids), the Hochschild-Kostant-Rosenberg theorem
gives HH_*(A) = Omega^*_A and the Connes HKR decomposition for HC_*. Hence cyclic
homology carries only Kahler differential forms, and the trace pairing is integration —
the Haar functional already used. No new invariant can appear. Additionally:

* applying cyclic homology requires passing from a monoid (Frobenioid object monoid,
  splitting monoid) to an algebra, an arbitrary choice which destroys the mono-analytic
  structure on which the log-volume is defined (Prop 3.9 (ii): log-volumes are only
  compatible with the mono-analytic structure, and Remark 3.9.4 (ii) shows how sensitive
  they are to a wrong structure);
* the paper's own "realified semi-simplification" Rss is explicitly "in the spirit of the
  Grothendieck group" (K_0-level), not HC-level. The K_0-level statement is the one the
  paper uses, and it is already the log-volume.

Verdict: reject.

### 3.4 Index (K-theoretic / Fredholm / Toeplitz)

1. Type. An index is an integer (or a locally constant function in moduli); the paper's
   log-volume is a real number, continuous and unbounded in the scaling λ (log|λ| tends
   to -inf as |λ| tends to 0). Lean: no_locallyConstant_int_eq_neg_log — an
   integer-valued locally constant functional cannot equal -log (it is forced constant on
   [1,2], where -log takes the values 0 and -log 2).
2. Realification. The pilots are objects of realified Frobenioids (Def 3.8 (i)); an index
   lives on the integral K_0 before realification. The realification is precisely the
   quotient that makes log well-defined and simultaneously kills the integral lattice an
   index could detect. "log-volume = index" is therefore a category error; the only
   index-type statement available is the degree homomorphism K_0 -> Z -> R, which is again
   the log-volume's linear functional, not a new invariant.
3. Repo evidence. The existing determinant-line layer DeterminantLogVolumeActual.lean is
   rank one: determinantLine I = I, log-volume = log(absNorm I). There is no cohomology,
   no chi, no analytic torsion to index; the "determinant/index" picture collapses to the
   degree map.

Verdict: reject.

### 3.5 Regulators (Borel / Beilinson)

Regulators are real-valued homomorphisms on K_{2n-1}(F) tensor Q of a number field, i.e.
they see units and their polylogarithmic periods. The q-parameters q_v are local p-adic
quantities; the log-volume is a log of a measure on a log-shell, not a period. There is
no comparison map from the regulator of a number field to the Haar log-volume of a p-adic
hull, and none is expected: the two kinds of real numbers have different functoriality
(regulators are additive in K-theory classes, log-volumes are multiplicative in regions).

Verdict: reject.

---

## 4. The decisive obstructions (summary form)

O1 (object-level vs functional-level). Cor 3.12's content is the containment
imageSet_q subset hull_Theta together with the identification of the paper's hull with the
carrier the estimate is made on. The current exact gap ("paper Theta-pilot hull log vs
q[2u]/root-stack carrier") is a gap in constructing/identifying subsets of the paper's
carrier. A trace/index/regulator is a functional: it can evaluate a region, never build or
identify one. No functional-analytic framework can close a gap of this kind.

O2 (type mismatch: log vs linear). The paper log-volume satisfies
(a) scaling: L(λS) = L(S) + log λ (Prop 3.9 (i));
(b) Haar/translation invariance: L(a+S) = L(S) (Remark 3.9.4 (i));
(c) normalization: L(O) = 0.
A trace/index functional satisfies (d) additivity on disjoint unions. Lean proves that
(a), (b), (d) are inconsistent (no_additive_of_scaling_and_translation). Hence no linear
functional can be the log-volume; only log of a Haar measure is faithful, which is the
paper's own definition. (Log-sum-exp on unions is the signature of log of a measure.)

O3 (sign/positivity). Positive traces are nonnegative and monotone; the paper's signed
log-volume is <= 0 with normalization 0 at O, and its value is log|λ|. Passing to a
difference of positive traces destroys monotonicity, which is the only mechanism by which
containment implies the inequality. So a trace formulation cannot reproduce the proof
structure of Cor 3.12; it can only restate its conclusion.

O4 (torsion/root blindness). The pilots are "generators up to torsion" (Def 3.8 (i));
every trace/magnitude functional is invariant under μ_n (Lean:
trace_functional_blind_to_roots, norm_mul_of_pow_eq_one). Therefore an NCG realization is
blind to the μ_{2l}-root data by construction. It can never address the
"q[2u]/root stack carrier" half of the exact gap; and where the root data is essential
(the possible images relative to the Kummer isomorphisms, i.e. the very thing the hull of
Cor 3.12 is taken over), NCG says nothing.

O5 (multiradiality / no common container). Cor 3.12 is asymmetric: the Theta side is
subject to (Ind1)(Ind2)(Ind3), the q side is not (lines 1204-1234). A single trace (or a
single Hilbert space, or a single measure space) is a common container for the two
pilots. The paper's architecture is built precisely to avoid such a container; producing
one would be a strictly stronger theorem (a common ring/common mono-analytic realization
of the two pilots). If instead one only uses the common mono-analytic container (which
the paper does have), then the inequality is exactly the containment, already formalized
(S706/S722: globalQPilotLog <= globalThetaPilotHullLog). So the NCG route either
over-strengthens (unavailable) or trivializes (already done).

---

## 5. What does survive: positive byproducts usable now

P1. The paper's log-volume already is the trace picture. Remark 3.9.4 (i) is the
commutative case of "trace = integration", including the normalisation tau(1) = 1 ("multiply
by e, add 1") and the trace quotient Rss. The repo's IQHullLogVolumeInterface (monotone
ENNReal-valued logVolume, unitRegion, scaleShift with Haar invariance, hull subset
scaleShift '' unitRegion) is the same structure. So "express the log-volume as a trace" is
done; the formalization already contains it, and it is what makes the containment argument
work. Nothing is gained by renaming it "Dixmier" or "spectral".

P2. Index/trace normalisation dictionary (a correct explanation of the constants). For a
finite group G acting on a measure space, the canonical trace on the crossed product
satisfies tau(f) = (1/|G|) times the integral of f, i.e. the stacky volume of [X/G] is
mu(X)/|G|; equivalently 1/|G| is the reciprocal of the Jones index of C(X) inside C(X) x G.
With G = μ_{2l} this gives the canonical meaning of the paper's 1/(2l): the root-stack
normalization. Likewise 1/l^* is the trace of the label algebra (Plancherel normalisation
of the procession), and Remark 3.9.3 ("no weighted averages are possible") is the
rigidity/uniqueness of the trace normalization. This supports the repo's constants
order/(2l) and 1/l^* as canonical, but it cannot change them: an index normalization is a
scalar factor; it cannot repair a coefficient such as the (l+1)/24 of the
linear-coefficient model.

P3. Structural clarification of the (l+1)/24 tension. The paper's Theta side is a hull
(sup over possible images, hence a max of scalings, Remark 3.9.5 (i)) followed by a
procession average over capsules (Prop 3.9 (i),(ii)), where each capsule carries its own
log-volume and Remark 3.9.3 forces equal weights. It is not a linear coefficient
(sum over j of j^2/(2l)/(l^*)) times log q. Therefore the paper's Cor 3.12 does not assert
the coefficient inequality (l+1)/24 <= 1; that inequality belongs to the S704
linear-coefficient model, which S707/S722 already classify as a surrogate for the hull
log-volume. The NCG reading makes this structural point vivid (traces average over a
group; hulls take suprema; the paper uses both, at different levels), but it does not by
itself prove the paper's inequality either.

---

## 6. If the route is nevertheless to be pursued: the exact gaps to state

Any attempt to make the trace picture do work must supply the following, and none of them
is a trace/index statement:

G1 PaperHullScalingIdentification. For each b, identify the repo's perBThetaHullLog with
log|λ_Theta| for the actual paper λ_Theta of Remark 3.9.5 (i) (the smallest λ·O
containing the union of the possible images). This requires the possible-image subsets on
the paper carrier, i.e. exactly the current exact gap.

G2 PaperQPilotScalingIdentification. Identify the q-pilot image's scaling |λ_q| with the
paper q-pilot quantity, including the q[2u]/root-stack Kummer identification
(TwoLthRootKummer / root-stack section, not a completion root: S342).

G3 (only if a trace is insisted on) SignedTraceRealization. A signed trace functional on
the log-shell algebra with (i) omega-independence, (ii) homogeneity, (iii) log-sum-exp
compatibility on unions. By §3.1 and O2 such a functional, if it exists, is the Haar
weight with a sign convention; proving existence is P1 again.

G1/G2 are object-level and untouched by any of NCG, cyclic homology, index theory or
regulators.

---

## 7. Kill tests for any future "NCG for Cor 3.12" proposal

A proposal must answer all five; a "no" at any point falsifies it as a route to the paper
inequality.

1. Does it satisfy the paper normalization (mu^log(O) = 0, multiply by e gives add 1)? If
   not, it is not the log-volume.
2. Is its functional linear on disjoint unions (a trace/index)? If yes, it contradicts the
   scaling law (Lean no_additive_of_scaling_and_translation). If no, it is not a trace.
3. Does it see the 2l-root/Kummer data? If yes, it is not a trace/magnitude functional.
   If no, it cannot address the q[2u]/root-stack half of the gap (Lean
   trace_functional_blind_to_roots).
4. Does it derive the inequality from containment/positivity? Then it is the existing Haar
   monotonicity (IQHullLogVolumeInterface, S706/S722), not new mathematics. Does it derive
   it from integrality? Then it is a discrete invariant and cannot equal a continuous
   log-volume (Lean no_locallyConstant_int_eq_neg_log).
5. Does it produce a common container for the two pilots? If yes, flag it as a strictly
   stronger theorem (a common ring/mono-analytic realization), which is not available. If
   no, there is no trace comparison to make.

---

## 8. Lean artifact

tmp/sheaf/xif/paper/S732NCGLogVolumeNoGo.lean, compiled with lake env lean (exit 0),
axioms only propext, Classical.choice, Quot.sound (audited in
tmp/sheaf/xif/paper/_S732_axiom_audit.lean):

* PaperLogVolume (axioms of Prop 3.9 (i): normalization + scaling), logVol_hull
  (hull = log λ), logVol_hull_mono, cor312_scaling_iff (Cor 3.12 = scalar comparison).
* no_additive_of_scaling_and_translation (O2 in kernel-checked form).
* trace_functional_blind_to_roots, norm_mul_of_pow_eq_one (O4).
* no_locallyConstant_int_eq_neg_log (index discreteness, §3.4).

Limits of the artifact, stated honestly: it formalizes the structural no-go statements
above. It does not formalize Dixmier traces, the HKR theorem, or the Connes adele-class
spectral realization; those are discussed in §3 as mathematical facts/references, not as
Lean theorems. It also does not prove the paper inequality; the exact gaps G1/G2 (§6)
remain open and object-level.

---

## 9. Recommendation

Do not pursue the NCG/index/trace/regulator route for the final inequality. The gap is
object-level; the functional-level picture is already the paper's own integral/log
formalism and the repo's Haar/hull interface. The only concrete, faithful gains are:
(a) the Jones-index normalization reading of 1/(2l) and 1/l^* (P2), which can be recorded
as a short Lean lemma if a normalization audit needs it; (b) the explicit recognition, in
the ledger, that the S704 linear-coefficient model is a surrogate and that the (l+1)/24
coefficient belongs to it, not to the paper's hull log (P3).

Recommended next exact step (not NCG): construct the paper's possible-image subsets for
the Theta-pilot on the root-stack/extension carrier (hodgeTwoLthRoot), then identify
perBThetaHullLog with log|λ_Theta| (G1). That is the actual reduction of the exact gap.
