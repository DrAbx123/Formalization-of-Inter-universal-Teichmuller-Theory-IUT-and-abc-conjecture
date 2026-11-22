# W8 memo: configuration space / persistent topology for the qPilot–Theta comparison

Date: 2026-10-30
Status: research memo + two compiled Lean no-go files; no fake carrier, no surrogate target,
no target change, no new axiom.

Companion kernels:
* tmp/sheaf/xif/paper/W8ConfigurationSpaceNoGoActual.lean
  (Q_p local model; lake env lean EXIT=0; main declarations depend only on
  [propext, Classical.choice, Quot.sound]; no sorryAx).
* tmp/sheaf/xif/paper/W8BlockNoGoActual.lean
  (actual one-factor paper tensor block; lake env lean EXIT=0; main declaration depends only on
  [propext, Classical.choice, Quot.sound]; no sorryAx).
* Logs: tmp/sheaf/xif/paper/logs/W8_padic_no_go.log, logs/W8_block_no_go.log.

Related actual files: S793 (least lambda-O hull), S799 (hull-log formula), S800/S801 (hull first),
S810 (least-hull paper carrier), S814 (value-group skeleton and quantization), S822 (p-adic
determinant / log-volume), S782 and S824 (finite root stack and its Haar), S858/S873/S875/S881/S883/S884
(PaperGap intrinsic volume), S860/S876/S877/S888 (global weighted target and Hq/Htheta),
PaperLevelXiFTargetProofActual and RootNormalizedContainmentActual (per-b scalar inequality),
QVFamTensorCoefficientActual (the one-factor block), FinitePadicTensorTopology (the block topology).

## 0. Verdict (Chinese summary)

1. **The configuration space exists, but it is exactly the join of S793.** For each bad place b the
   exponent space is C_b = (qVFamTensorV -> Real); in the actual formalization qVFamTensorV = Unit,
   so C_b = Real (one-dimensional). The region map Phi(c) = F(c) * O is order-reversing. The
   basepoint is cRoot = order/(2l). The possible Theta images are the finite chain
   {Phi(j^2 cRoot) : 1 <= j <= l*}. The least lambda-O hull is the join of this chain and equals
   Phi(cRoot). This is a kernel-checked theorem (S793:91-153, S801:36-39, S810:34-40); no topology
   is used or needed.

2. **Paths/homotopy cannot give the log.** On the actual paper block (W8BlockNoGoActual.lean,
   kernel-checked): O and pU * O are homeomorphic (multiplication by the prime scalar unit pU), but
   their actual normalized Haar logs are 0 and -log p. Hence no functional of the region that is
   invariant under ambient homeomorphisms (hence under homotopy type or singular homology) can agree
   with the hull log. This is an exact no-go, not a missing construction.

3. **Paths in the carrier are degenerate.** Q_p is totally disconnected; every continuous map from
   the interval (indeed from any preconnected space) is constant; every path-connected subset is a
   subsingleton (W8ConfigurationSpaceNoGoActual.lean, kernel-checked). Thus "qPilot and Theta are
   path-connected in the carrier" is literally false.

4. **In the exponent parameter space path-connectedness is universal.** C_b is convex, so any two
   points are joined by a path. Because it holds for every pair, it cannot imply a directional paper
   inequality. This is formalized: universal_relation_not_imply plus the explicit countermodel
   path_connected_does_not_imply_log_comparison (W8ConfigurationSpaceNoGoActual.lean). Concretely,
   the exponent vectors 0 and 1 are path-connected, but the comparison 0 <= -log p fails.

5. **Persistent homology sees only relative label data.** The label cloud {j^2 cRoot} lies on a line.
   The Vietoris-Rips/Cech persistence module is invariant under translations of the cloud, whereas
   the log changes by -k log p under a shift by k. PH can recover the minimizing label (j = 1, i.e.
   cRoot), which is already known; it cannot give the absolute log. Moreover PH is invariant under
   replacing an exponent by its value-group ceiling, while the exact paper formula needs the value
   group to realize cRoot; when the ceiling is strictly larger the naive formula -sum cRoot log p is
   false (S814:318-345, kernel-checked).

6. **The real global gap is the norm equality c_norm = order.** The actual per-b inequality
   qPilot(c_norm) <= hull(c_norm/(2l)) is unconditional (PaperLevelXiFTargetProofActual:72-77). The
   paper normalization order/(2l) requires c_norm = order (the S824 dichotomy; S877/S888 reduce the
   weighted Hq/Htheta bridges exactly to it). This is an equality of two numbers attached to the same
   q, not a deformation.

**Verdict: reject W8 as a proof route for the least lambda-O hull log or for the qPilot/Theta
comparison.** Accept it only as (i) a restatement of S793's join, (ii) the S814 skeleton/order+measure
picture, (iii) the S824 stacky 1/(2l) normalization (the only genuine transformation space). No new
target, no new axiom, no target change. The only inputs that would revive the route are an exact
value-group generator at cRoot (the scaling data) or a proof of c_norm = order; both are
arithmetic/norm statements, not topology.

## 1. The actual objects and the exact current state

### 1.1 Carrier and coefficients

* qVFamTensorV = Unit (QVFamTensorCoefficientActual:60); the block is
  ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
  (QVFamTensorCoefficientActual:72-73). It carries the finite-dimensional Q_p topology of
  FinitePadicTensorTopology:52-61 (norm induced from coordinates).
* Paper root coefficient cRoot = order/(2l), constant on the single factor
  (QVFamRootFactorCorrectionActual / BadPlacePaperRootThetaHullActual; quoted in S793:64-77).
* Labels: SignedLabel l = {j : Int // -(l*) <= j <= l*}, l* = (l-1)/2 (GaussianKernel:93-96,
  FiniteLabels:28). Nonzero labels modulo +- are j = 1,...,l*. The Theta image at label j is the
  lambda-O region at exponent j^2 * cRoot (S793:72-80). The label j = 1 has exponent exactly cRoot
  (SignedLabelOneActual:15-28).

### 1.2 The least hull and the qPilot region

* S793 defines the candidate lambda-O regions, the image union, the least hull as the intersection of
  all candidates, and proves paperLeastLambdaOHull = Phi(cRoot) (S793:82-153).
* S801 proves paperLeastLambdaOHull = paperQPilotRegionPaperOrder by rfl (S801:36-39); S810 records the
  same object as the corrected paper carrier (S810:34-40, 55-66). Thus, as a set, the Theta hull and
  the paper-order qPilot region are the *same* region. The comparison is an equality of sets; its
  numerical content is the identification of the Haar log with the paper value, not the existence of a
  hull or of a path.
* The old union/closure hull is only a superset; the exact reverse gap is
  S810LeastEqualsOldUnion (S793:155-176, S810:47-51).

### 1.3 The actual log values

* For a unit u of the block, the normalized Haar log of u * O is
  (1/d) * log(padicDet u), d = finrank_Qp(block) (S822:117-146). This is unconditional in u (no
  scaling data).
* For the prime scalar unit pU, the log is -log p:
  arithmeticTupleNormalizedLogVolume_primeScalar_zpow (FinitePlaceNormalizedUnitScalingLogVolume:510-519),
  used in W8BlockNoGoActual.lean at k = 0 and k = 1.
* For a general exponent vector c, the exact formula -sum c log p requires
  ArithmeticTuplePureFractionalScalingData at c: S799:59-80, S822:242-249, S814:293-310. The value
  group obstruction is S814:318-345.

### 1.4 The global target and its exact bridges

* The actual per-b scalar inequality qPilot(c_norm) <= rootThetaHull(c_norm/(2l)) is unconditional
  (RootHullContainmentInequality:123-133; PaperLevelXiFTargetProofActual:57-77).
* The weighted global target is S860:44-49; the corrected global target and its exact gap are
  S876:36-72; the reduction to HqCorrected and HthetaCorrected is S877:43-107; both are reduced to
  per-b c_norm = order in S877:92-103 and S888:50-109 (Htheta also needs
  S810LeastEqualsOldUnion).
* The PaperGap interface (signed hull log = least-hull log, plus the intrinsic log-shell volume) is
  S858:58-80; the actual root volume is S884:80-103; the single exact field is the scaling data.

## 2. The W8 construction, made precise

### 2.1 Exponent configuration space

Let C_b = qVFamTensorV -> Real (one-dimensional in the actual model) and Phi_b(c) = F(c) * O_b, where
F(c) is the fractional tensor lattice at exponent vector c and O_b is the holomorphic lattice. Then:

* Phi_b is order-reversing: c <= c' implies Phi_b(c') subset Phi_b(c)
  (S793:108-116, using arithmeticTupleFractionalLattice_mono).
* Phi_b is not injective on Real: it depends only on the value-group ceiling of c; two exponents in
  the same value-group interval give the same ball (S814:288-310, quantization invariance).
* The basepoint is cRoot. The possible Theta images are Phi_b(j^2 cRoot), j = 1,...,l*. The least
  hull is join_j Phi_b(j^2 cRoot) = Phi_b(cRoot), because j^2 >= 1 and j = 1 is present (S793:94-153).
* Global configuration space: the product over b of C_b, dimension #Bad. The paper target is a
  weighted sum over b, not a product, so the global comparison is coordinatewise per b.

Dimension accounting ("dimension from labels / intermediate objects"):
* label direction: l* points (l* = (l-1)/2), a finite discrete set, dimension 0; the nonzero signed
  labels modulo +- are exactly l*.
* exponent direction: 1 per bad place (qVFamTensorV = Unit); #Bad globally.
* carrier: Q_p-dimension d = finrank_Qp(block) (one factor: the local degree); as a topological space
  the carrier is zero-dimensional and totally disconnected.
* Hence there is no high-dimensional manifold in the actual objects. The only "high-dimensional"
  quantity is the Q_p-dimension d of the carrier, and the log is a linear functional on the
  one-dimensional exponent line, not on the d-dimensional carrier.

### 2.2 The hyperspace of regions

The family {Phi_b(c) : c in Real} with the Hausdorff metric is homeomorphic to the value-group
quotient (a real interval in the one-factor case); it is not a manifold with interesting topology,
and the least hull is a single point of it. The finite image family {Phi_b(j^2 cRoot)} is a finite
discrete chain. Neither version produces a nontrivial homotopy type.

### 2.3 Label nerve and persistent homology

The image family is a chain
  Phi_b(l*^2 cRoot) subset ... subset Phi_b(4 cRoot) subset Phi_b(cRoot).
The nerve of a chain is a point. In the Vietoris-Rips/Cech filtration of the finite point cloud
{j^2 cRoot} on the line, the persistence module records only the relative distances
(j'^2 - j^2) cRoot; all bars are finite except the last, and the minimizing label j = 1 is the only
extremal datum. There is no positive-degree homology from a finite point cloud, and the p-adic balls
themselves are totally disconnected. Persistent homology therefore recovers the label minimum, not
the absolute value cRoot or the log.

### 2.4 The only genuine transformation: the unit action

The correct "transformation in a space" is the action of the unit group U = (block)^x on the set of
lambda-O regions: u * Phi_b(c) = Phi_b(c + v(u)), where v is the valuation vector (in the one-factor
case v(u) = -log_p(norm u)). The orbit of the basepoint O is the family of unit-scaled canonical
regions. The normalized log is the homomorphism
  u |-> (1/d) * log(padicDet u) = (1/d) * log(dHC u),
i.e., a character U -> Real (S822:102-146). The qPilot/Theta comparison is the inequality of the
values of this character on the relevant elements. This is a precise construction; it is S822, not a
new topological input. The character is nontrivial on homeomorphic regions, which is exactly the
no-go of section 3.1.

### 2.5 The stacky version

The finite root stack L(mu_2l) (S782) with the mu_2l-action is the only place where a genuine finite
group acts. Its Haar measure is mu_2l-invariant, and the log-divisor identity
log V(root) = (1/(2l)) log V(q) is a theorem (S824:125-138; W1 memo 2.1-2.3). This gives the paper's
1/(2l) normalization, not the least-hull log; the identification of the two is equivalent to
c_norm = order (W1 memo 3.2; S824 dichotomy).

## 3. No-go theorems

### 3.1 N1: no homeomorphism-invariant log on the actual block (kernel-checked)

File: W8BlockNoGoActual.lean, theorem no_homeomorphism_invariant_block_log.

Statement: let O be the canonical unit reference of the actual block and pU the prime scalar unit.
For any additive Haar mu and any F : Set(block) -> Real,
  if F(h '' S) = F(S) for every ambient homeomorphism h,
  then it is not the case that
    F(O) = normLog_mu(O) and F(pU * O) = normLog_mu(pU * O).

Proof: pU is a unit, so x |-> pU * x is a homeomorphism (Homeomorph.smul pU), and it carries O onto
pU * O. Hence any homeomorphism-invariant F has F(pU * O) = F(O). But the actual log values are 0 and
-log p (S822 prime scalar zpow, k = 0 and k = 1), and log p != 0. Contradiction.

Consequence: every invariant of the region that factors through the homeomorphism type -- homotopy
type, singular homology, Euler characteristic, the fundamental groupoid, any "shape" -- is constant on
this family and cannot be the log. This includes any candidate "topological degree" or "persistent
homology" of the region itself.

### 3.2 N2: paths in the p-adic carrier are constant (kernel-checked)

File: W8ConfigurationSpaceNoGoActual.lean, theorems padic_path_eq,
padic_isPathConnected_subsingleton, padic_no_nontrivial_pathConnected.

Statement: every path gamma : Path x y in Q_p has x = y; every path-connected subset of Q_p is a
subsingleton; there is no path-connected subset with two distinct points.

Proof: Q_p is ultrametric, hence totally separated, hence totally disconnected
(Mathlib: Topology/MetricSpace/Ultra/TotallySeparated, instance chain). The interval is preconnected,
so the image of a path is preconnected, hence a subsingleton. This is a literal refutation of
"qPilot and Theta are path-connected" as a statement about points of the carrier.

For the actual block, the same conclusion follows from the coordinate linear isometry
finitePadicTensorCoordinates : block ~ (Index -> Q_p) (FinitePadicTensorTopology:48-58): the target is
a finite product of totally disconnected spaces, hence totally disconnected, and an isometry is a
homeomorphism. This block-level total disconnectedness is not formalized in the two companion files
(the block-level file uses only the homeomorphism, which suffices for N1); it is a standard
consequence of the cited instances.

### 3.3 N3: path-connectedness cannot imply the directional comparison (kernel-checked)

File: W8ConfigurationSpaceNoGoActual.lean, theorems universal_relation_not_imply and
path_connected_does_not_imply_log_comparison.

Statement: let P be a relation that holds for every pair (e.g. Nonempty(Path a b) on a path-connected
space) and Q a relation that fails somewhere. Then P does not imply Q. On the one-factor exponent
space the log is exponentLog P c = -(sum c) log P (the shape of S864.paperLambdaOLogVolume). The
points 0 and 1 are path-connected, but exponentLog P 0 <= exponentLog P 1 fails (0 <= -log P is
false). Hence "path-connected" alone has no discriminating power for the paper inequality.

This is the exact logical defect of the proposed inference "both sides are path-connected, therefore
compatible". The paper inequality is directional (qPilot log <= hull log); path-connectedness is an
equivalence relation and, on the convex exponent space, universal.

### 3.4 N4: persistent homology is translation-invariant, the log is not

Proof sketch (not formalized as a PH theorem; the underlying invariance is elementary). The label
cloud is {j^2 cRoot : 1 <= j <= l*} in Real. Translating the cloud by k (i.e., replacing cRoot by
cRoot + k) translates every ball in the Vietoris-Rips/Cech filtration, hence induces an isomorphism of
persistence modules. But the normalized log of the hull changes by -k log p. Therefore the persistence
diagram cannot determine the absolute log; it can only determine relative label differences and the
minimizing label. The same argument applies to any construction that uses only the order/incidence
structure of the label set.

### 3.5 N5: quantization is invisible to topology, but decisive for the log (in-tree kernel-checked)

The exact formula -sum c log p requires an exact generator of norm p^{-c} at every coordinate
(ArithmeticTuplePureFractionalScalingData; S799:59-68, S822:242-249, S814:293-310). The value group of
a p-adic completion is (1/e_K)Z, so a general fractional c is only seen through its ceiling. S814
proves:
* if the ceiling admits exact generators, the hull log is exactly -sum c' log p at the ceiling c'
  (S814:293-310);
* if the ceiling is strictly larger coordinatewise, the naive value -sum cRoot log p is *false*: the
  true log is strictly smaller (S814:318-345).
Topology and PH are invariant under the ceiling (the region is literally the same set), so they cannot
certify the paper's fractional exponent. This is precisely the arithmetic gap, not a topological one.

### 3.6 N6: the global bridge is a norm-instance equality

The weighted HqCorrected and HthetaCorrected are reduced to per-b
qVFamNormalizedCoefficient = order (S877:92-103, S888:50-109). S824 proves the dichotomy: the
degree-normalized stacky log equals the least-hull log iff c_norm = order. This is an equality of two
real numbers attached to the same local q (spectral normalized norm vs valuation order); no continuous
deformation or homotopy can change it. Persistent homology cannot supply it.

## 4. What survives (positive)

### 4.1 P1: the skeleton dictionary (S814), the correct "space" picture

S814 identifies the local lambda-O region with a segment [c, infinity) of the value-group skeleton, the
containment with segment inclusion, and the normalized log with minus the skeleton length
c log p (S814:83-192). The q-pilot segment [order, infinity) contains the paper hull segment
[order/(2l), infinity) because order/(2l) <= order, and monotonicity of the normalized log gives the
paper inequality
  paperSkeletonQPilotLog <= paperLeastLambdaOHullLog
unconditionally (S814:237-270). This is the honest space picture: order + Haar length. It is not
homotopy, and it does not produce the exact hull-log formula.

### 4.2 P2: the p-adic determinant makes the log a character (S822)

The normalized log of u * O is (1/d) log(padicDet u), padicDet is a monoid homomorphism, and the
p-adic Monge-Ampere second difference vanishes (S822:89-206). Thus the log is affine in the exponent and
is determined by its values on the value-group generators, not by the topology of the region. This is
the correct cohomological formulation: the log is a character/1-cocycle of the unit group, not a
homotopy invariant of the hull.

### 4.3 P3: the stacky quotient (S782, S824)

The finite root stack L(mu_2l) with the actual mu_2l-invariant Haar measure is the only genuine
"space with a transformation" in the paper's normalization. It gives the unconditional 1/(2l)
log-divisor identity and branch independence (S824; W1 memo 2.1-2.4). It does not give the hull log;
the identification is the kernel-checked dichotomy of W1 memo 3.2.

### 4.4 P4: the exact reformulation of compatibility

The paper comparison is exactly
  Phi_b(cRoot) subset Phi_b(c_norm)  <=>  cRoot <= c_norm coordinatewise
  <=>  the q-pilot skeleton segment contains the hull segment,
plus the numerical identification of the hull log with the paper value (scaling data / c_norm = order).
None of these is a path statement.

## 5. Why the idea looks right and where it is mislocated

The paper's inequality is between measures of regions: log mu(hull) vs log mu(qPilot region). The
functional is monotone under inclusion and linear on exponents. Both properties are outside topology:
* inclusion is an order relation, already handled by S793 in two lines;
* the numerical value is a measure (Haar) value, handled by S822/S814, and it requires the value group
  (quantization) and the norm comparison (c_norm = order).
The only actual "transformation" in the paper is the mu_2l ambiguity and the 2l-root normalization;
that is a finite group action and a measure identity (S824), not a homotopy. The proposed
configuration space is therefore either (a) the exponent space, where everything is convex and
path-connected (no information), or (b) the hyperspace of regions, where all elements are homeomorphic
(no information), or (c) the carrier, where paths are constant (false statement).

## 6. Kill test

A candidate W8 construction must produce, from the configuration space alone, a nonconstant function on
the family {Phi(c)} that equals the /normalized log/. The no-go results forbid this in three
independent ways:
* N1 forbids any homeomorphism-invariant function (in particular any homotopy invariant, homology
  invariant, or PH of the region);
* N3 forbids any merely path-connectedness-based argument, because path-connectedness is universal on
  the exponent space and cannot select a direction;
* N5 forbids any construction that sees only the region and not the value-group realization: the
  region is unchanged by the ceiling while the log changes.
The only remaining possibility is a construction that carries the Haar measure or the value group. Such
a construction is exactly S822/S814, i.e., the current route, not a new one.

Explicit countermodel to the inference (kernel-checked): on the one-factor exponent space, every two
points are path-connected, including (0, 1); but exponentLog P 0 <= exponentLog P 1 is false for
P > 1. Hence path-connectedness does not imply the comparison.

## 7. Recommendation and next executable step

1. Do not open a new W8 Lean target beyond the two no-go files. Do not add an axiom, do not change the
   target, do not replace the least hull by a surrogate.
2. Keep the two no-go files as the W8 record; they are kernel-checked and independent of the remaining
   arithmetic gaps.
3. The actual next steps remain (priority order):
   (a) c_norm = order (S736/S824/S877/S888) -- highest leverage: closes Hq and (with the least=old
       union equality) Htheta;
   (b) the completion scaling data at cRoot, or a direct value-group computation of the least-hull
       log (S799/S814/S875/S883/S884);
   (c) S810LeastEqualsOldUnion;
   (d) the PaperXiFSourceLink fields (TASK_LEDGER:88-101).
   All are arithmetic/measure/norm statements; W8 does not change their status.
4. If the user wants the "space" language to be used, the only defensible statements are:
   * the exponent segment/skeleton picture (S814) -- order + length;
   * the unit-action character picture (S822) -- the log is a character of U;
   * the finite root stack quotient (S782/S824) -- the 1/(2l) measure identity.
   Each is already in the tree; none is a homotopy statement.

## 8. Evidence and inventory

### 8.1 W8ConfigurationSpaceNoGoActual.lean

* lake env lean EXIT=0 (logs/W8_padic_no_go.log, attempt 1).
* Main declarations and axioms:
  - no_homeomorphism_invariant_padic_log : [propext, Classical.choice, Quot.sound]
  - padic_path_eq : [propext, Classical.choice, Quot.sound]
  - padic_isPathConnected_subsingleton : [propext, Classical.choice, Quot.sound]
  - path_connected_does_not_imply_log_comparison : [propext, Classical.choice, Quot.sound]
* SHA256 DC863558D9B24166FA3BA5D24CF66657FC7090EF7C1ED7E68872118DBEF244E9; 9256 bytes; 202 lines.
* No sorry, no admit, no axiom declaration; the token scan hits are comments and #print axioms.

### 8.2 W8BlockNoGoActual.lean

* lake env lean EXIT=0 (logs/W8_block_no_go.log, attempt 1).
* no_homeomorphism_invariant_block_log : [propext, Classical.choice, Quot.sound].
* SHA256 01E2CC86AFCC9D9B50F6EEC4E39BC8052BFE9564B77C8038C67C8AE72563119E; 5976 bytes; 132 lines.
* No sorry, no admit, no axiom declaration.

### 8.3 What is not formalized (honest list)

* Total disconnectedness of the actual tensor block (the proof route is
  FinitePadicTensorTopology:48-61 plus the Pi of Q_p; N1 does not need it).
* The translation-invariance no-go for persistent homology (N4 is an elementary argument, not a Lean
  theorem).
* Singular homology vanishing in positive degrees for the carrier (Mathlib has
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace; not invoked in the W8 files).
* The PH algorithm and any specific persistence diagram of the label cloud.
* The transfer of the carrier path no-go to the block (N2 is formalized on Q_p; the block version is a
  coordinate-isometry argument).

### 8.4 Files read for this memo

TASK_LEDGER.md; S793PaperLeastLambdaOHullActual.lean; S799LeastLambdaOPaperTargetActual.lean;
S800LeastLambdaOHullActual.lean; S801PaperHullLogActual.lean; S782FiniteRootStackExtensionActual.lean;
S810LeastHullPaperCarrierActual.lean; S814 (skeleton) and S814PaperHullLogInterfaceActual;
S822PadicDetHullActual.lean; S824RootStackyHaarVolumeActual.lean and W1_STACKY_HAAR_MEMO.md;
S858PaperGapConditionalCor312Actual.lean and .md; S860GlobalCor312AuditActual.lean;
S873/S875/S876/S877/S880/S881/S883/S884/S886/S888 (the 2026-10-30 batch);
PaperLevelXiFTargetProofActual.lean; RootNormalizedContainmentActual.lean;
RootHullContainmentInequalityActual.lean; QVFamTensorCoefficientActual.lean;
PaperSymbolTypesActual.lean; SignedLabelOneActual.lean;
FinitePlaceNormalizedUnitScalingLogVolume.lean; FinitePadicTensorTopology.lean;
Mathlib: TotallyDisconnected/PathConnected/ConstMulAction/Padic API.

### 8.5 Unrun / not verified

* The full project build was not run; only the two W8 files were compiled, each with lake env lean.
* No comparator or target-type acceptance was run for W8; the no-go files do not touch the paper
  target, so no comparator is applicable.
* The concurrent build in the workspace caused transient olean read errors during compilation; the
  logs record the successful attempt 1. The two successful runs are the ones cited.
