# Task F memo: equivariant homotopy / equivariant K-theory / Bredon cohomology / orbifold stacks for the mu_{2l} root stack

Date: 2026-10-30
Status: research memo; no fake carrier, no surrogate target, no change of target.
Companion compiled kernel: tmp/sheaf/xif/paper/TaskFEquivariantOrbifoldKernel.lean
(compiled with lake env lean, EXIT=0; it proves only the elementary
normalization/log-invariance facts, not any paper identification).
Related repo probes: S735ProbeMathlibRootStackTools.lean (Mathlib API names),
S346/S356/S392 (orbifold spec / action groupoid / section monoid),
S342/S719 (completion-root impossibility), S736 (spectral c_norm vs paper order).

## 0. Executive verdict (中文摘要)

1. Equivariant homotopy theory, equivariant K-theory, and Bredon cohomology
   cannot serve as the paper-faithful carrier of q[2u]. They see only the free
   mu_{2l}-orbit (the root torsor), and when the root exists the torsor is
   trivial: all genuine equivariant invariants are those of mu_{2l} itself and
   are independent of q_v and of the actual root r. The actual root unit, its
   norm, and its log are not equivariant homotopy / K-theory / Bredon classes.
   Refuse as carrier.

2. Orbifold stacks do supply the correct invariant log-volume normalization.
   The quotient/stacky measure of a finite free action gives the factor
   1/|G| = 1/(2l); equivalently the log-volume element on the root line is
   (1/(2l)) dlog|q|, and the volume of a fundamental domain (one branch of
   q[2u]) is (1/(2l)) times the q-volume. This is exactly the paper coefficient
   order(q_v)/(2l). The action groupoid keeps the actual roots as objects, and
   the log is mu_{2l}-invariant because roots of unity have norm one. So the
   orbifold route is paper-faithful for the normalization and for the
   branch-independence of the log, and it is the natural home of the paper
   phrase "Theta value determined up to mu_{2l}".

3. However, the orbifold route does NOT construct the paper q_v or its root,
   does NOT supply the paper lambda-O hull, and does NOT prove
   paperRootThetaHullLog = paperRootThetaFormulaLog. It can only reformulate
   the coefficient order/(2l) as a stacky measure normalization instead of a
   completion-valued fractional scaling generator. The exact hull equality
   (PaperRootHullSetGap) and the paper q_v/root construction remain exact gaps.
   In the completion carrier the fractional scaling data is impossible
   (S342/S719), so no orbifold or equivariant object can fill
   PaperRootHullFormulaGap on that carrier.

4. Concrete usable statements (Lean-ready, Mathlib names verified by S735):
   Torsor, Equiv.smulConst, and especially
   MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self:
   for a finite group G, a G-invariant measure mu, a fundamental domain s and a
   G-invariant set t, mu t = |G| * mu (t inter s); the quotient/stacky measure
   is mu t / |G| = mu (t inter s). The compiled kernel proves
   log (r^n) = log r * n, the root scaling log r = log q / n, norm of a root of
   unity = 1, log-invariance under root-of-unity multiplication, and the finite
   regular-orbit average.

## 1. The paper object and the current exact gap

### 1.1 Paper object

* q[1u] = q_v: the single-underline q-parameter.
* q[2u] = q_v^(1/2l): the double-underline 2l-th root.
* Paper theta value at label j: q[2u]^(j^2) = q[1u]^(j^2/(2l)).
* Paper root coefficient: qVFamPaperRootCoefficient = order(q_v)/(2l)
  (QVFamRootFactorCorrectionActual.lean, lines 54-57).
* Paper Theta hull log: paperRootThetaHullLog T b mu, the normalized log of
  paperRootThetaHull, with expected formula
  paperRootThetaFormulaLog T b =
    -((sum over qVFamTensorV, qVFamPaperRootCoefficient) * log p)
  (BadPlacePaperRootThetaHullActual.lean).
* Paper root correction (PAPER_ROOT_CORRECTION.md): the paper q_v is a K-side
  Tate parameter, and q_v^(1/2l) is an element of the monoid O^tri_{K_v} of
  nonzero integral elements of K_v, not a completion root and not a root-stack
  class in the paper text. The repo qVFamily is a Clause B native source
  parameter with order coprime to l; it is not identified with paper q_v.
  S342 rules out a completion 2l-root for qVFamily only.

### 1.2 Current repo root-side facts

* TwoLthRootKummerActual.lean: actual algebraic-closure root
  hodgeTwoLthRoot, with hodgeTwoLthRoot_pow:
  hodgeTwoLthRoot^(2l) = qVAlgClosedUnit; the root set is a mu_{2l}-torsor
  (twoLthRoot_ratio_mem_mu).
* S709RootImageRadiusFormulaActual.lean: the actual extension root norm is
  rootImageRadius = p^(-c_norm/(2l)) where c_norm is the spectral normalized
  coefficient (see S736).
* S736RootNormCoefficientAuditActual.lean: rootNormCoefficient is the
  generator-supply spectral c_norm, NOT the paper order; the identification
  spectral c_norm = order(qVFamily) is an exact gap (S736PaperOrderGap).
  Consequently perBThetaHullLog (which uses rootHalfCoefficient = c_norm/(2l))
  and paperRootThetaHullLog (which uses paperRootCoefficient = order/(2l)) are
  different objects until S736PaperOrderGap is proved.
* S346OrbifoldStructuralSheafActual.lean / S356RootStackActionGroupoidActual.lean
  / S392RootStackSectionMonoidActual.lean: the existing orbifold interface,
  the nondegenerate mu_{2l} action groupoid on algebraic-closure roots, and the
  function-monoid candidate. S356 records RootStackMonoidSectionCarrier as an
  exact missing object; S392 uses qSection/rootSection only at the value level
  and assumes a q-coordinate.

### 1.3 Exact hull/coefficient gaps

* PaperRootHullFormulaGap T b (BadPlacePaperRootThetaHullActual.lean):
  data : ArithmeticTuplePureFractionalScalingData at the fractional
  paperRootCoefficientFamily = order/(2l), plus hull_eq : paperRootThetaHull
  equals the fractional-lattice times holomorphic-lattice region.
* S719PaperRootHullGapDecompositionActual.lean:
  PaperRootHullFormulaGap iff Nonempty PaperRootHullScalingDataGap and
  PaperRootHullSetGap. The scaling-data part at a fractional completion
  coefficient is impossible (S342/S719: it is equivalent to a completion
  2l-th root of q[1u]). So this gap cannot be filled on the completion carrier.
* The set part PaperRootHullSetGap (hull = fractional-lattice region) is a
  separate arithmetic/geometry statement; the orbifold route does not prove it.
* The paper signed-hull consumer: PaperSignedHull with
  signedHullLogVolume = -ambient.logVolume ambient.hull; S716 uses
  paperPerBThetaHullLog; S726 proves the s663 positive-theta-average equality
  is false. The correct paper comparison is on the paper hull log, not on a
  theta-value average.

## 2. Four structural facts that decide the question

### F1. The root set is a free transitive mu_{2l}-torsor

If r and r' are two 2l-th roots of q != 0, then (r'/r)^(2l) = 1, so r'/r is
in mu_{2l}. The set Root(q) is nonempty by the paper 2-torsion/root assumption;
choosing r gives a mu_{2l}-equivariant bijection
  mu_{2l} -> Root(q),  zeta |-> zeta * r.
The action is free (zeta * r = r implies zeta = 1 since r != 0) and transitive.
Hence Root(q) is the regular mu_{2l}-set, and the quotient Root(q)/mu_{2l} is a
point. The actual root r is a trivialization of this torsor, not an invariant
of it. This is the precise structural reason why equivariant homotopy,
K-theory, and Bredon cohomology cannot see r.

### F2. Roots of unity have norm one; the log is invariant and is determined by q

In any normed field, if zeta^n = 1 with n > 0, then ||zeta||^n = 1 and
||zeta|| >= 0, so ||zeta|| = 1. Therefore for any root r and any zeta in
mu_{2l},
  ||zeta * r|| = ||r||,  log ||zeta * r|| = log ||r||.
The log is a mu_{2l}-invariant function on the torsor. Moreover, from
r^(2l) = q,
  log ||r|| = (1/(2l)) log ||q||,
and for the paper theta value r^(j^2),
  log ||r^(j^2)|| = (j^2/(2l)) log ||q||.
Thus the log-volume does not require choosing a root; it only requires root
existence. This is why the paper can say the theta value is determined up to
mu_{2l} and still have a well-defined log-volume. The compiled kernel proves
these facts (TaskFEquivariantOrbifoldKernel.lean).

### F3. The mu_{2l}-orbit average of the theta value is zero, not the theta value

Under zeta : r |-> zeta * r, the theta value r^(j^2) goes to
zeta^(j^2) r^(j^2). For 0 < j < 2l we have 2l not dividing j^2, so
  (1/(2l)) sum_{zeta in mu_{2l}} zeta^(j^2) = 0.
This is the finite Fourier/Gauss calculation of S689_GAUSS_ORBIT_MEMO.md. It is
a concrete obstruction: no construction that averages the signed theta value
over mu_{2l}, and no Bredon/K-theoretic invariant class built from that
average, can recover the paper theta value. Only the modulus/log survives the
group action. The paper's log-volume is therefore correctly a G-invariant
scalar, not an equivariant cohomology class.

### F4. The stacky measure of a finite free action gives the 1/|G| factor

Let a finite group G act on a measured space (X, mu), preserving mu, with a
fundamental domain s. For a G-invariant measurable set t,
  mu t = |G| * mu (t inter s)
(Mathlib: MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self;
verified by the S735 probe). The quotient/stacky measure is
  mu_stack(t) = mu t / |G| = mu (t inter s).
For the root torsor this is the exact source of the 1/(2l) normalization. In
log coordinates, the root line carries dlog|r|; the q-line carries
dlog|q| = 2l dlog|r|; the quotient/stacky measure is (1/(2l)) dlog|q|. The
volume of a fundamental domain (one branch of q[2u]) is (1/(2l)) times the
q-volume. This is exactly q[2u] = q[1u]^(1/(2l)) at the log-volume level.

Normalization dictionary:

| object | log |
|---|---|
| q[1u] = q | log ||q|| |
| q[2u] = r, r^(2l) = q | (1/(2l)) log ||q|| |
| q[2u]^(j^2) = r^(j^2) | (j^2/(2l)) log ||q|| |
| paperRootCoefficient | order/(2l) |
| stacky volume element | (1/(2l)) dlog|q| |

With the sign convention of the paper, log ||q|| = -order(q) log p, so
-log ||r|| = (order/(2l)) log p, which is the positive paper coefficient. This
matches paperRootThetaFormulaLog.

## 3. Equivariant homotopy theory

### 3.1 Concrete objects and theorems

* Genuine G-spaces, G-CW complexes, equivariant homotopy groups
  pi_n^H(X); tom Dieck, Transformation Groups (1987); May, Equivariant
  Homotopy and Cohomology Theory (1996).
* Borel construction X_{hG} = EG x_G X; for a free G-space, X_{hG} is
  homotopy equivalent to X/G.
* Free G-spaces are equivariantly equivalent to spaces over BG: the
  G-homotopy type of a free G-space X is the pullback of EG -> BG along the
  classifying map X/G -> BG (Elmendorf, Systems of fixed point sets, 1983;
  this is the free case of the isotropy-separation equivalence).
* tom Dieck splitting: for a G-spectrum, the fixed-point/geometric
  decomposition has contributions from conjugacy classes of subgroups H; for a
  free G-space only H = e contributes, so the equivariant stable homotopy type
  is the non-equivariant type of X/G.

### 3.2 What it preserves

The mu_{2l}-action and the torsor structure: yes. The actual root r, its norm,
and its log: no. Since Root(q) is the regular orbit and the quotient is a
point, every genuine equivariant homotopy invariant of Root(q) is that of
mu_{2l} (or of a point, after the free equivalence), independent of q and r.
The norm/invariant log is a non-homotopy-invariant function (it is a real
valued log, not a locally constant homotopy class; the valuation is locally
constant but its scale log p is external data). A homotopy theorist can see
the valuation as a map to Z, but not the log-volume number.

### 3.3 Verdict

REFUSE as the paper carrier or as the invariant log-volume. Equivariant
homotopy theory is a correct language for the mu_{2l}-ambiguity and for the
free-quotient structure, but it is strictly weaker than the actual root data.
It cannot supply q[2u].

## 4. Equivariant K-theory

### 4.1 Concrete objects and theorems

* For finite G, K_G(pt) = R(G), the representation ring; for G = mu_{2l},
  R(G) = Z[z]/(z^(2l) - 1). Atiyah-Segal, Equivariant K-theory and completion
  (1969); the completion theorem K_G^*(X)^wedge_I = K^*(X_{hG}).
* The root line with coordinate r is a G-equivariant line; its K-class is the
  character z (or z^{-1}); the label j gives the character z^(j^2). The
  augmentation R(G) -> Z sends every z^m to 1; the character at zeta sends
  z^m to zeta^m, a phase.
* K-theory is the group completion of the monoid of G-equivariant vector
  bundles; group completion discards the scale/norm of a trivialization.

### 4.2 What it preserves

The mu_{2l}-weights/characters and the Gauss phase structure: yes. The actual
root unit r and its norm/log: no. For any two roots r, r', the equivariant
line bundles are isomorphic as G-line bundles (both are the same character),
so their K-classes coincide; K-theory cannot distinguish r from r'. The first
Chern class of the root gerbe is zero because the root exists. The norm is a
metric/valuation, not a K-theory class; no regulator from K_1(K_v) to R gives
the p-adic log-volume of the paper.

### 4.3 Gauss obstruction

S689_GAUSS_ORBIT_MEMO.md computes the mu_{2l}-orbit average of the theta
value and finds zero for every nonzero label (2l does not divide j^2). In
K-theoretic language, the character decomposition does not produce a positive
log identity; the only nonvanishing invariant is the modulus. This is a
concrete negative result, not a matter of missing formalization.

### 4.4 Verdict

REFUSE for the carrier and for the log-volume. It is at most auxiliary
bookkeeping for the mu_{2l} weights.

## 5. Bredon cohomology

### 5.1 Concrete objects and theorems

* Bredon, Equivariant Cohomology Theories (LNM 34, 1967): for a finite group
  G and a coefficient system M : O_G^op -> Ab, the Bredon cohomology
  H_G^n(X; M) is the cohomology of Hom_{O_G}(C_*(X), M).
* For the free orbit G/e (one 0-cell of orbit type G/e, no higher cells), the
  Bredon cochain complex is concentrated in degree 0, with value M(G/e).
  Hence H_G^0(G/e; M) = M(G/e) and H_G^n(G/e; M) = 0 for n > 0.
* Kummer theory/Hilbert 90: for G acting trivially on K^*, the Kummer
  sequence 1 -> mu_n -> K^* -> K^{*n} -> 1 gives the connecting map
  K^*/(K^*)^n -> H^1(G; mu_n) = Hom(G, mu_n); the class of q is the
  obstruction to an n-th root. The root exists iff the Kummer class is zero.
  The repo has a cocycle/class-law layer in
  LeanFormal/IUT/IUTII/Kummer/KummerClass.lean; the full H^1 identification is
  explicitly a later obligation in that file, not an actual theorem.

### 5.2 What it preserves

The existence/obstruction and the torsor class: yes. The actual root: no. The
root is a 0-cochain/trivialization, not a cohomology class. The log is a
G-invariant map to R, i.e., a class in H_G^0(G/e; R) = R; it is just a real
number. There is no higher Bredon class carrying the norm or the log-volume.

### 5.3 Verdict

REFUSE as carrier or log-volume. ACCEPT as a consistency/obstruction language:
the paper's 2-torsion input must make the Kummer class of paper q_v vanish;
Bredon/group cohomology can state that, but it cannot supply the root.

## 6. Orbifold stacks and the stacky measure

### 6.1 Concrete objects

* The action groupoid Root(q) x mu_{2l} => Root(q) (S356): objects are actual
  roots, morphisms zeta : r -> zeta * r. This is the nondegenerate carrier
  that keeps the actual root; it is not the S355 quotient (which collapsed to
  a subsingleton). The groupoid is connected with trivial automorphism groups
  (a free transitive action), so it is equivalent to a point as a groupoid;
  its content is the actual root objects and the mu_{2l} morphisms, not a
  nontrivial inertia stack.
* The family version: O^tri_{K_v} (or the algebraic-closure root line) with
  the free mu_{2l}-action by multiplication; the quotient stack
  [O^tri / mu_{2l}] has coarse moduli the 2l-th power locus in the q-line
  (which contains q_v by the root assumption). On a fixed root torsor the
  action is free and transitive; the quotient is a point. The mu_{2l} here is
  the structure group of the torsor, not the automorphism group of a point:
  the quotient groupoid of a free transitive action on a fixed torsor is
  contractible, and the nontrivial stacky content is the family over the
  q-line together with its 1/(2l) measure normalization. (This is why orbifold K-theory/inertia, which needs
  nontrivial stabilizers, adds nothing here.)
* The paper's "Theta value determined up to mu_{2l}" is exactly a section of
  this torsor: a chosen root r is a trivialization; the log is the
  G-invariant function on the torsor.

### 6.2 The stacky measure theorem

Mathlib gives the exact finite-group statement:
  MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self
  [Fintype G] [MulAction G alpha] [SMulInvariantMeasure G alpha mu]
  (hs : IsFundamentalDomain G s mu) (t : Set alpha)
  (ht : forall g, g • t =ae[mu] t) :
    mu t = Nat.card G • mu (t inter s)
(verified by S735ProbeMathlibRootStackTools.lean; the probe also verifies
IsFundamentalDomain.covolume_eq_volume and quotientMeasure_eq, and the Torsor
API: Torsor, Equiv.smulConst, Equiv.constSDiv).
For the root line, take G = mu_{2l}, s = one fundamental domain (one branch),
t = the preimage of a base region in the q-line. Then
  mu t = (2l) * mu (t inter s),
so the stacky/quotient measure is mu t / (2l) = mu (t inter s). This is the
1/(2l) normalization, canonically and without choosing a root. In log
coordinates it is (1/(2l)) dlog|q|.

### 6.3 What it preserves

The actual roots (objects), the mu_{2l}-action (morphisms), the norm/log
(G-invariant), and the branch-independence of the log-volume: yes. This is
the precise sense in which the orbifold route is paper-faithful: the paper
only needs q[2u] up to mu_{2l}, and the log is invariant under the ambiguity.
It is strictly better than the equivariant homotopy/K-theory/Bredon routes,
which discard the actual root altogether.

### 6.4 What it does not supply

1. It does not construct paper q_v or its root. The actual root must exist in
   the paper carrier (O^tri_{K_v}) or in the extension L; the stack does not
   create it. The current repo root is in the algebraic closure (or L), not in
   the paper O^tri_{K_v}; PAPER_ROOT_CORRECTION says qVFamily is not paper q_v.
2. It does not supply the paper lambda-O/holomorphic hull. The paper hull is a
   specific intersection/closure of fractional-lattice regions in a tensor
   block; the stacky measure only normalizes the root direction.
3. It does not prove the paper hull equality. PaperRootHullSetGap (hull =
   fractional-lattice region) is an arithmetic/geometry input. The stacky
   measure can prove the log formula for a stacky hull, but identifying that
   hull with the paper hull is a new theorem.
4. It cannot fill PaperRootHullFormulaGap on the completion carrier as stated:
   the fractional scaling data at order/(2l) is equivalent to a completion
   2l-th root and is impossible (S342/S719). The stacky route can only replace
   the completion-valued scaling generator by the measure normalization; that
   is a different construction and needs its own paper identification.
5. The coefficient mismatch S736 (spectral c_norm vs paper order) is untouched.

### 6.5 Verdict

ACCEPT for the invariant log-volume normalization and for the branch
independence of the log; REFUSE as a construction of the paper carrier/hull or
as a proof of the paper formula. The orbifold route is the correct
normalization layer, not a closure of the exact gap.

## 7. Orbifold K-theory / inertia stack / Chen-Ruan

For a free action, the inertia stack of [X/G] is the quotient itself: the
stabilizers are trivial, so there are no twisted sectors; the Chen-Ruan
orbifold cohomology reduces to the ordinary cohomology of the quotient. The
age m/(2l) of zeta^m is defined, but it contributes no log-volume; the
fractional part of the paper exponent j^2/(2l) is age-like, while the integer
part comes from the valuation. This is an analogy, not a theorem, and it gives
no carrier or measure. REFUSE as a proof tool; at most a bookkeeping remark.

## 8. Verdict table

| Framework | Keeps actual root unit? | Keeps norm/log? | Invariant log-volume? | Fills paper hull gap? | Verdict |
|---|---|---|---|---|---|
| Equivariant homotopy theory | no (only the free orbit) | no (log not homotopy invariant) | no | no | refuse as carrier |
| Equivariant K-theory | no (character only) | no (group completion kills scale) | no | no | refuse; auxiliary weights |
| Bredon cohomology | no (root is a 0-cochain) | no (log is H^0 = R) | no | no | refuse; Kummer obstruction only |
| Orbifold stack / stacky measure | yes (objects are actual roots) | yes (G-invariant log) | yes: (1/(2l)) normalization | no (hull equality missing) | accept for normalization only |
| Orbifold K-theory / Chen-Ruan | no (free action, no twisted sectors) | no | no | no | refuse |

## 9. Lean-ready exact statements

### 9.1 Compiled kernel (EXIT=0)

File: tmp/sheaf/xif/paper/TaskFEquivariantOrbifoldKernel.lean

* log_eq_log_div_of_pow_eq:
  {q r : Real} (hq : 0 < q) (hr : 0 < r) {n : Nat} (hn : 0 < n)
  (h : r ^ n = q) : Real.log r = Real.log q / n.
* log_pow_eq_mul_log_div:
  same hypotheses, (j : Nat) :
  Real.log (r ^ (j ^ 2)) = ((j ^ 2 : Real) / n) * Real.log q.
* norm_eq_one_of_pow_eq_one:
  {K : Type} [NormedField K] {zeta : K} {n : Nat} (hn : 0 < n)
  (hzeta : zeta ^ n = 1) : ||zeta|| = 1.
* log_norm_mul_rootOfUnity_eq:
  ... (r : K) : Real.log ||zeta * r|| = Real.log ||r||.
* sum_left_invariant_eq_card_mul:
  {G : Type} [Group G] [Fintype G] (f : G -> Real)
  (hf : forall g h, f (g * h) = f h) :
  (sum g, f g) = (Fintype.card G : Real) * f 1.
* stacky_average_eq:
  (1 / (Fintype.card G : Real)) * (sum g, f g) = f 1.

These are the exact normalization facts. They do not assert the paper hull
formula.

### 9.2 Mathlib API verified by the S735 probe (compiled 2026-10-30)

* Torsor, Equiv.smulConst : P -> G ≃ P, Equiv.constSDiv : P -> P ≃ G.
* MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self :
  mu t = Nat.card G • mu (t inter s) for a G-invariant t and a fundamental
  domain s.
* MeasureTheory.IsFundamentalDomain.covolume_eq_volume.
* MeasureTheory.IsFundamentalDomain.quotientMeasure_eq.
* MeasureTheory.QuotientMeasureEqMeasurePreimage.
* groupCohomology, groupCohomology.H0Iso, and the finite-cyclic
  groupCohomologyIsoEven/Odd names in Rep.FiniteCyclicGroup (some #check names
  in the probe were stale; only the compiled names should be used).
* MeasureTheory.Measure.IsHaarMeasure, haarScalarFactor.
Note: the probe deliberately contained some stale #check names and reported
unknown-identifier errors for those; the names above are the ones that
elaborated.

### 9.3 Exact remaining gaps (not addressed by task F)

G1. Paper q_v and its root: identify the paper q_v and construct its 2l-th root
    in the paper carrier O^tri_{K_v} (or the extension L). qVFamily is not
    paper q_v (PAPER_ROOT_CORRECTION); the completion root is impossible for
    qVFamily (S342).
G2. Spectral c_norm = paper order (S736PaperOrderGap), needed to compare
    perBThetaHullLog with paperRootThetaHullLog.
G3. PaperRootHullSetGap: paperRootThetaHull equals the fractional-lattice
    region at paperRootCoefficient. This is the hull equality that the stacky
    measure does not prove. The scaling-data part (PaperRootHullScalingDataGap)
    is completion-impossible; do not chase it on the completion carrier.
G4. PaperSignedHull / paperLogVolume identification: paperRootThetaHullLog =
    paperRootThetaFormulaLog, and its comparison with the q-pilot log.

## 10. Recommendation

1. Do not replace the actual extension/field/root carrier by an equivariant
   homotopy, K-theory, or Bredon object. Those frameworks are refusals for
   the paper carrier; they can only state the mu_{2l}-ambiguity.
2. If the orbifold normalization is used, formalize it as a separate layer:
   the action groupoid on actual roots (S356) plus the stacky measure theorem
   above, proving the 1/(2l) log-volume normalization. This is a genuine,
   paper-faithful normalization result, not a surrogate for the missing hull.
3. Keep PaperRootHullFormulaGap as an impossibility on the completion carrier
   (S342/S719). The stacky route may replace the fractional scaling generator
   by the measure normalization, but then the paper identification becomes a
   new exact theorem: stacky hull log = paperRootThetaHullLog, plus the hull
   equality. State it explicitly; do not assume it.
4. The real remaining arithmetic work is G1-G4, especially the paper q_v/root
   construction and the hull equality. No equivariant or orbifold theorem in
   the literature supplies these for the paper's actual data.

No fake object, no surrogate target, no target change.