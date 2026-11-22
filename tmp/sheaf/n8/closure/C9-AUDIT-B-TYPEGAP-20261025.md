# C9 audit: B-branch files under the E16 type gap

Task: task-184 (C9-AUDIT-B-TYPEGAP-20261025). Owner: logdescent. Date: 2026-10-25. Read-only audit; no new attack; no Lean/Project/target/other-owner edits. Only this file written. P6 unproved; target_accepted=false.

Audited files and hashes:
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (E16): 7CC2DDD03CFEFA97E38049CA1CCB90016E944DECE0185F706E42F7F97CD61FD8
- C9-MODP-CERTIFICATE-20261025.md (task-155): E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95
- C9-MODP-BRANCH-PROOF-20261025.md (BRANCH): AF543BBBC50E8EC8CF9909CD5675D830018254760ABC66410C81501A7227EADE
- C9-MODP-GENERATOR-20261025.md (GEN): 8232226E983D95C4495864B7491A864750BF730B03611BC27FC5B5E25D39507C
- C9-AUDIT-BRANCH-20261025.md (AUDIT): C914E001B45EFE3755D09463DA4D85C78214B56975FAE7042E52BB8A5A56777D
- C9-GAMMA-COLUMN-ATTACK-20261025.md (GAMMA): 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C
- C9-TAME-LOG-DOMAIN-20261025.md (TAME): 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06

E16 type gap (the correction being applied): in the tame C9 type, y_i=F(x_i) is the p-adic log of a unit, hence y_i in m=J; under I/J=p^{-1}J/J the class of y_i is zero. The Kondo y-basis is a Q_p-basis of k_+=K, not an F_p-basis of I/J. Full Out(G_K) acts only Q_p-linearly through Phi; no cited theorem gives an integral action on O_K, J, I, or I/J. Therefore any B-branch statement that treats the y-basis as a trace-adapted basis of I/J, or the full actual Gamma as acting on I/J, has a type gap. It can survive only under an explicit integral-lift hypothesis H_A (for a subgroup) or H_A-full (for full Gamma).

## 0. Verdict

- The local trace/pi-power computation and the abstract linear-algebra dichotomy survive, because they live in I/J itself.
- Every statement that identifies the Kondo y-basis, y_1, or the 2025 trace line with a line/basis of I/J is invalid as written.
- The TAME section 6 statement for the full actual Gamma, and all B=O_K/B=I conclusions for full barGamma, are invalid as written; they become conditional theorems under H_A-full plus an explicit integral normalization/alignment.
- The task-155 headline B=O_K under the natural trace alignment is invalid as an actual source conclusion; its conditional core survives as abstract linear algebra plus an unproved alignment/action hypothesis.
- GEN's UNDETERMINED verdict survives and is strengthened; its proposed basis-alignment matrix in GL_e(Z_p) is not established.
- No B=O_K or B=I is actually proved for the source; no target/global use is valid.

## 1. What is actually proved and has no type gap

These statements are in, or directly about, I/J and the actual field/group data.

1. p=12301 is prime, p=1 mod 41, K=Q_p(pi), pi^41=p, e=41, K/Q_p tame totally ramified cyclic, p>e+1. Actual integer/local field data.
2. I/J = pi^{-40}O_K/pi O_K has F_p-basis e_0=1, e_{-40}=pi^{-40}, ..., e_{-1}=pi^{-1}; dim e=41. l=O_K/J=span(e_0). Actual.
3. Trace table: Tr(pi^a)=0 for 1<=a<=40; Tr(1)=41; Tr(pi^{-k})=u^{-1}p^{-1}Tr(pi^{41-k})=0 for 1<=k<=40. Hence tau(e_0)=41 != 0 and W0=ker(tau)=span(e_{-40},...,e_{-1}), dim 40. Actual (task-155 sections 1-2; BRANCH section 2).
4. y_i=F(x_i) in m=J for the tame type, hence [y_i]=0 in I/J. Actual consequence of log(O_K^x)=m (TAME section 1; EXT).
5. Mapping-class assignment for odd d: a_i -> x_{2i}, b_i -> x_{2i+1}, so the actual rho(Mod) generators fix x_0,x_1,sigma,tau and y_1 in k_+. Actual paper-level statement (Kondo 2025 Section 2 S2.Ex62; GAMMA section 3).
6. Phi: Out(G_K) -> GL_d(Q_p) is continuous closed; its codomain is Q_p-linear. Actual paper-level statement (Kondo 2026 Lemma 1.6).
7. Field automorphisms sigma in Aut(K) preserve O_K, J and fix l=O_K/J because sigma induces identity on the residue field. Actual field theory (GAMMA section 4; FULL-OUT section 4).
8. Kondo 2025 Theorem I: for finite Galois degree>1 with p odd, Out-conjugates of Aut(K) are infinite and Aut(K) is not normal. Actual paper-level statement; it does not give alpha(l) or integral matrices.
9. Abstract linear algebra: if one is given an F_p-linear action on I/J and a line U with I/J=U direct sum W, H acting trivially on U and irreducibly as Sp(W) on W, then B=O_K iff the orbit of l stays in U, and B=I iff some gamma moves l off U; the matrix criterion is m_{i1}=0 for all i>=2 versus some nonzero. Actual conditional algebra; no source action is supplied by this statement.
10. If H_A is explicitly assumed and H acts on I/J as diag(1,Sp_40), then H fixes l when U=l and the abstract criterion gives B_H=O_K. This is a conditional theorem, not an actual source result.

## 2. Survives only under an explicit integral-lift hypothesis

These statements are mathematically meaningful only after adding H_A (subgroup) or H_A-full (full Gamma):

(H_A) the chosen actual subgroup Gamma0 preserves O_K, J, I and induces an F_p-linear action on I/J, compatible with the log-shell/unit and normalized-volume interface.

(H_A-full) the same for the full actual finite image Gamma.

Under H_A/H_A-full:

1. TAME section 6 dichotomy: B/J is an F_p-subspace of I/J containing l; with H containing Sp(W), B=O_K or B=I. Valid conditional statement.
2. H (or a subgroup acting as diag(1,Sp)) fixes l if U=l; then B=O_K. Valid conditional.
3. If l has W-coordinate v != 0, then H's Sp orbit spans W and B=I. Valid conditional.
4. The finite matrix criterion in BRANCH/GAMMA (first column m_{i1}) is valid, but only for the explicitly given I/J action; the existence of that action is the hypothesis.
5. Task-155's conditional certificate: the trace table and the abstract statement "if U=trace line and H acts as diag(1,Sp_40), then B=O_K" survive under H_A plus the alignment hypothesis. They do not survive as actual source conclusions.
6. The local B=O_K/B=I volume values (b=3: -411/41 vs 9/41; b=273 etc.) survive only as conditional local arithmetic given a B branch; they require TC-A..TC-H + TC-S for any target/global use.
7. GEN's verdict UNDETERMINED for full barGamma survives (E16 strengthens it: not only unknown v/matrix, but the full action itself is unconstructed).

## 3. Invalid as written

These statements must be corrected in any reuse; the mathematical content is missing a construction or is type-inconsistent.

1. TAME section 6 headline: "For actual Gamma=Aut(G_K), B=span gamma(O_K) satisfies J subset B subset I and B=O_K or B=I." Invalid as written:
   - no proof that arbitrary gamma(O_K) lies in I;
   - full Gamma's action on O_K/J is not constructed;
   - the dichotomy's proof uses B/J subset I/J and gamma(l) in I/J, which are not available for full Gamma.
   Status: conditional theorem under H_A-full; not actual.

2. Any statement "the 2025 y-basis is a trace-adapted F_p-basis of I/J" or "T is in GL_e(Z_p) between y-basis and an I/J basis". Invalid as written: y_i in J maps to 0; a Q_p-basis of K is not an F_p-basis of I/J; an integral change matrix T requires an integral normalization/lattice comparison not supplied. Status: missing datum.

3. Any statement "U=<y_1> is the line l=O_K/J inside I/J", including the natural-alignment sentence in task-155 and the conditional D-fixes-l step in GAMMA. Invalid as written at the level of I/J: y_1 is zero mod J. It can only be a shorthand for an unconstructed integral normalization. Status: invalid-as-written; conditional only after H_A and an explicit normalization.

4. "H acts on I/J as diag(1,A), A in Sp_40" as an actual theorem. Invalid as actual: H is defined via Phi on k_+ (Q_p); its integral action is an inferred interface, not a Kondo theorem. Status: conditional under H_A plus AbsTopIII/IUT III naturality.

5. "D fixes l and B_D=O_K" because D fixes x_1/y_1. Invalid as written: D fixes y_1 in k_+, but y_1 is not a vector of I/J; D's action on I/J is unconstructed. Status: the k_+ statement survives; the I/J conclusion is conditional.

6. "Under the natural trace alignment, B=O_K and B=I does not occur" (task-155 section 5) as an actual source statement. Invalid as actual: the natural alignment is inferred, and the H action on I/J is not a paper theorem. Status: conditional; task-155 itself flags the alignment, but its headline wording overstates it.

7. "The full finite image barGamma contains an element with nonzero lower first-column m_{i1}, hence B=I", or the opposite "all elements have first column e_1, hence B=O_K", for full Out. Invalid as written: full Out's integral action on I/J is not constructed; non-normal conjugates preserve alpha(O_K), not O_K; no alpha(l) or matrix is computed. Status: not actual; Q1 is ill-posed without H_A-full (E16).

8. "Kondo Theorem I supplies a B=I generator." Invalid: Theorem I supplies non-normality/infinite conjugates, not any value alpha(l) or lattice preservation. Status: no.

9. Any downstream use of b=3/B=I "local closure" or b=3/B=O_K "local deficit" as an actual target input. Invalid as target: B branch is conditional and TC-A..TC-H + TC-S are missing; TAME section 5 (11)-(14) are not target proof. Status: conditional/withdrawn for target.

10. The task-153 finite model e=5,p=5 as evidence for actual e=41/p=12301. Invalid as actual: it is a finite representation model, not the C9 field; it only shows trace+Sp data do not determine l without the alignment. Status: model only.

## 4. Exact missing data

To make the B branch actual for a source subgroup or full Gamma, one needs at least:

1. Integral lift/naturality H_A or H_A-full: a proof (or explicit source axiom) that the actual Out action preserves O_K,J,I and induces an F_p-linear action on I/J, compatible with the log-shell/unit and normalized-volume interfaces. AbsTopIII/IUT III currently only provide an inferred interface (SYM/IND1 TC-S).
2. An integral normalization/alignment between the Kondo y-basis (Q_p-basis of K) and a Z_p-basis of O_K adapted to I/J, or a direct construction of the I/J basis. No T in GL_e(Z_p) is known.
3. The actual line vector v of l in the U/W decomposition of I/J, or the basis-alignment matrix.
4. The actual first-column matrices m_{i1} for the source generators (D, Aut(K), and any full-Out generators), or a proof all are zero/one is nonzero.
5. For full Out: generators beyond D and Aut(K), their lattice preservation, and their action on I/J; Kondo Theorem I does not supply these.
6. For any target/global use: TC-A..TC-H + TC-S.

## 5. Classification summary table

| Statement | Status |
|---|---|
| Local p,pi,I/J basis, trace table, W0=ker Tr, l=span(1) | PROVED ACTUAL |
| y_i in m=J, [y_i]=0 in I/J | PROVED ACTUAL |
| Mapping-class generators fix x_1,y_1 in k_+ | PROVED PAPER-LEVEL |
| Phi Q_p-linear; H closed preimage; Sp containment | PROVED PAPER-LEVEL |
| Field automorphisms fix l | PROVED ACTUAL FIELD THEORY |
| Abstract B=O_K/B=I dichotomy given H_A action | CONDITIONAL ALGEBRA |
| TAME section 6 B dichotomy for full Gamma | INVALID AS WRITTEN; conditional under H_A-full |
| y-basis/T as F_p basis of I/J / GL_e(Z_p) | INVALID AS WRITTEN; missing datum |
| U=<y_1>=l in I/J | INVALID AS WRITTEN; conditional on unconstructed normalization |
| H acts diag(1,Sp) on I/J | CONDITIONAL INFERRED INTERFACE |
| D fixes l / B_D=O_K | CONDITIONAL on H_A/alignment; k_+ statement only actual |
| task-155 conditional B=O_K under natural alignment | CONDITIONAL; not actual source theorem |
| full barGamma B=O_K or B=I | NOT PROVED; Q1 ill-posed without H_A-full |
| Kondo Theorem I gives B=I generator | INVALID |
| b=3/B=I local closure or B=O_K deficit as target | CONDITIONAL/WITHDRAWN for target |
| e=5,p=5 model as actual branch evidence | MODEL ONLY |

## 6. Consequences for the C9 route

- The earlier B branch files contain a valid local trace computation and a valid abstract finite criterion, but they do not prove an actual B=O_K or B=I for the source. The E16 correction applies to all "actual Gamma", "H fixes l", "D fixes l", "natural alignment", and "full barGamma" wording.
- Any future route must first supply H_A/H_A-full and the integral normalization; without them, no B branch can be fed into TAME section 5 formulas or C9 global assembly.
- Even with H_A, the branch is conditional on the actual v and matrices; no B=I is assumed. The task-155 b=3/B=I local surplus and b=3/B=O_K deficit are conditional values only, and TC-A..TC-H + TC-S are still required for target.
- No target F(Hull) subset H_C, no h_C>=Q_C, and no global counterexample is claimed.

## 7. Acceptance

Read-only audit; only C9-AUDIT-B-TYPEGAP-20261025.md written. No Lean/Project/target/other-owner edits. No new attack. Natural-language self-review done; Lean/Project/kernel/comparator/independent review not run; not applicable. target_accepted=false.
