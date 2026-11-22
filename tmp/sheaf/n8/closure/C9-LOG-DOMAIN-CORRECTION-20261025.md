# C9 log-domain correction (task-170)

Task: task-170. Date: 2026-10-25. Owner/executor: transport.
Stage: stage1 natural-language correction only. No Lean/Project/target edits.
Only this file written.

Inputs:

| file | lines | SHA256 |
|---|---:|---|
| C9-LOG-DOMAIN-EXTEND-20261025.md (task-146) | 199 | CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA |
| C9-AUDIT-LOG-ARCH-20261025.md (task-161) | 298 | F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC |
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-ERRATA-SYMPLECTIC-20261025.md | 13 | A189FC87D9F633916A097C2B8D9C5BDA7407825920765C1CECA36335BE5024C7 |
| C9-ERRATA-IND1-20261025.md | 13 | EF63F916B4312A3E8562D16C2C122770BF7F188B75760989F958FDA2F6A0F8C2 |

## 0. Purpose and scope

This file corrects the log-domain errors confirmed by task-161 and records
which parts of task-146 survive. No new C9 attack, no finite/archimedean
compensation claim, no target containment, no Lean.

Notation: p odd, K/Q_p finite, absolute ramification e, residue degree f,
residue field cardinality q_res=p^f, uniformizer pi, m=pi O_K, v_p(pi)=1/e,
O_K integer ring, U^1=1+m.

## 1. Corrected log/exp theorem

### 1.1 p-adic log converges on all of U^1

For x in m,

    log(1+x) = sum_{k>=1} (-1)^{k+1} x^k/k.

If x in m^n, v_p(x)>=n/e, hence

    v_p(x^k/k) >= k n/e - v_p(k).

For k=p^t, v_p(k)=t and the lower bound is

    p^t n/e - t -> +infinity.

Therefore the log series converges on every m^n, n>=1, and hence on
U^1=1+m. There is no log convergence threshold n0. In particular, the
task-146 statement that for n<e/(p-1) the log term valuation goes to
-infinity is wrong by sign: it goes to +infinity.

The correct statement is:

    log: U^1 -> m,   log(1+x)=sum (-1)^{k+1}x^k/k,

is defined by the convergent power series on all of U^1. The Teichmuller
convention log(zeta)=0 for zeta in mu_{q_res-1}(K) is an additional source
convention, not a consequence of the power series at zeta (see 2.2).

### 1.2 p-adic exp threshold: strict inequality

For x in m^n,

    v_p(x^k/k!) >= k n/e - (k-1)/(p-1)
                  = n/e + (k-1)(n/e - 1/(p-1)).

The right side tends to +infinity for all k exactly when

    n/e > 1/(p-1).

Thus the minimal exp domain exponent is

    n_exp := floor(e/(p-1)) + 1,

equivalently the least integer n with n/e > 1/(p-1).

On m^{n_exp}, exp converges uniformly and

    exp: m^{n_exp} -> U^1,   log(exp x)=x,
    exp(log(1+x))=1+x for x in m^{n_exp}.

The log series is defined on all U^1, but exp is inverse to it only on the
smaller m^{n_exp}; the restricted inverse statement is what is used below.

Boundary correction. When e/(p-1) is an integer, including e=p-1, the
threshold is one higher than ceil(e/(p-1)):

    e=p-1:  e/(p-1)=1, n_exp=2, not 1.

At e=p-1 (for example p=3, e=2), the term x^k/k! for x=pi and k=p^t has
valuation

    k/(p-1) - (k-1)/(p-1) = 1/(p-1),

which does not tend to zero; exp does not converge on m. Hence the task-146
extension "e<=p-1, n0=1, exp converges on m" is wrong at the boundary
e=p-1. The audit task-161 repeats this boundary error. The correct statement
is:

    exp converges on m^n for n > e/(p-1), i.e. n >= n_exp;
    for n < n_exp (including equality when e/(p-1) is an integer) the
    uniform valuation bound does not force convergence, and at e=p-1 the
    explicit term above shows divergence on m.

If one only needs a sufficient threshold, n_exp is exact for uniform
convergence on m^n. No log threshold is involved.

### 1.3 d=ef and e=1 sanity checks

- e=1 (unramified): e/(p-1)=1/(p-1)<1 for p>2, n_exp=1, exp converges on m;
  log converges on U^1. This recovers the usual Q_p picture.
- e=p-1: n_exp=2 as above.
- e<p-1: n_exp=1; exp converges on m.
- e>p-1: n_exp>=2.

## 2. Restricted log image versus full log image

### 2.1 The full log is not confined to m^{n_exp}

The full log on U^1 converges and its linear term is x. Its image
log(U^1) is an additive subgroup of m containing the linear image of U^1;
in particular it is not the lattice m^{n_exp} whenever n_exp>1. A precise
description of log(U^1) as a Z_p-lattice is not needed here; the correction
is only that

    log(U^1) != m^{n_exp} in general,
    log(U^1) is not confined to the higher lattice m^{n_exp}.

Task-146's identity J_K=log(O_K^times)=m^{n0} is therefore only a statement
about the restricted domain D_K below, not about the full log image.

### 2.2 Two source conventions

(a) Pure analytic domain. Only points where the power series converges:
D_an=U^1 (all of it for log). Teichmuller roots are not automatically in
D_an; for e>p-1 they are generally outside the exp domain, though log on them
is still defined by the convergent log series only if they lie in U^1 (the
nontrivial roots do not, so this convention simply does not assign log 0 to
nontrivial roots).

(b) Source Teichmuller convention. Define log(zeta)=0 for
zeta in mu_{q_res-1}(K), and restrict the analytic log to the smaller domain
U^{n_exp}; combine:

    D_K = mu_{q_res-1}(K) * U^{n_exp} = mu * (1+m^{n_exp}),
    log: D_K -> m^{n_exp},
    ker(log|D_K)=mu_{q_res-1}(K).

This is the convention that matches IUT III Rmk1.1.1/Rmk1.2.2 and
AbsTopIII Def5.4(iii)/Prop5.8 (root-unit log zero), but it is a source
convention, not a consequence of the same power series at zeta.

Under (b), and only under (b):

    J_K := log(D_K) = m^{n_exp},                          (2.1)
    I_K := p^{-1} J_K = m^{n_exp-e} = pi^{n_exp-e} O_K.   (2.2)

Under (a), J_K remains the full log(U^1), which is larger than m^{n_exp};
the restricted identity (2.1) does not apply. Do not write
"J_K=log(O_K^times)=m^{n_exp}" without naming convention (b).

For e<p-1, n_exp=1 and (2.1)/(2.2) recover J_K=m and I_K=p^{-1}m. For
e>=p-1 they do not give the full log image.

## 3. Volume formula with residue degree f

The task-146 formula omitted f. Correctly:

    [O_K : m^n] = q_res^n = p^{f n},
    logvol_O(m^n) = (n f/e) log p.                         (3.1)

The factor 1/e is the normalization by the ramification degree, and f is the
residue degree; both are necessary. For the restricted shell I_K=m^{n_exp-e},

    logvol_O(I_K) = ((n_exp-e) f/e) log p.                 (3.2)

Compared with the tame value n_exp=1, the restricted shell volume increases by

    ((n_exp-1) f/e) log p.                                 (3.3)

For f=1 this reduces to the task-146 expression; for f>1 the omission of f
is a genuine error.

## 4. What survives from task-146

Survivors, valid independently of the symplectic donor:

1. p-adic log converges on all U^1=1+m (corrected sign and no threshold).
2. The exp convergence threshold is n_exp=floor(e/(p-1))+1, not a log
   threshold and not ceil at integer boundary; exp/log inverse on m^{n_exp}.
3. The Teichmuller decomposition O_K^times=mu x U^1 and the convention
   log(mu)=0, when adopted, are standard; the distinction (a)/(b) is valid.
4. Under restricted convention (b), J_K=m^{n_exp}, I_K=m^{n_exp-e}; under
   (a) this is not the full log image.
5. The integer lattice: log(U^1) subset m, so
   O_K + log(U^1) = O_K; under (b), O_K+m^{n_exp}=O_K. The Kummer zero path
   therefore still generates O_K, not a larger lattice.
6. exp(pz) for z in O_K is safe for every e: n_exp<=e, so
   v_p(pz)>=1>=n_exp/e, and log(exp(pz))=pz.
7. q (the BPS/pilot nonunit) does not enter p-adic log; Gaussian exponents and
   tensor integrality are not determined by the log domain.
8. The same-path second log-link remains empty: the log image (full or
   restricted) lies in m, hence is nonunit, while the next log-link input must
   be a unit (IUT III Rmk1.1.1(i)). This does not require n0.

Corrected but surviving in a weaker form:

9. e=p-1 is not "U^1 full exp"; only log is defined on all U^1, exp inverse
   holds on m^2. The statement e<=p-1 for the full inverse is withdrawn.
10. "J_K=m^{n0}" survives only as the restricted D_K identity, not as full
    log image.
11. The volume scaling survives with f: (n f/e) log p, not (n/e) log p.

## 5. Donor-dependent / conditional parts (not corrected as theorems)

The following are not log-domain theorems and remain conditional:

- The use of Kondo's 2025 trace/2026 symplectic image and the corrected donor
  H=Phi^{-1}(Sp) (task-147 errata) for lattice/orbit generation.
- The identification of the 2025 trace basis with the 2026 symplectic basis.
- The wild-ramification adaptation of trace/W=kerTr/pi-power formulas; task-146
  rightly says these cannot be copied from tame, but their actual replacement
  is not proved.
- The statement that Aut(G_K) additive image preserves m^{n_exp} and the
  normalized shell; plausible from linear isometry but not established here.
- The archimedean normalization and global weights (task-150/156/162
  corrections).
- Any downstream target containment TC-A..TC-H plus TC-S; task-149 and
  task-161 remain binding.

## 6. Exact corrected theorem (log domain)

Let K/Q_p be finite with ramification e, residue degree f, uniformizer pi,
m=pi O_K, p odd.

(i) log(1+x)=sum_{k>=1}(-1)^{k+1}x^k/k converges for every x in m; it defines
    log: U^1=1+m -> m.

(ii) exp(x)=sum x^k/k! converges on m^n iff n>e/(p-1), uniformly; the minimal
     exponent is n_exp=floor(e/(p-1))+1. On m^{n_exp}, exp and log are inverse
     maps between m^{n_exp} and exp(m^{n_exp}) subset U^1.

(iii) At e=p-1, n_exp=2; exp does not converge on m (term x^{p^t}/p^t! has
      constant valuation 1/(p-1)). The task-146 claim n0=1 at e=p-1 is
      corrected to n_exp=2.

(iv) Under the source Teichmuller convention (b),
     D_K=mu_{q_res-1}(K)*U^{n_exp}, log(D_K)=m^{n_exp},
     ker log=mu_{q_res-1}(K).
     Under the pure analytic convention (a), this is not the full log image:
     log(U^1) is larger than m^{n_exp}.

(v) Restricted shell:
     J_K^{res}=m^{n_exp}, I_K^{res}=p^{-1}J_K^{res}=m^{n_exp-e}.
     Full log shell is not identified with this unless (b) is the source
     convention.

(vi) Volume:
     logvol_O(m^n)=(n f/e) log p,
     logvol_O(I_K^{res})=((n_exp-e) f/e) log p.

(vii) Integer lattice:
      O_K + log(U^1)=O_K; under (b), O_K+m^{n_exp}=O_K.
      No larger source-generated integer lattice comes from the log domain.

(viii) Same-path h>=2 log-link is empty; independent unit paths are new first
       log-links, not iterations.

## 7. Error classification table

| item | task-146 status | correction |
|---|---|---|
| log converges only above n0 | ERROR | log converges on all U^1; no log threshold |
| divergence for n<e/(p-1), log term -> -inf | ERROR (sign) | log term -> +inf; exp bound is the strict one |
| n0=ceil(e/(p-1)) exact exp threshold | CONDITIONAL/ERROR at boundary | n_exp=floor(e/(p-1))+1; e=p-1 gives 2 |
| e=p-1, n0=1, exp on m | ERROR | exp on m^2; log still on U^1 |
| J_K=log(O_K^times)=m^{n0} | ERROR as full image | only restricted D_K convention (b) |
| I_K=m^{n0-e} full shell | CONDITIONAL | restricted shell; full log shell larger |
| logvol_O(m^n)=(n/e)logp | ERROR for f>1 | (n f/e)logp |
| volume loss (n0-1)/e logp | ERROR for f>1 | ((n_exp-1)f/e)logp |
| integer lattice O_K | VALID | survives with full/restricted image |
| exp(pz) safe | VALID | n_exp<=e |
| h>=2 empty same path | VALID | image in m, nonunit |
| Teichmuller log=0 | VALID as source convention | not analytic at zeta |
| wild trace/symplectic formulas | CONDITIONAL donor-dependent | not copied from tame |
| target containment | NOT CLAIMED | task-149 TC conditions |

## 8. Exact remaining gaps

1. Source-level decision whether the actual C uses convention (a) or (b) for
   the log domain at Teichmuller units and at U^1; this determines whether
   J_K is m^{n_exp} or the full log(U^1).
2. Exact lattice description of full log(U^1) for e>p-1, if convention (a)
   is used. The correction only proves it is larger than m^{n_exp}, not its
   precise index.
3. Wild-ramification replacement for the tame trace/symplectic formulas;
   donor-dependent, not a log-domain issue.
4. Archimedean normalization and global weights; separate task-150/156/162
   corrections.
5. Downstream TC-A..TC-H plus TC-S; no target containment follows from this
   correction.

## 9. Status

This file corrects the confirmed log-domain errors of task-146 and the
boundary error repeated in task-161. It does not prove any C9/P6 global
inequality, does not use the original symplectic section 2 construction, and
does not remove the donor-dependent and target-container conditions.

target_accepted=false.
