# C9 audit: H_A-full integrality route (task-204)

Task: task-207. Date: 2026-10-25. Auditor: transport.
Stage: independent read-only audit. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Audited bytes and inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-HAFULL-INTEGRALITY-20261025.md (task-204 route) | 157 | 16523153A35BF386899AC2F36EB6DB53C777F7CA704034615646BD84DF002929 |
| C9-HAFULL-CONSTRUCT-20261025.md | 187 | C02D4A24CD201AD6F0FC2D5E308772F943AE29C911058F40ED19A2C8D7BA6878 |
| C9-AUDIT-HAFULL-LITE-20261025.md | 254 | 5FA594D485B2A9D1618F21AA22CAC9CE63746AE489F177E76F700745C8A10BAD |
| C9-HAFULL-CORRECTED-ATTACK-20261025.md | 271 | A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0 |

## 1. Verdict

HAFULL_INTEGRALITY_AUDIT = CONDITIONAL/OVERCLAIM: one decisive premise is
asserted but not proved; the algebra after it is valid.

The route's decisive step is

    alpha^times(U^n)=U^n for all n>=1 (in particular U^e=1+pO_K).   (P)

If (P) is granted for the actual full Out action, the rest of the attack is
correct:

    exp(p) in U^e,
    log(U^e) subset pO_K,
    alpha^times(exp p) in U^e,
    a(alpha)=p^{-1}log(alpha^times(exp p)) in O_K,
    a(alpha)=alpha_+(1),
    alpha_+(O_K) subset O_K,
    inverse gives equality,
    H_A-full and B=O_K follow,
    B=I is excluded under H_A-full.

But (P) is NOT standard local class field theory as asserted, and it is not
proved in the audited file. Local reciprocity gives the inertia/unit
identification and the reciprocity isomorphism; it does not by itself say that
an arbitrary automorphism of G_K preserves the principal-unit filtration U^n
or the exact subgroup U^e. The file calls this "standard local class field
theory" without a theorem/citation. That is the main missing source-level
condition.

Therefore:

- The route establishes a CONDITIONAL implication (P) => H_A-full/B=O_K.
- It does NOT establish H_A-full for actual full Out.
- The claims "a(alpha) lies in O_K for every full Out generator", "H_A-full
  holds", "B=O_K actual", and "B=I excluded actual" are OVERCLAIMS as stated.
- No W subset J abuse is used; that part is clean.

## 2. Step-by-step audit

### 2.1 U^e=1+pO_K

With pi^e=p u, u in Z_p^times, and U^n=1+pi^n O_K,

    U^e=1+pi^e O_K=1+p u O_K=1+pO_K.

This is exact. VALID.

### 2.2 exp(p) in U^e

For e=41<p-1=12300, exp converges on m (and on pO_K subset m). Since
p in pO_K, exp(p) is defined, and

    exp(p)=1+p+p^2/2!+... = 1+p(1+p/2+...) in 1+pO_K=U^e.

Also log(exp p)=p. VALID.

### 2.3 log(U^e) subset pO_K

For x in O_K,

    log(1+p x)=p x - p^2x^2/2 + p^3x^3/3 - ...

Every term p^n x^n/n has valuation at least 1 because p is odd and
v_p(p^n/n!)>=0. Hence log(1+p x) in pO_K. VALID.

This is the local integrality mechanism, independent of trace/W.

### 2.4 Upper ramification filtration characteristic under Out

The route asserts:

    for every alpha in Out(G_K), alpha^times(U^n)=U^n for all n>=1.   (P)

Justification given: local reciprocity identifies inertia with O_K^times, and
the higher ramification subgroups in upper numbering are group-theoretic.

Audit:

- Local reciprocity does give a canonical identification of the inertia
  subgroup with O_K^times, and Out acts on inertia.
- It does NOT directly imply that the standard principal-unit filtration
  U^n=1+pi^nO_K is preserved by an arbitrary automorphism of G_K. The upper
  numbering is defined via ramification groups of finite Galois extensions;
  its compatibility with the reciprocity filtration U^n requires a precise
  normalization/index shift and an invariance statement for the filtration
  under Aut(G_K), not merely the existence of the reciprocity isomorphism.
- No citation to AbsTopIII/Kondo or a theorem "upper ramification filtration is
  characteristic under Out(G_K)" is supplied. The statement is stronger than
  the inertia/unit identification used in H_A-lite.
- In particular, knowing alpha^times(O_K^times)=O_K^times does not determine
  whether alpha^times(U^e)=U^e. The file needs the latter exact preservation,
  not only inertia preservation.

Classification: (P) is UNPROVED/ASSERTED, not a valid standard-LCFT step as
written. It may be true under an anabelian reconstruction theorem, but that
theorem is missing from the proof.

### 2.5 alpha^times(exp p) in U^e

Follows from (P). Conditional on (P). Without (P), alpha^times(exp p) is only
a unit; its log need not lie in pO_K.

### 2.6 log(alpha^times(exp p)) in pO_K and a(alpha) in O_K

Follows from 2.5 and 2.3. Conditional on (P). Without (P), a(alpha) lies in
I=p^{-1}J but not necessarily in O_K.

### 2.7 a(alpha)=alpha_+(1)

Use Kondo log compatibility alpha_+ log = log alpha^times and
log(exp p)=p:

    log(alpha^times(exp p))=alpha_+(log(exp p))=alpha_+(p).

Since alpha_+ is Q_p-linear and p is the rational scalar,

    alpha_+(p)=p alpha_+(1),
    a(alpha)=p^{-1}alpha_+(p)=alpha_+(1).

This is valid conditional on the Kondo compatibility and the reconstruction
identification k_+(G_K)=K. VALID CONDITIONAL.

### 2.8 alpha_+(O_K) subset O_K

From a(alpha)=alpha_+(1) in O_K and alpha_+(J)=J:

    O_K=Z_p 1+J,
    alpha_+(O_K)=Z_p alpha_+(1)+J subset Z_p O_K+J=O_K.

This step is valid conditional on a(alpha) in O_K and J preservation. It does
not need W subset J. VALID CONDITIONAL.

### 2.9 Inverse equality

Apply the same argument to alpha^{-1}: alpha^{-1}_+(1) in O_K (conditional on
(P) for alpha^{-1}) and alpha^{-1}_+(J)=J. Then alpha^{-1}_+(O_K) subset O_K.
Apply alpha_+: O_K subset alpha_+(O_K). Hence equality alpha_+(O_K)=O_K.

This is valid conditional on (P) for all alpha. Without (P) for the inverse, it
does not follow.

### 2.10 H_A-full, B=O_K, B=I excluded

If (P) holds for every alpha in full Out, then every alpha preserves O_K,J,I;
H_A-full follows and B=O_K. Also alpha_+(1) mod J is nonzero because the
induced map on O_K/J is surjective; hence l is fixed and B=I is excluded.

These conclusions are CONDITIONAL on (P) and on the Kondo/reconstruction
interface. They are not actual full-Out theorems from the cited frozen sources.

## 3. Abuse / missing-condition list

1. MAIN ABUSE: (P) is called standard local class field theory, but only
   inertia/reciprocity identification is standard. Preservation of the full
   principal-unit filtration U^n (or even U^e) by arbitrary Out elements is an
   additional anabelian/group-theoretic input not proved or cited.

2. INDEXING: the route does not verify that the reciprocity image of U^n is
   exactly the upper ramification subgroup used, including the upper-numbering
   shift. Even if an upper filtration is characteristic, the exact U^n
   correspondence needs proof.

3. OVERCLAIM: "a(alpha) lies in O_K for every full Out generator" is
   conditional on (P), not established.

4. OVERCLAIM: "H_A-full holds for full Out" and "B=O_K actual; B=I excluded"
   are conditional on (P). Without it they are not proved.

5. The route correctly does not use W subset J, and E24's W subset J error is
   absent. This part is clean.

6. The reconstruction identification k_+(G_K)=K, O^times(G_K)=O_K^times, and
   alpha^times/alpha_+ compatibility are paper-level conditional inputs, as
   the file admits. They are not Lean/kernel verified.

## 4. Corrected conditional theorem

Let (P) be:

    for every alpha in the actual full finite image/full Out under
    consideration, alpha^times(U^e)=U^e.

Assume additionally:

- Kondo log compatibility alpha_+ log=log alpha^times;
- reconstruction k_+(G_K)=K and O^times(G_K)=O_K^times;
- J=log(O_K^times)=m and I=p^{-1}J.

Then:

    a(alpha)=p^{-1}log(alpha^times(exp p))=alpha_+(1) in O_K,
    alpha_+(O_K)=O_K,
    H_A-full holds,
    B=O_K,
    B=I is excluded.

Without (P), the route only gives a(alpha) in I=p^{-1}J; the integrality
a(alpha) in O_K, hence H_A-full and B=O_K, remain OPEN.

The exact missing source input is a theorem (or computation) that the actual
Out action preserves U^e=1+pO_K, equivalently preserves the relevant
principal-unit filtration. A proof that the upper ramification filtration is
stable under Out(G_K) would suffice, but is not supplied.

## 5. Relation to the corrected attack

C9-HAFULL-CORRECTED-ATTACK shows:

- alpha_+(1)=p^{-1}log(alpha^times(exp p)) is canonical in I;
- H_A-full iff a(alpha) in O_K minus J;
- H_A-full => l fixed => B=O_K;
- abstract H_A-lite can fail integrality.

The task-204 route tries to prove the integrality by preserving U^e. The audit
confirms the algebra of that attempt but flags the unproved filtration
preservation. Together, the two files give:

    H_A-lite + explicit (P)  =>  H_A-full => B=O_K,
    H_A-lite alone           =>  a(alpha) in I, integrality open.

## 6. Status classification

| item | classification |
|---|---|
| U^e=1+pO_K | VALID |
| exp(p) in U^e | VALID |
| log(U^e) subset pO_K | VALID |
| a(alpha) in I | VALID conditional on Kondo compatibility |
| a(alpha)=alpha_+(1) | VALID conditional |
| alpha^times(U^n)=U^n for all n | NOT PROVED/ASSERTED |
| alpha^times(U^e)=U^e | NOT PROVED (key missing premise) |
| alpha^times(exp p) in U^e | CONDITIONAL on (P) |
| a(alpha) in O_K | CONDITIONAL on (P) |
| alpha_+(O_K) subset O_K | CONDITIONAL on (P) |
| H_A-full for full Out | CONDITIONAL/OVERCLAIM |
| B=O_K actual | CONDITIONAL |
| B=I excluded actual | CONDITIONAL on H_A-full |
| W subset J abuse | ABSENT; E24 not repeated |
| complete C/target | MISSING |

## 7. Verdict summary

The route is a valid conditional proof of H_A-full/B=O_K from the preservation
of U^e by Out, plus the Kondo/reconstruction interface. The preservation of
U^e (or the upper ramification filtration) is the decisive missing premise and
is overclaimed as standard local class field theory. The algebra is otherwise
correct: U^e=1+pO_K, exp(p) in U^e, log(U^e) subset pO_K, a(alpha) in O_K,
a(alpha)=alpha_+(1), alpha_+(O_K)=O_K, and B=O_K follow under (P).

Without (P), a(alpha) is only in I; H_A-full and B=O_K remain open, and B=I
is not excluded. The route does not use W subset J, so it avoids E24's
specific error, but it does not close H_A-full.

target_accepted=false.
