# C9 audit: archimedean global readout (task-156)

Task: task-163. Date: 2026-10-25. Auditor: transport.
Stage: read-only natural-language audit. No Lean/Project edits.
Only this file written.

## Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-ARCH-GLOBAL-20261025.md (task-156) | 197 | 524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489 |
| C9-ARCHIMEDEAN-20261025.md (task-150 prior arch audit) | 250 | F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957 |
| C9-AUDIT-TARGET-CONTAINER-20261025.md | 580 | B6F748C63EE441509440704CEEF69764C542355A3AF5FE18ABD39159E44F3F47 |
| C9-ERRATA-IND1-20261025.md | 13 | EF63F916B4312A3E8562D16C2C122770BF7F188B75760989F958FDA2F6A0F8C2 |
| C9-ERRATA-SYMPLECTIC-20261025.md | 13 | A189FC87D9F633916A097C2B8D9C5BDA7407825920765C1CECA36335BE5024C7 |

## Verdict

arch_global_audit = CONDITIONAL WITH A NORMALIZATION INCONSISTENCY;
not valid as a literal paper-level formula.

- alpha_v weights: VALID as standard degree weights (with a warning about
  double-counting against the local d_v factor).
- h_inf formula (A2)/(A3): INCONSISTENT/ERROR as written. (A2) has
  d_v log(r/pi) but (A3) drops the d_v factor; and the reference radius
  pi conflicts with the audited IUT IV normalization log-volume(B_I)=0.
- shell containment h_inf <= 0: CONDITIONAL, not valid under the
  B_I-normalization. It is valid only under a shell-pi normalization, which
  must be stated and reconciled with IV Thm1.10(vii).
- product formula (A10): VALID; the derived bound (A11) and the sign
  conclusion are conditional on the h_inf normalization in (A3).
- necessary radius r_inf >= pi exp(D): CONDITIONAL on the same normalization;
  under B_I-normalization the pi factor disappears.
- b=3 D=408/41: valid conditional arithmetic for the B=O_K branch value
  h=-411/41; not an actual finite deficit.
- b=273 D=38883/41: ambiguous/wrong for the B=O_K branch; the B=O_K/B=h_B
  value is 38463/41. The 38883/41 number belongs to the h_A branch.
- downstream target use: correctly marked conditional by task-156, but the
  file still uses TAME section 5 local values; those remain withdrawn/
  conditional per task-149.

## 1. Alpha weights

(A4): alpha_v = d_v/[F:Q], with d_v=[F_v:R] and one place per conjugacy class
of embeddings, satisfies sum_v alpha_v=1. This is the standard degree weight
and is compatible with the product formula (A10).

(A8): alpha_p=[(F_mod)_p:Q_p]/[F_mod:Q] and sum_{p|p0} alpha_p=1 is correct
for the finite places over a fixed rational prime p0.

Classification: VALID, assuming the standard convention one complex place
(with d_v=2), not one per embedding. No error found in the weight definition
itself.

Warning: (A4) alpha_v already contains d_v/[F:Q]. If (A2) also multiplies the
local radial log-volume by d_v, the global contribution is
d_v^2/[F:Q]*log(r/pi), not d_v/[F:Q]*log(r/pi). This is a degree double-count
risk; see Section 2.

## 2. h_inf formula and normalization

(A2): h_v^rad(B_v(r)) = d_v log(r/pi).
(A3): h_inf(C) = sum_v alpha_v log(r_v/pi).

These are not the same formula: (A3) omits the d_v factor present in (A2).
Either:

- the local radial log-volume has no d_v and (A2) is wrong, or
- the global sum must be sum_v alpha_v d_v log(r_v/pi) and (A3) is wrong.

More importantly, the reference is normalization-dependent.

The audited prior arch file C9-ARCHIMEDEAN-20261025.md records the IUT IV
normalization:

    IV Thm1.10(vii): log-volume(B_I)=0,
    log-volume(pi^{j+1} B_I)=(j+1) log pi.

Under this normalization, a radial hull of radius r has log-volume log r
(up to the local dimension convention fixed by B_I), not log(r/pi); the shell
radius pi is a container boundary, not the zero reference.

If instead one normalizes the shell I_v={|a|<=pi} to zero, then (A2)'s
log(r/pi) is natural. But then this is not the IV B_I normalization quoted in
the same task, and one must state which normalization enters the global h_C.
The task cannot mix the two.

Consequences:

- (A5) F=Q h_inf=log(r_inf/pi) is conditional on shell-pi normalization.
  Under B_I normalization it should be log(r_inf), possibly with a local
  dimension factor fixed by the tensor packet convention.
- (A9) r_v<=pi implies h_inf<=0 only in shell-pi normalization. Under B_I
  normalization, r_v<=pi gives h_inf<=log pi, which is positive; the
  non-compensation conclusion does not follow.
- (A17) r_inf>=pi exp(D_C) is shell-pi normalization only if D_C is the full
  natural-log quantity. If D_C=d_p log p, this is r_inf>=pi*p^{d_p}, not
  pi*exp(d_p). Under B_I normalization it is r_inf>=p^{d_p} (no pi factor).

The exact source reconciliation needed is a single normalization statement
linking IUT IV Thm1.10(vii)'s B_I=0 to the global h_C in III Rmk3.1.1.
C9-ARCH-GLOBAL does not supply it; it quotes both but uses only the shell
reference.

Classification: h_inf formula = ERROR/conditionally inconsistent; the missing
normalization is not a minor unit conversion because it shifts the sign of
(A9) and the pi factor in (A17).

## 3. Shell containment h_inf<=0

The implication is elementary once (A3) with shell-pi normalization is
accepted:

    r_v<=pi all v => log(r_v/pi)<=0 => h_inf<=0.

But its premises are two:

1. H_C,inf subset I_v for all v (source shell containment); task-156 correctly
   says this is not proved.
2. h_inf is measured relative to I_v (shell-pi normalization); this is not
   established and conflicts with the IV B_I normalization cited.

Thus h_inf<=0 is CONDITIONAL, not a valid paper-level consequence. It is not
enough to say "if containment holds"; the normalization must also hold.

Under B_I normalization, shell containment gives h_inf<=log pi>0; it does not
exclude compensation and does not yield a negative bound.

## 4. Product formula

(A10):

    sum_{v|infty} alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0

is the standard product formula with degree weights. VALID.

(A11) derivation:

    h_inf >= - sum_p alpha_p v_p(x) log p - log pi

uses (A3) without d_v and the shell-pi reference. It is valid under that
normalization. Under a corrected B_I normalization the -log pi term is absent
and the sign of the "integral element" bound can change (it becomes a
nonnegative lower bound in the simplest radial case), so the qualitative
statement "product formula only gives a nonpositive lower bound" is
normalization-dependent.

What survives independently: product formula alone does not produce a
positive lower bound of the form D_C^Sp for arbitrary x; it only constrains
point norms. The exact inequality (A11) should not be quoted without the
normalization.

Classification: (A10) VALID; (A11)/(A12) CONDITIONAL; the sign conclusion is
not valid as a paper-level statement until normalization is fixed.

## 5. Finite deficit and necessary radius

(A14)-(A15): D_p^Sp formula is explicitly conditional in task-156 on the
corrected donor (task-147) and target container (task-149). This is correct.
It is not an actual finite deficit.

(A16)-(A17): conditional equivalence. If finite donor and target container
conditions hold and if the chosen h_inf normalization is the shell-pi one,
then h_C>=Q_C iff h_inf>=D_C^Sp. But D_C^Sp in (A14) is
"sum alpha_p D_p^Sp log p", i.e. a natural-log quantity containing log p.

- If D_p^Sp/log p is written d_p (dimensionless), then
      D_C^Sp = d_p log p,
  and F=Q shell-pi normalization gives
      r >= pi * exp(D_C^Sp) = pi * p^{d_p}.
  This is the correct base-p radius; it is NOT pi * exp(d_p).
- Under B_I normalization the same correction gives r >= p^{d_p} (no pi).

Task-156's (A17) writes r>=pi exp(D_C^Sp), which is formally correct only if
D_C^Sp is the full natural-log quantity. Its numerical substitution then uses
d_p=408/41 directly in exp, which is the error: it drops the log p factor and
uses base e instead of base p=12301.

Correct numerics for F=Q:

- b=3: h_A=-411/41, Q_p=-3/41, d_p=408/41, D_C^Sp=(408/41)log p.
      r >= pi * p^(408/41) = 1.574145...e41 (log10 r ~ 41.1970).
      The file's 65903.669 = pi*exp(408/41) is far too small.
      It would be correct only if p were replaced by e, which is not the local
      prime.
- b=273 branch h_A: d_p=38883/41, D_C=(38883/41)log p,
      r >= pi*p^(38883/41). The exponent log10 is
      (38883/41)*log10(p) = 3878.7598...; adding log10(pi) gives
      log10 r ~ 3879.2570.
      Branch h_B/B=O_K value 38463/41 gives
      (38463/41)*log10(p)=3836.8629..., log10 r~3837.3600.
      Task-156's 38883/41 is the h_A branch; it is not the B=O_K h_B branch.

Classification: A14/A15 conditional; A16/A17 conditional; A18 is an
arithmetic/unit error (base e substituted for base p), and A19 is
branch-ambiguous plus the same base error. The correct necessary radius is
pi*p^{d_p}, not pi*exp(d_p).

## 6. Global decomposition and good/bad weights

(A6)-(A8): h_C = sum finite alpha_p h_p + h_inf, Q_C=sum bad alpha_p Q_p.
These are assembly templates, not actual values; no complete C is constructed.
They are conditional. The statement "good finite profile relative reference 0"
is also conditional on the source normalization; task-156 does not prove it
from a complete C.

(A13) nonradial angular term: correct in shape but actual angular volume is
not constructed; the whole nonradial branch is conditional.

## 7. Errors / overclaims to classify

1. (A2)/(A3) mismatch: d_v appears in the local formula but not in the global
   sum. This is a genuine inconsistency, not just notation. Classification:
   ERROR in the written formulas; fix to either
   h_v=d_v log(r/pi), h_inf=sum alpha_v d_v log(r/pi), or
   h_v=log(r/pi), h_inf=sum alpha_v log(r/pi).

2. Reference normalization: (A2)/(A3)/(A9)/(A11)/(A17) all use the shell pi
   as zero; the audited IV formula uses B_I=0 and gives (j+1)log pi for
   pi^{j+1}B_I. Classification: CONDITIONAL/ERROR as a paper-level claim;
   needs a source normalization reconciliation. Under B_I normalization the
   pi factor in (A17) and the sign in (A9) are wrong.

3. Shell containment h_inf<=0: not valid under B_I normalization; only
   conditional under shell-pi normalization plus unproved H_C containment.
   Classification: CONDITIONAL, overclaimed if stated as paper-level.

4. Product formula: formula valid; derived sign bound conditional. The
   qualitative "product formula cannot prove positive compensation" remains
   true in the weaker sense that it is only a point constraint, but the exact
   (A11) sign statement is not normalization-independent.

5. b=273 D=38883/41: branch ambiguity (h_A vs h_B/B=O_K); possibly the wrong
   number for the B=O_K branch. Classification: CONDITIONAL/ERROR as quoted.

6. Base error in A18/A19: task-156 substitutes d_p=408/41 (or 38883/41)
   directly into pi*exp(d_p), which uses base e. Since D_C=d_p log p, the
   correct radius is pi*p^{d_p}. For b=3 this gives ~1.574e41, not
   6.59e4. Classification: ERROR in the numerical radius; formula with D_C
   natural is correct, numerical substitution is not.

7. Finite donor and target container: task-156 correctly flags both; no
   overclaim there. But any downstream use of D_C^Sp and (A16) remains
   conditional on task-147/task-149 and cannot be registered as actual.

## 8. Exact corrected conditional statements

Let norm be the chosen global archimedean normalization. Write
H_inf = sum_v alpha_v h_v^rad(r_v), with h_v^rad the radial log-volume of the
actual hull in that normalization.

If norm is shell-pi:
    h_v^rad=d_v log(r_v/pi) [or log if the d_v convention is global weight],
    H_inf=sum alpha_v h_v^rad,
    H_inf<=0 if r_v<=pi,
    F=Q: H_inf=log(r/pi), necessary r>=pi*p^{d_p}, where D_C=d_p log p.
    (If D_C is already natural log, r>=pi*exp(D_C); do not substitute d_p.)

If norm is IV B_I=0:
    h_v^rad=log r_v (local dimension convention fixed by the tensor packet),
    H_inf=sum alpha_v h_v^rad,
    r_v<=pi gives H_inf<=log pi (not <=0),
    F=Q: H_inf=log r, necessary r>=p^{d_p} (or exp(D_C)).

The paper-level theorem must state which norm is used. Task-156 mixes the
shell formula with IV normalization citations. Until reconciled, the h_inf
sign, shell-containment non-compensation, and required radius are conditional.

The product formula (A10) remains valid independent of this choice; it gives
only a point constraint.

## 9. Verdict summary

| item | classification |
|---|---|
| alpha_v=d_v/[F:Q], sum=1 | VALID (degree weights; watch d_v double count) |
| alpha_p finite weights | VALID as stated for places over p0 |
| (A2) local radial d_v log(r/pi) | CONDITIONAL/ERROR: conflicts with (A3) and IV norm |
| (A3) h_inf=sum alpha log(r/pi) | CONDITIONAL/ERROR: normalization and missing d_v |
| (A9) r_v<=pi => h_inf<=0 | CONDITIONAL; false under IV B_I norm |
| (A10) product formula | VALID |
| (A11)/(A12) bound | CONDITIONAL on normalization |
| (A13) angular term | CONDITIONAL; no actual construction |
| (A14)/(A15) D_C^Sp | CONDITIONAL on task-147/task-149 |
| (A16)/(A17) radius criterion | CONDITIONAL on normalization and finite/target conditions |
| b=3 d_p=408/41, r=pi*p^{d_p} | ARITHMETIC ERROR in task-156: used pi*exp(d_p), base e instead of p; correct ~1.574e41 |
| b=273 d_p=38883/41 | BRANCH AMBIGUOUS; h_A value, not B=O_K h_B; plus base-p error |
| target containment | NOT CLAIMED; task-149 conditions stand |

Overall: **CONDITIONAL WITH A NORMALIZATION ERROR**. The archimedean
qualitative point (product formula alone does not create a positive
compensation) is acceptable, but the specific h_inf formula, shell-containment
sign, and pi factor in the necessary radius are not valid paper-level
statements as written. No new attack, no Lean edits, no target accepted.