# C9 audit: complete-C construction obstruction (task-188)

Task: task-188. Audit of C9-FULLC-CONSTRUCTION-ATTACK-20261025.md.
Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language verification only. No Lean/Project edits,
no target changes, no new attack, no arbitrary data. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs

- C9-FULLC-CONSTRUCTION-ATTACK-20261025.md, 168 lines,
  SHA256 2e37310dd3eb96135d8e13dc7ce7205a6f43c85f21720daa28bab3745d6d08bd.
- C9-MASTER-CONTRADICTION-20261025.md, current master route.
- IUT I May 2020, Definition 3.1(a)-(f), and the frozen clause summaries in
  C9-FULLC-CONSTRUCTION and C9-FULLC-WEIGHTS.

The audited file does not construct a complete C. Its central claim is:
(1) the field-level start must contain Q(zeta_12); (2) the local start
p=12301, e=41, b=3, q=p^6 is available locally; (3) the first actual missing
object is an elliptic curve E/F satisfying the candidate conditions (4.1).

This audit independently checks each step and classifies actual / conditional /
missing / impossible. It does not supply a new curve or a new arithmetic attack.

## 1. Executive verdict

1. The field-level constraint is correct: if E[2] and E[3] are full over F and
   sqrt(-1) isin F, then Q(zeta_12) subset F. F=Q(zeta_12) has degree 4 over Q,
   is Galois, and 41 does not divide 4. This part is ACTUAL paper-level
   necessary condition.

2. The splitting/local facts are correct: p=12301 is prime, p=1 mod 12, so p
   splits completely in F=Q(zeta_12) (four places); p=1 mod 41, so mu_41 subset
   Q_p and the tame totally ramified cyclic K=Q_p(pi), pi^41=p, degree 41,
   exists. This part is ACTUAL local arithmetic.

3. The q=p^6 step has a genuine omitted unit. The tame local model gives
   qhat=pi^b and q_Tate=qhat^{2l}. With b=3, l=41 and pi^41=p u,
   u in Z_p^times,

       q_Tate = pi^{2bl} = pi^{246} = (pi^41)^6 = p^6 u^6.

   Thus q=p^6 requires u=1 (e.g. the Kummer field K=Q_p(p^{1/41})). The
   audited file writes pi^41=p u and then q=p^6 without this normalization;
   the correct general value is p^6 u^6. The valuation v_p(q)=6 is unchanged,
   but the exact Tate parameter is not p^6 for arbitrary u. This is a
   CONDITIONAL/arithmetic correction, not a fatal error for the candidate
   profile.

4. The claimed first obstruction is genuine as a MISSING ACTUAL OBJECT, not a
   proved impossibility: no explicit E/F with field of moduli Q, stable
   reduction everywhere, full E[6] over F, bad reduction at p=12301, local
   Tate parameter p^6, and mod-41 image containing SL2(F_41) is constructed.
   The audited file correctly says the obstruction is missing, not impossible.

5. The precise (4.1) is a CANDIDATE-PROFILE obstruction, not a necessary
   condition for every complete C: q=p^6 and the b=3 profile are chosen local
   data. A complete C can in principle have other bad primes/local types; the
   first source-level obstruction for a general complete C is the actual
   elliptic curve E in clause (b), and q=p^6 is extra candidate data. The file
   should label (4.1) accordingly.

6. The full E[6]/field of moduli/mod-41 conditions are not implied by the
   local q candidate. Local q=p^6 gives local 6-torsion over Q_p(zeta_6) at p,
   not global E[6] over F=Q(zeta_12); a rational j does not supply a global
   equation, stable reduction, torsion fields or mod-41 image. These are
   MISSING, not derived.

7. No complete C is constructed. The first obstruction is real: no actual
   curve/equation/discriminant/conductor/torsion-field/bad-set computation
   exists. F=Q(i) alone is impossible for full E[3]. Shortcuts
   S_bad={12301} and 'take q=p^6 globally' are invalid. P6 is not advanced.

## 2. Detailed verification

### 2.1 Field constraint (ACTUAL)

IUT I Definition 3.1(a) requires a number field F with sqrt(-1) in F.
Definition 3.1(b) requires the 2- and 3-torsion points of E_F to be rational
over F.

If E[3](F) is full, then the mod-3 Galois representation is trivial on G_F.
Its determinant is the cyclotomic character chi_3: G_F -> mu_3, hence chi_3 is
trivial on G_F. Therefore mu_3, equivalently Q(zeta_3), is contained in F.
With sqrt(-1) in F, the compositum

    Q(i, zeta_3) = Q(zeta_12)

is contained in F. This is a correct necessary condition.

Caveats:

- The argument uses full E[3], not just one 3-torsion point. The file states
  this correctly.
- E[2] full does not add a new root of unity: the Weil pairing is in mu_2={±1};
  sqrt(-1) comes from clause (a), not from E[2]. The file does not claim
  otherwise.
- The condition is necessary, not sufficient. E[2]/E[3] fields are generally
  nonabelian; Q(zeta_12) is abelian of degree 4 and does not contain an
  arbitrary E[2] or E[3] field. The file states the actual E is missing.
- F=Q(i) alone cannot satisfy full E[3]; the file's impossibility statement is
  correct.

### 2.2 Degree and splitting (ACTUAL)

Q(zeta_12)/Q is cyclotomic Galois with

    [Q(zeta_12):Q] = phi(12) = 4,

and 41 does not divide 4. Thus the "degree prime to l=41" part of clause (b)
is satisfiable by F=Q(zeta_12).

p=12301 is prime (no divisor at most sqrt(12301) ~ 110.9; checked exactly).
p mod 12 = 1, so p splits completely in Q(zeta_12): there are phi(12)=4 places
of F over p. The file's statement "four places over p" is correct. The section
V of Definition 3.1(e) selects one of them; this is formal, not a construction
of E.

Also p mod 41 = 1, so Q_p contains mu_41. The Kummer field

    K = Q_p(pi),  pi^41 = p,

is totally ramified of degree 41 and cyclic; since p=12301 does not divide 41,
the extension is tame. Thus the local field used in TAME exists. This is
ACTUAL local arithmetic.

### 2.3 q=p^6 (CONDITIONAL; omitted unit)

TAME uses the local model

    q_Tate = qhat^{2l},   qhat = pi^b,   pi^41 = p u,   u in Z_p^times,

with e=l=41 and b=3. Then

    q_Tate = pi^{2bl} = pi^{246}.
    pi^{246} = (pi^41)^6 = (p u)^6 = p^6 u^6.                  (2.3-correct)

The audited file states q_Tate=qhat^{2l} and q=p^{2b}=p^6, but its own
hypothesis is pi^41=p u. The equality q=p^6 therefore requires u=1. If u is a
nontrivial unit, q=p^6 u^6, not p^6.

This does not affect the p-adic valuation:

    v_p(q) = 6,  gcd(6,41)=1.

It does affect the exact Tate parameter, the q-parameter order, and any global
equation/twist. A complete construction must either:

- choose the Kummer field with u=1, e.g. K=Q_p(p^{1/41}); or
- record q=p^6 u^6 and carry the unit twist through the local/global data.

The file should not write q=p^6 while keeping an arbitrary u. This is a real
arithmetic shortcut; classify q=p^6 as CONDITIONAL on u=1 (or on a twist that
removes u^6).

The file's note that the q-order condition still needs the actual q-parameter
order is correct: v_p(q)=6 prime to 41 is not the same as the clause (c)
order condition.

### 2.4 Field of moduli, stable reduction and E[6] (MISSING)

The file lists the required actual curve conditions:

    field of moduli Q, stable reduction everywhere,
    full E[2]/E[3] over F, bad reduction at p=12301, local q=p^6.   (4.1)

This is the right shape of the missing object. It is not proved impossible.
Audit points:

- A rational j-invariant, e.g. the Tate j(p^6), gives at most a curve over Q
  abstractly. It does not supply an equation, discriminant, conductor, bad set,
  or the field-of-moduli/torsion conditions.
- Full E[6] over F is equivalent to full E[2] and E[3] over F (coprime
  decomposition), so the torsion requirement is not stronger than clause (b).
  It is, however, a global condition; local q=p^6 only gives local 6-torsion at
  p over Q_p(zeta_6), not global E[6] over Q(zeta_12).
- p=12301 is a multiplicative-reduction place for a Tate q candidate, so the
  local mod-41 image at p is not SL2; the global image containing SL2 must come
  from other places. No matrix computation exists.
- Stable reduction everywhere and field of moduli Q simultaneously with the
  chosen local q are not automatic from a rational j. The file flags this.
- The field of moduli of an elliptic curve with rational j is Q in the usual
  sense (j determines the geometric isomorphism class), but the actual E/F
  equation/twist remains missing. The file's wording "field of moduli Q" is
  acceptable for a candidate, not a construction.

### 2.5 First obstruction (MISSING, not impossible; candidate-specific)

The audited file's first-obstruction statement is:

    no actual E/F with (4.1) is supplied; this is a missing actual object,
    not a proved impossibility.

This is correct as a missing-object statement. It is also correct that the
obstruction is prior to S_bad, per-p e_p/b_p, q/BPS, weights and target column:
all of those require E.

Two qualifications:

1. The general complete-C obstruction is the curve E in clause (b). The
   additional q=p^6 and b=3 conditions in (4.1) are a chosen candidate profile,
   not necessary for every complete C. If no E with q=p^6 exists, that blocks
   this candidate profile, not all complete C. The file should say
   "candidate-profile first obstruction" for (4.1).
2. The file correctly rejects the shortcuts S_bad={12301} and "take q=p^6
   globally." A real E can have additional bad primes; the bad set is finite
   but not constructed. No theorem produces E with bad reduction exactly at
   12301 and good reduction elsewhere.

### 2.6 Downstream objects (MISSING)

Even if E satisfying (4.1) were supplied, the following remain missing:

- actual S_bad(C), per-p e_p/b_p and local types;
- q/BPS/Theta-gluing, row/Theta weights and fixed q-volume class;
- TC-A..TC-H/TC-S target containment and normalized-volume compatibility;
- actual archimedean r_v/h_inf under the binding B_I-zero normalization;
- full barGamma/H_A-full branch data;
- complete C and P6.

The curve construction is necessary but not sufficient.

## 3. Exact arithmetic record

- phi(12)=4; 41 does not divide 4.
- 12301 is prime; 12301 mod 12 = 1; 12301 mod 41 = 1.
- p splits completely in Q(zeta_12): 4 places.
- mu_41 subset Q_p; K=Q_p(pi), pi^41=p, is tame totally ramified of degree 41.
- qhat=pi^3; q_Tate=qhat^{82}=pi^{246}.
- If pi^41=p u, q_Tate=p^6 u^6; q_Tate=p^6 iff u=1.
- v_p(q_Tate)=6; gcd(6,41)=1.
- No explicit curve equation/discriminant/conductor exists in the audited file.

## 4. Error/overclaim ledger

| id | item | verdict | correction |
|---|---|---|---|
| A1 | q_Tate=p^6 from pi^41=p u | CONDITIONAL/OVERCLAIM | q=p^6 u^6; require u=1 or carry unit twist. |
| A2 | q=p^6 as exact local parameter for arbitrary K | CONDITIONAL | q=p^6 only for u=1/twist; valuation 6 always. |
| A3 | (4.1) as general first obstruction | CANDIDATE-SPECIFIC | General first object is E in clause (b); q=p^6/b=3 is extra profile data. |
| A4 | F=Q(zeta_12) necessity | ACTUAL | Valid from clause (a)+full E[3]; necessary not sufficient. |
| A5 | F=Q(i) for full E[3] | IMPOSSIBLE | Correctly rejected; E[3] full forces zeta_3 in F. |
| A6 | degree 4 prime to 41 | ACTUAL | phi(12)=4; 41 does not divide 4. |
| A7 | p=12301 splits completely | ACTUAL | p=1 mod12; four places. |
| A8 | tame e=41 local field | ACTUAL | p=1 mod41; Kummer extension exists. |
| A9 | full E[6] over F=Q(zeta_12) | MISSING | Local q=p^6 does not give global E[6]; actual E/torsion field missing. |
| A10 | mod-41 image contains SL2 | MISSING | No actual E or matrix computation; bad p local image is not SL2. |
| A11 | stable reduction everywhere + field of moduli Q + local q | MISSING | Rational j candidate does not supply equation/bad set/twist. |
| A12 | S_bad={12301} shortcut | INVALID | Actual E may have other bad primes; no such theorem. |
| A13 | q=p^6 globally without E | INVALID | q is local parameter; global discriminant/torsion missing. |
| A14 | q-order condition from valuation 6 | NOT PROVED | Clause (c) order check still needs actual q-parameter. |
| A15 | complete C constructed | INVALID/NOT DONE | Only candidate skeleton; no actual E/global data. |

## 5. Classification

ACTUAL (paper/local arithmetic):

- Clause (a)+(b) implies Q(zeta_12) subset F for full E[2]/E[3].
- [Q(zeta_12):Q]=4, Galois, prime to 41.
- p=12301 prime, p=1 mod12, four places; p=1 mod41, mu_41 subset Q_p.
- Tame totally ramified cyclic K=Q_p(pi), pi^41=p, degree41 exists.
- q_Tate=qhat^{2l} with qhat=pi^b; valuation v_p(q)=6 for b=3.
- F=Q(i) cannot satisfy full E[3].
- No explicit E/F equation/bad set/torsion/mod41 data is present.

CONDITIONAL:

- q=p^6 (only u=1 or a unit twist removed).
- A candidate E with rational j=Tate j(p^6)/field of moduli Q; actual equation,
  stable reduction and local q not constructed.
- Full E[6] over F=Q(zeta_12), mod41 image containing SL2, and bad at 12301:
  conditional on an actual E not supplied.
- Any downstream S_bad/weights/TC/arch data conditional on E.

MISSING:

- Actual E/F satisfying clause (b) and candidate (4.1).
- Equation, discriminant, conductor, torsion fields, bad set.
- Mod-41 image computation.
- Actual K/CK/V/epsilon and q/BPS/gluing data.
- TC-A..TC-H/TC-S, full barGamma/H_A-full, arch r_v/h_inf, complete C.

IMPOSSIBLE/WITHDRAWN:

- F=Q(i) alone for full E[3].
- S_bad={12301} as an arbitrary shortcut.
- q=p^6 as a global parameter without an actual E.
- Complete C or P6 from the local candidate alone.

## 6. Conclusion

The audited file's field-level constraint and local p=12301/e=41 facts are
correct. The first real obstruction is the missing actual elliptic curve
E/F and its equation/torsion/bad-set data; this is a missing-object obstruction,
not a proof of impossibility. The q=p^6 claim needs the unit correction:
q_Tate=p^6 u^6, with q=p^6 only when u=1 or after an explicit twist. The
precise (4.1) is a candidate-profile obstruction; it should not be presented as
a necessary condition for every complete C. No complete C is constructed, and
P6 remains open.

## 7. Status

- Natural-language audit only; no Lean/Project edits; no new attack.
- Field necessity, degree/splitting, tame local existence: verified actual.
- q=p^6: conditional; missing u=1/twist; valuation 6 correct.
- First obstruction: missing actual E/F, not impossible; candidate-specific.
- Complete C: not constructed; P6 open; target_accepted=false.
