# C9 explicit computational search for E with required local data

Task: task-192 (Explicit computational search for E with required local data).
Owner: volumedet. Date: 2026-10-25. Stage1 natural-language/exact-computation
only; no Lean/Project/target edits; only this file written. `target_accepted=false`.

Inputs: task-183 `C9-FULLC-CONSTRUCTION-ATTACK-20261025.md`; task-191/192
context; corrected donor/errata from task-147/149/161/171/181. The task-183
q=p^6 and rational-j assumptions are NOT assumed; they are checked below.

## 0. Verdict

1. The local identity q_Tate=p^6 is correct only after the omitted unit is
   fixed: qhat=pi^b, q_Tate=qhat^{2l}=pi^{2bl}; for b=3 this is
   pi^{246}=(pi^41)^6=p^6 u^6, so q=p^6 requires u=1. A local Tate curve with
   q=p^6 exists.
2. The claimed rational j-invariant j(p^6) is not rational under the p-adic
   Mahler-Manin theorem: for algebraic q with 0<|q|_p<1, j(q) is
   transcendental over Q. Since q=p^6 is algebraic and |q|_p=p^{-6}<1,
   j(p^6) is transcendental; in particular not rational.
3. Consequently there is no elliptic curve over Q or over Q(zeta_12) (indeed
   over any number field) with local Tate parameter q=p^6 at a
   multiplicative-reduction place and algebraic j. A number-field E has
   algebraic j, while Tate uniformization would give j=j(q), transcendental.
   This is a no-go, not merely a missing equation.
4. The no-go also applies to the TAME profile q_Tate=pi^{2bl} with integer b:
   q_Tate is algebraic in K_v, so a global number-field E with that exact Tate
   parameter would have transcendental j, contradiction. Under the cited
   theorem, the tame b-profile cannot be realized by a global number-field E.
5. What remains actual: the local Q_p Tate curve; exact p-adic valuation and
   q-expansion computations. What remains conditional: the Mahler-Manin
   external theorem (not formalized here). What remains missing: an explicit
   global E with the required local data; LMFDB/Cremona data access; full
   E[6] global torsion; mod-41 image; TC conditions.

## 1. Local arithmetic verification

    p=12301 is prime, p=1 mod 12, p=1 mod 41, p=1 mod 6.

Let K=Q_p(pi), pi^41=p u, u in Z_p^×, e=41, b=3. The TAME local model gives

    q_Tate = qhat^{2l} = (pi^b)^{2l} = pi^{2bl}.
    For b=3:  pi^{246} = (pi^41)^6 = (p u)^6 = p^6 u^6.        (1.1)

Thus q_Tate has valuation 6, and q_Tate=p^6 exactly iff u=1. The unit is a
real omission in task-183; q=p^6 is conditional on u=1 (or on a twist that
removes u^6). The valuation and the local field are actual; the exact
parameter p^6 is a normalized subcase.

Exact checks run in Python (big integers):

```python
p = 12301
assert all(p % q for q in range(2, 112))       # prime
assert (p % 12, p % 41, p % 6) == (1, 1, 1)
q = p**6
assert q % p == 0                              # v_p(q)=6
assert (p-1) % 6 == 0                          # mu_6 subset Q_p
```

Output: p prime True, p mod 12/41/6 = 1/1/1, v_p(q)=6, mu_6 available.

## 2. Tate j(q) and the rationality check

The Tate j-function is

    j(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + ...
         = q^{-1} + 744 + sum_{n>=1} c_n q^n,   c_n in Z.       (2.1)

For q=p^6, the inverse term has v_p=-6; all other terms have v_p>=0,
so

    v_p(j(p^6)) = -6,       p^6 j(p^6) = 1 + 744 p^6 + ... .   (2.2)

So j(p^6) is not p-integral. In particular it is not a rational integer and
not p^6 (which has v_p=+6). If it were rational, its denominator would have
to be divisible by p^6; that is not the same as the task-183 claim of a
rational j-invariant.

Exact Python check of the leading term and first coefficients:

```python
c = [196884, 21493760, 864299970, 20245856256, 333202640600,
     4252023300096, 44656994071935, 401490886656000,
     3176440229784420, 22567393309593600]
N = 60; M = p**N
A = 1 + 744*(p**6)
for k, ck in enumerate(c, start=1):
    A = (A + ck * pow(p, 6*k+6, M)) % M
assert A % p == 1
assert p**6 == q
print(A % p**12)
```

Output: `A mod p = 1`, `A = p^6 j(p^6) mod p^60` is a nontrivial 30-digit
base-p number, not 1; in particular p^6 j(p^6) is a p-adic unit, not the
integer 1.

### 2.1 External theorem: Mahler-Manin

The p-adic Mahler-Manin theorem (proved by Barre-Sirieix, Diaz, Gramain and
Philibert; Zbl 0853.11059) states: if q is algebraic with 0<|q|_p<1, then
j(q) is transcendental over Q. For q=p^6 this applies. Therefore
**j(p^6) is not rational**; task-183's phrase 'rational j-invariant j(p^6)'
is incorrect. This theorem is external and was not formalized here; the
computation in (2.2) independently shows the p-adic valuation obstruction.

If one accepts the theorem, the no-go below is actual (external theorem +
local algebra). If one does not accept it, the rationality remains an open
external question, but the computational evidence and valuation show that
task-183 cannot assert rationality.

## 3. No global E with q=p^6 and algebraic j

Let E be an elliptic curve over a number field F, and let v be a
multiplicative-reduction place with residue characteristic p=12301 and Tate
parameter q_E in F_v=Q_p. Tate uniformization gives

    E_{/F_v} = E_{q_E},     j(E) = j(q_E).                    (3.1)

Suppose q_E=p^6. Then j(E)=j(p^6) is transcendental by §2.1, but j(E) is
algebraic (indeed in F). Contradiction. Therefore:

**No elliptic curve over any number field has local Tate parameter q=p^6 at
a multiplicative-reduction place.**

This excludes E/Q and E/Q(zeta_12) with j in Q; that is, the required object
(E, j in Q, bad at 12301, local q=p^6) does not exist. The obstruction is
not a missing equation; it is a theorem-level incompatibility.

Consequences for the C9 profile:

- q_Tate=(pi^b)^{2l}=pi^{2bl} with b in Z is algebraic in K_v for every b,
  so under the same theorem no global number-field E can have this exact
  Tate parameter. The tame b=3 profile with q=p^6 is therefore not
  realizable by a global E (conditional on the external theorem).
- If one only asks for 'bad reduction at 12301 and some q', a global E can
  have transcendental q and algebraic j; but then q is not p^6 and the
  b=3/TATE q relation fails.
- Additive reduction places have no Tate q; they cannot satisfy the local
  q=p^6 condition either.

## 4. Explicit local object that DOES exist

The local Tate curve over Q_p with q=p^6 exists:

    E_q(C_p) = C_p^× / q^Z,     q=p^6,
    j(E_q) = j(p^6) (transcendental).

Standard Tate Weierstrass model (p-adic, not a finite rational equation):

    y^2 + xy = x^3 + a_4(q) x + a_6(q),
    a_4(q) = -5 sum_{n>=1} n^3 q^n/(1-q^n),

Discriminant and reduction:

    Delta(q) = q prod_{n>=1}(1-q^n)^{24},    v_p(Delta)=6,
    multiplicative reduction at p, conductor exponent 6.

Torsion: since q=p^6 is a sixth power and mu_6 subset Q_p (p=1 mod 6),

    E_q[6] subset E_q(Q_p),

by the Tate parametrization E_q[n] = mu_n × q^{Z/n} with q^{1/6}=p in Q_p.
Thus the local E[6] condition is satisfied; what fails is the global
number-field rational-j condition.

This is an **actual local** object; it is not an E over Q or over Q(zeta_12)
and cannot be globalized with algebraic j.

## 5. Search for explicit E and alternatives

### 5.1 Database/web search

Attempted LMFDB/Cremona access:

- LMFDB API (`https://www.lmfdb.org/api/ec_curves/...`) is blocked in this
  environment: hostname resolves to a non-public IP, so no LMFDB rows were
  retrieved.
- Web search returned only general references and no explicit curve with
  conductor/bad prime 12301; no local Cremona/LMFDB database is present.
- Therefore no explicit E with the required data was obtained from a
  database; this is a data-access gap, not evidence of existence.

### 5.2 Alternatives checked

1. **Rational j = p^6, local q=p^6.** Impossible: j=p^6 has v_p=+6, while a
   Tate q=p^6 gives j(q) with v_p=-6; moreover q=p^6 => j transcendental.
2. **j = j(p^6) (Tate specialization).** j is transcendental, so no
   number-field E; only the local Q_p Tate curve. Task-183's rational-j
   assumption is false.
3. **Change q to p^6 u^6 or any algebraic q in pZ_p.** Same Mahler-Manin
   contradiction; no global number-field E with algebraic Tate q.
4. **Drop q=p^6 but keep rational j.** Then q is (generically) transcendental
   p-adically; the TAME relation q=pi^{2bl} with pi algebraic fails. This
   abandons the b=3 local profile, not an alternative realization of it.
5. **CM curves j=0,1728 and other integral j.** j is p-adic integral (v_p>=0),
   so multiplicative reduction at p with positive-valuation Tate q is
   incompatible; CM curves have potential good reduction, no q=p^6 at p.
6. **Twists.** Quadratic twists preserve j; they change the Tate parameter
   by algebraic factors. If the resulting q were algebraic, the theorem
   still forbids a global number-field E; if q is transcendental, q≠p^6.
7. **Full E[6] over Q(zeta_12).** This is a separate global torsion
   condition; it may be satisfiable by some E, but no such E with q=p^6 can
   exist under the theorem. A search for full E[6] alone was not completed
   because the q-requirement already gives a no-go; any future candidate
   must drop q=p^6.

### 5.3 What a successful alternative would have to drop

The task-192 list requires simultaneously: j in Q, full E[6] over
Q(zeta_12), bad at 12301, local q=p^6. The no-go kills the conjunction
'j in Q + local q=p^6'. Thus at least one of the following must be dropped:

- rational/algebraic j (then no number-field E; only local p-adic object);
- q=p^6 (then the b=3 TATE profile and its D3 computation do not apply);
- the multiplicative-reduction/Tate model at p (additive reduction has no q).

None of these is an actual construction of the original object.

## 6. Actual / conditional / missing

ACTUAL (exact/local/external):

- p=12301 prime, p=1 mod 12/41/6; q=p^6 is algebraic, |q|_p<1, v_p(q)=6.
- q_Tate=pi^{2bl}=p^{2b} u^{2b}; for b=3 q=p^6 iff u=1.
- Local Tate curve E_q over Q_p with q=p^6, multiplicative reduction,
  full E[6] over Q_p, j(q) transcendental.
- v_p(j(p^6))=-6 and p^6 j(p^6) ≡ 1 mod p; exact Python check.
- External Mahler-Manin theorem (cited, not formalized): algebraic q with
  0<|q|_p<1 => j(q) transcendental.

CONDITIONAL (on external theorem):

- No number-field E with local q=p^6 and algebraic j.
- No global realization of the TAME b-profile q=pi^{2bl} with algebraic j.

MISSING:

- An explicit E/Q or E/Q(zeta_12) with j in Q, full E[6], bad at 12301,
  local q=p^6: does not exist under the theorem; without the theorem no
  construction exists.
- LMFDB/Cremona rows and a completed database search (access blocked).
- Full global E[6] torsion field for any curve, mod-41 image containing
  SL2(F_41), conductor/bad set, TC-A..TC-H/TC-S.

IMPOSSIBLE/WITHDRAWN:

- task-183's rational j(p^6) assumption (j(p^6) transcendental).
- j=p^6 with local q=p^6 (valuation mismatch and theorem).
- q=p^6 as a global parameter with algebraic j.
- Claiming an explicit E with the required data from LMFDB/Cremona: none
  found, and the q-requirement is theorem-obstructed.

## 7. Conclusion

The requested object (E/Q or E/Q(zeta_12), j in Q, full E[6] over
Q(zeta_12), bad at p=12301, local q=p^6) is not constructed. More strongly,
under the cited p-adic Mahler-Manin theorem it cannot exist: q=p^6 is
algebraic with |q|_p<1, so j(q) is transcendental, while a number-field E
has algebraic j. The local Tate curve is the only actual object; it has
transcendental j and cannot be globalized as a number-field elliptic curve.
Task-183's 'rational j(p^6)' is false; its q=p^6 also requires u=1. The
remaining missing objects are a global E without q=p^6 (if the b=3 profile
is dropped), or a new local model with transcendental q (not the TAME
algebraic q=pi^{2bl}). No arbitrary curve, no arbitrary j, and no Lean edits
were used.

## 8. Status

Stage1 natural-language/exact computation only. External Mahler-Manin
theorem not independently formalized. Lean/Project/kernel/comparator/
independent review not run. Only this file written. `target_accepted=false`;
complete C9/P6 not proved.
