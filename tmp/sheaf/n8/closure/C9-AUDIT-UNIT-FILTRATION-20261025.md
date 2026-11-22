# C9 audit: does Out(G_K) preserve the unit filtration U^n?

Task: task-208. Auditor: qside. Date: 2026-10-25.
Stage: independent natural-language/local-mathematics verification; no Lean/Project
or target edits; only this file written.

Audited task: task-204 / `C9-HAFULL-INTEGRALITY-20261025.md`, SHA256
`16523153A35BF386899AC2F36EB6DB53C777F7CA704034615646BD84DF002929`.
Primary paper sources re-read:

- Kondo 2025, `sources/Kondo-2512.09231v1.html`, SHA256
  `FF39006CF92EC22E1A39CAA89FEE9B86080953861D7AC6405E6919338C5C9E6F`,
  Theorem A (field-theoretic subgroup criterion, condition (3)).
- Kondo 2026, `sources/Kondo-2605.25428v2.html`, SHA256
  `FE7C464E2AE09FFC85C4B02CAD8B10B7EEBEF351113975A34C53A62169A27D86`,
  Lemma 3.3 / Definition 3.2 (Sp donor and `H = Phi^{-1}(Sp)`).

## 0. Verdict

**The central premise of task-204 is FALSE.** It is not true that every
`alpha in Out(G_K)` preserves the upper ramification filtration and hence every
unit filtration `U^n = 1 + pi^n O_K` under local reciprocity.

The exact paper statement is Kondo 2025, Theorem A: for an automorphism `alpha`
of `G_K`, the following are equivalent:

1. the outer class of `alpha` lies in the field-theoretic subgroup
   `Aut(k) subset Out(G_K)`;
2. ... (Hodge-Tate transport conditions);
3. `alpha` is compatible with the filtration on `G_K` given by the
   [positively indexed] higher ramification subgroups in the **upper**
   numbering;
4. ... additive `(kbar_hat)_+` transport condition.

Thus the stabilizer of the upper ramification filtration is the **finite**
field-theoretic subgroup `Aut(k)`, not all of `Out(G_K)`. Kondo explicitly calls
`Aut(k)` a necessarily finite subgroup of `Out(G_K)` and uses condition (3) as a
criterion distinguishing it from the much larger outer automorphism group.

Task-204's sentence

> the higher ramification subgroups of `G_K` (upper numbering) are
> group-theoretic; ... Therefore every automorphism of `G_K` preserves
> the filtration`

is therefore an abuse: the upper filtration is compatible with the
**field-theoretic** automorphisms, not with all continuous group automorphisms.
Task-204 correctly uses upper (not lower) numbering, but incorrectly treats the
upper filtration as characteristic in the abstract profinite group `G_K`.

## 1. The precise local reciprocity normalization

Local reciprocity gives `rec_K : profinite-completion(k^times) -> G_K^ab`.
Local class field theory identifies the unit filtration with higher ramification
subgroups only after fixing the upper/lower numbering convention. The standard
theorem is of the form

```text
rec_K(U_K^n) = (some upper ramification subgroup of G_K^ab)
(up to a fixed index shift depending on K and the chosen numbering).
```

Important consequences:

- The correct correspondence is with **upper** numbering, so task-204's choice
  of upper numbering is not itself the error.
- A fixed index shift does not matter for stability of `U^n`: if every upper
  subgroup were preserved, the preimage filtration `U^n` would be preserved
  even after a shift.
- The fatal point is different: **not every** `alpha in Out(G_K)` preserves the
  upper ramification filtration. Kondo 2025 Theorem A says exactly that
  preserving it is equivalent to being field-theoretic.

Lower numbering would be even worse: the lower filtration is not the
automorphism-invariant one in this comparison. But replacing upper by lower
would not repair task-204; the correct upper statement already fails for full
`Out(G_K)`.

## 2. Characteristic-subgroup issue

The inertia subgroup and the wild inertia subgroup are characteristic in `G_K`
(they are group-theoretically singled out), but the **higher** upper
ramification filtration is not characteristic under all abstract automorphisms
of `G_K`. Kondo 2025 Theorem A is precisely the theorem that identifies the
automorphisms compatible with the full upper filtration as the finite subgroup
`Aut(k)` of `Out(G_K)`. Hence:

```text
{alpha in Out(G_K) : alpha preserves every upper G_K^u} = Aut(k),
|Aut(k)| < infinity.
```

Task-204's use of the word `group-theoretic` conflates two different things:

- the **field-theoretic subgroup** `Aut(k)` is group-theoretically definable by
  the Kondo/Anabelian criterion, but it is only a finite subgroup;
- a general `alpha in Out(G_K)` need not lie in it, and then `alpha^times` need
  not preserve any of the higher unit groups `U^n`.

The fact that `Out(G_K)` contains the actual symplectic donor
`H = Phi^{-1}(Sp_{2g}(Z_p))` (Kondo 2026 Lemma 3.3) makes the distinction
non-vacuous. `H` has infinite image `Sp_{2g}(Z_p)`, while `Aut(k)` is finite;
therefore `H` is not contained in `Aut(k)`. By Theorem A, there exist actual
`alpha in H` that do **not** preserve the upper ramification filtration.

## 3. Explicit obstruction / counterexample

A fully explicit matrix for one such `alpha` is not needed to refute the
all-`Out` premise; the following is an actual obstruction from the cited
theorems.

### 3.1 Infinite donor versus finite field subgroup

1. Kondo 2026, Lemma 3.3: `Phi(Out(G_K))` contains `Sp_{2g}(Z_p)`;
   `H = Phi^{-1}(Sp_{2g}(Z_p))` is an actual closed subgroup of `Out(G_K)` with
   infinite image.
2. Kondo 2025, Theorem A: the subgroup of `Out(G_K)` preserving the upper
   ramification filtration is exactly the field-theoretic subgroup `Aut(k)`,
   which Kondo states is necessarily finite.
3. Therefore `H` is not contained in `Aut(k)`. Choose
   `alpha in H minus Aut(k)`; by Theorem A, `alpha` does not preserve the upper
   filtration, so for some `u` (equivalently some unit level `n`)
   `alpha^times(U^n) != U^n`.

This is an actual existence obstruction, not an abstract `GL_d` model: `H` is
the corrected actual donor of Kondo 2026 (see task-147/`C9-SYMPLECTIC-SOURCE`).

### 3.2 Kondo 2025 Theorem B

Kondo 2025 Theorem B constructs an actual `k/Q_p` and an actual group
automorphism `phi` of `G_k` such that `rho o phi` is not Hodge-Tate for an
irreducible Hodge-Tate `rho`. By Theorem A, `phi` cannot preserve the upper
ramification filtration. This is a second, independent actual counterexample to
the statement 'every automorphism of `G_K` preserves the upper filtration'.
It is not claimed here that this particular `phi` lies in the C9 donor `H`; the
`H`-argument of §3.1 is the donor-specific obstruction.

## 4. What part of task-204 survives

### 4.1 The local unit calculation is correct

With `K/Q_p` tame totally ramified, `e=41`, `p=12301`:

```text
pi^e = p u,  pO_K = pi^e O_K,
U^e = 1 + pO_K.
```

Since `exp_k` converges on `pO_K` and `log_k` converges on `U^1`,

```text
exp_k(p) in 1 + pO_K = U^e,  log_k(exp_k(p)) = p,
log_k(U^e) subset pO_K,  p^{-1} log_k(U^e) subset O_K.
```

These are valid local facts; no correction is needed here. The verification of
the term valuations is standard: for `x in O_K`,
`v(log(1+px)) >= min_n (n e - v(n)) >= e` for `e>=1`, because
`v(n) <= log_p n <= n-1`.

### 4.2 Kondo log compatibility is valid for all alpha

Kondo 2026 Theorem 2.6 proof gives the commutative diagram

```text
alpha_+ o log_k = log_k o alpha^times
```

on `O_K^times`; this is a functorial statement for every `alpha in Out(G_K)`,
not only field-theoretic ones. Hence task-204's identities

```text
alpha_+(p) = log_k(alpha^times(exp_k p)),
a(alpha) := p^{-1} alpha_+(p) = alpha_+(1)
```

remain formally true for every `alpha` (using `p` in `J`, `exp p` in `U^1`, and
`Q_p`-linearity). This is the part of task-204 that is not affected by the
filtration error.

### 4.3 What fails

The step

```text
alpha^times(exp_k p) in U^e  because alpha^times(U^e)=U^e
```

is false for general `alpha in Out(G_K)`. Consequently

```text
log_k(alpha^times(exp_k p)) in pO_K
```

need not hold, and

```text
a(alpha)=p^{-1} log_k(alpha^times(exp_k p)) in O_K
```

need not hold. For such `alpha`, `a(alpha)` is still in `I=p^{-1}J` because
Kondo log compatibility gives it as `alpha_+(1)` and H_A-lite gives `alpha_+(J)=J`,
but it may lie outside `O_K`. This is exactly the integrality obstruction the
earlier task-202/task-196 files identified; task-204's filtration claim
attempted to remove it but is unsupported.

## 5. Downstream consequences in task-204

| task-204 step | verdict | reason |
|---|---|---|
| `exp p in U^e`, `log U^e subset pO_K` | **VALID actual local algebra** | standard p-adic exp/log; see §4.1 |
| `alpha_+ log = log alpha^times` | **VALID paper-level (Kondo 2026 Thm2.6)** | functorial diagram |
| `a(alpha)=alpha_+(1)` | **VALID conditional on log compatibility** | §4.2 |
| every `alpha in Out` preserves upper filtration | **ERROR** | Kondo 2025 Thm A: only finite `Aut(k)` does |
| `alpha^times(U^n)=U^n` for all `alpha` | **ERROR/unsupported** | follows only for field-theoretic subgroup |
| `alpha^times(exp p) in U^e` for all alpha | **ERROR** | same |
| `a(alpha) in O_K` for all alpha | **NOT PROVED; generally false/source-unknown** | integrality obstruction remains |
| `alpha_+(O_K)=O_K` | **NOT PROVED for full Out** | depends on failed integrality |
| `B=O_K` for full Out | **INVALID as a conclusion** | task-204's elimination of B=I rests on failed premise |
| `B=I` excluded for full Out | **INVALID as a conclusion** | not established |
| H_A-full for full Out | **OPEN** | exact obstruction persists |

For the **field-theoretic subgroup** `Aut(k)` the filtration premise is true
(field automorphisms preserve the valuation and all `U^n`); task-204's argument
would then give H_A-full for `Aut(k)` and `B_Aut(k)=O_K`, which is already the
known subgroup result. It does **not** extend to the full `Out(G_K)` or to the
infinite symplectic donor `H`.

## 6. Normalization details and possible counter-arguments

### 6.1 Upper vs lower

Task-204 correctly says upper numbering. Kondo 2025 Theorem A condition (3)
explicitly uses '[positively indexed] higher ramification subgroups in the
upper numbering'. Even with this correct convention, the stabilizer is
`Aut(k)`, not `Out(G_K)`.

### 6.2 Shifted reciprocity indices

Local reciprocity may identify `U^n` with upper ramification subgroups only up
to a fixed index shift (depending on `K`, `e`, and conventions). This does not
repair task-204: a fixed shift would preserve all `U^n` if all upper subgroups
were preserved, but the latter fails for non-field-theoretic automorphisms.

### 6.3 `U^e=1+pO_K`

Correct: `pO_K=pi^e O_K` because `e` is the ramification index and
`pi^e=p u`. No issue.

### 6.4 `exp p`

Correct: `p` has valuation `e>1`; `exp` converges on `m` and `p in pO_K`;
`exp(p) in 1+pO_K`. No issue.

### 6.5 Is `alpha^times` the inverse action?

Even if the reciprocity convention makes `alpha^times` the inverse of the
conjugate action, an inverse of a filtration-preserving automorphism also
preserves the filtration; inversion does not repair the failure. The issue is
the stabilizer of the filtration, not the direction of the action.

## 7. Classification

| item | classification |
|---|---|
| Kondo 2025 Thm A: filtration preserved iff field-theoretic | **BINDING paper theorem** |
| `Aut(k) subset Out(G_K)` finite | **BINDING paper statement** |
| upper (not lower) numbering in the criterion | **BINDING; task uses upper** |
| every `alpha in Out` preserves upper filtration | **ERROR (contradicted by Thm A)** |
| `alpha^times(U^n)=U^n` for all alpha | **ERROR** |
| `exp p in U^e`, `log U^e subset pO_K` | **VALID local algebra** |
| Kondo log compatibility `alpha_+ log=log alpha^times` | **VALID paper-level** |
| `a(alpha)=alpha_+(1)` | **VALID conditional** |
| `a(alpha) in O_K` for all full Out alpha | **NOT PROVED / obstruction** |
| H_A-full, B=O_K, B=I exclusion for full Out | **INVALID as derived in task-204** |
| H_A-full for `Aut(k)` / `Gamma_0` | **VALID conditional subgroup result only** |
| full H_A-full / full B branch | **OPEN** |

## 8. Final verdict

**Task-204's key premise fails.** The correct paper statement (Kondo 2025
Theorem A) is that preserving the upper ramification filtration characterizes
the finite field-theoretic subgroup `Aut(k) subset Out(G_K)`, not all of
`Out(G_K)`. Since the corrected donor `H=Phi^{-1}(Sp_{2g}(Z_p))` has infinite
symplectic image and `Aut(k)` is finite, there exist actual `alpha in H` outside
`Aut(k)`; those `alpha` do not preserve the filtration, so the claimed
`alpha^times(U^n)=U^n` and the resulting integrality of `a(alpha)` are not
available.

The local exp/log arithmetic and the Kondo log compatibility are valid, and
the canonical formula `a(alpha)=alpha_+(1)` survives. The integrality
`a(alpha) in O_K`, hence H_A-full and the `B=O_K` / `B=I` conclusions for full
`Out`, are **not** proved. Task-204's own `target_accepted=false` remains; its
claim that the integrality obstruction is removed by filtration must be
withdrawn.

This file contains no new attack and no Lean/Project edits. `target_accepted=false`;
full C9/P6 remains open.

## 9. Sources

- Kondo 2025, *Anabelian aspects of the outer automorphism groups of the
  absolute Galois groups of mixed-characteristic local fields*, local snapshot
  `tmp/sheaf/n8/closure/sources/Kondo-2512.09231v1.html`, SHA256
  `FF39006CF92EC22E1A39CAA89FEE9B86080953861D7AC6405E6919338C5C9E6F`;
  Theorem A, condition (3); Theorem B.
- Kondo 2026, *Lubin-Tate representations over nontrivial finite Galois
  extensions of Q_p are not Aut-intrinsically Hodge-Tate*, local snapshot
  `tmp/sheaf/n8/closure/sources/Kondo-2605.25428v2.html`, SHA256
  `FE7C464E2AE09FFC85C4B02CAD8B10B7EEBEF351113975A34C53A62169A27D86`;
  Theorem 2.6 proof (log compatibility), Definition 3.2 / Lemma 3.3 (Sp donor).
- `tmp/sheaf/n8/closure/C9-SYMPLECTIC-SOURCE-20261025.md`, SHA256
  `3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70`;
  corrected donor `H=Phi^{-1}(Sp)`, not `rho(Mod)=Sp`.
- `tmp/sheaf/n8/closure/C9-HAFULL-INTEGRALITY-20261025.md`, SHA256
  `16523153A35BF386899AC2F36EB6DB53C777F7CA704034615646BD84DF002929` (audited).

End of C9-AUDIT-UNIT-FILTRATION-20261025.