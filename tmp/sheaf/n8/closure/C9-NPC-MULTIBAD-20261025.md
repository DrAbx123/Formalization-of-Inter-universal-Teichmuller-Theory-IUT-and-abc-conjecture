# C9 NPC/U for the multi-bad b=273 target

Task: task-334. Date: 2026-10-25. Author: transport.
Uniform profile only; no mixed/E3; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-NPC-IND2-20261025.md | 136 | 60B24D744A1E509A9F04EEFC05D5F06AD4517C5684E1CB290E35B9F7B4B07184 |
| C9-DPRIMES-KODAIRA-20261025.md | 142 | DA7DFD3137E0D0287403390DAEE4039F5681648748E0366FF8D7A0A8A382AC70 |
| C9-B273-COMPLETE-C-20261025.md | 165 | 8CD5991AA2A8AD9528DD273F97C0BAEF6F1EAAF56FC1568AC049A2644A2AE437 |

## 1. Verdict

The M-prime III* places of E_546 do NOT enlarge the admissible V_bad target of
the b=273 complete C. The actual b=273 target remains single-bad-prime
V_bad={p=12301}; the task-325 procession NPC/U applies.

The reason is the IUT I Definition 3.1(b) definition: V_bad is a set of
nonarchimedean valuations of F_mod over which XF has bad **[i.e.,
multiplicative]** reduction. The M-primes have Kodaira type III*, which is
additive, not multiplicative. They are bad-reduction places in the loose
sense, but they are not admissible elements of V_bad. After the
semistabilization field F_sem they become good.

Therefore:

- no M-prime is a selected bad prime of the actual b=273 target;
- the M-prime III* local places contribute at most good-place volume0 after
  semistabilization; they do not add a positive finite bad class;
- the single-bad-prime NPC/U theorem applies to the actual b=273 target;
- conditional b=273 F>=8821.538890... is retained.

No explicit positive-volume uniform counterexample is constructed; the
III* places cannot supply one because they are additive/good, not selected
multiplicative bad places.

## 2. Source classification of the M-primes

From task-DPRIMES-KODAIRA:

    M=1728p^546-1,  each q|M:
    E_546 has Kodaira type III*, (v(c4),v(c6),v(Delta))=(3,5,9),
    local semistabilization degree4,
    after the quartic semistabilization E has good reduction.

Thus:

- over Q (or before semistabilization), M-primes are additive III*;
- over F_sem they are good;
- III* is not multiplicative, so it is not an admissible V_bad element under
  IUT I Def3.1(b);
- over Vgood_mod, Def3.1(b) explicitly allows bad reduction at some elements
  over good places; this does not make them V_bad.

The actual b=273 complete C uses F_sem (task-258). Hence
V_bad={p=12301}; M-primes are good finite places with normalized finite
contribution0.

## 3. Multi-bad extension theorem

For completeness, the procession invariance argument extends to an admissible
multi-bad multiplicative target.

Theorem 3.1 (multi-bad NPC). Let S be a nonempty set of selected multiplicative
bad primes, with the uniform all-bad profile. At each p in S:

    L_B^p = p^{s_p-r_p+1} J_p^{tensor r_p},   J_p=pi_p O_{K_p}.     (3.1)

Assume:

(M1) the local type at each p is the tame B=O_K/B=I type for which the
     procession invariance of task-325 applies;
(M2) no other selected bad local type is present;
(M3) good finite places have volume0;
(M4) TC-B/normalized-volume monotonicity.

Then the finite target hull is contained in the tensor product of the local
row hulls, and

    h_C <= sum_{p in S} alpha_p max(H_A^p,H_B^p) + h_inf.          (3.2)

Proof. At each p, the procession/capsule poly-automorphisms act by factor
permutations and D^dag isomorphisms preserving J_p, so L_B^p is invariant by
task-325. The tensor product over p is invariant under the product action.
Good places contribute0. The arch factor is h_inf. Monotonicity gives (3.2).
QED.

Caveat: if some selected bad p has a different local type (wild/e!=ell), M1
fails; then (3.1) and the row invariance are not available, and one needs a
separate local row classification. The M-prime III* places are not in S, so
this caveat does not affect the actual b=273 target.

## 4. Application to b=273

For E_546:

- selected bad set S={p=12301}, multiplicative I_546;
- M-primes III* are not selected V_bad; after F_sem they are good;
- good finite contributions are0;
- arch is h_inf.

Thus the actual b=273 target is single-bad; task-325 applies. Under TC-B and
the row-volume values:

    h_C <= H_B + h_inf,   H_B=(-38736/41)log p,                   (4.1)
    F >= (38463/41)log p - h_inf
       >= D_B - A_proc = 8821.538890... >0.                      (4.2)

This is the conditional b=273 counterexample; it requires the actual complete C
and TC/arch inputs, as before.

## 5. Exact obstruction

If one insists on treating the M-prime III* places as additional **selected
bad** places, the resulting object is not an IUT-admissible target:

- III* is additive, not multiplicative, so it cannot be in V_bad by Def3.1(b);
- it has no multiplicative q-parameter/B=O_K/B=I row;
- taking it as a selected bad place changes the target model (a profile/model
  change), not the original b=273 complete C.

Alternatively, one may semistabilize: F_sem makes them good, and they
contribute0. There is no source-valid positive-volume uniform class from these
places. No explicit counterexample to NPC/U is constructed.

The only remaining obstruction to the b=273 F>0 conclusion is the usual one:
actual complete C and NPC/U/TC/arch inputs, with NPC now supplied for the
single-bad selected set.

## 6. Conclusion

The M-prime III* places do not make the actual b=273 target multi-bad in the
IUT-admissible sense. V_bad requires multiplicative reduction; III* is
additive; F_sem makes the M-primes good and contributes zero finite volume. The
actual target has V_bad={p=12301}; the single-bad procession NPC/U theorem
applies, and the conditional b=273 counterexample F>=8821.538890... is
retained.

The multi-bad extension is available for selected multiplicative bad primes
with tame B-row local types (Theorem 3.1); other local types or III* selected
as bad are outside the target/admissibility. No mixed E3 and no arbitrary
region was used.

target_accepted=false.
