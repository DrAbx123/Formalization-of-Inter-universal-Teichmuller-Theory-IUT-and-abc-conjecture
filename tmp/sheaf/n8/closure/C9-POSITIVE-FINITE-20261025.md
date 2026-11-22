# C9 positive finite/global contribution: exact obstruction

Task: task-277 (NL theorem: new positive finite/global contribution). Owner:
volumedet. Date: 2026-10-25. Natural-language theorem/proof only. No arbitrary
weights, no Lean/Project/target edits. Only this file written.
`target_accepted=false`.

## 0. Result

The exact obstruction is: under the corrected C1 assembly and the conditional
local formulas, every source-derived finite/global term beyond the C1
bad-place sum and h_inf is zero or nonpositive, or is a branch-dependent
B=I term that is not actual. Consequently there is no genuine positive
source contribution of size +80.55 (b=3) or +8808 (b=273).

The short theorem below makes this precise. It is a non-positivity
obstruction, not a P6 proof.

## 1. Notation and C1

Let

    h_C = sum_p alpha_p h_p + h_inf(C) + E_extra(C),          (1.1)

where the first two terms are the corrected C1 assembly (bad finite places
plus archimedean; good places are zero relative to the reference). `E_extra`
denotes any additional source-derived finite/global contribution beyond C1
(tensor/order, Ind1-3, target saturation, row/Theta weights, other local
types). P6 is `h_C>=Q_C`; the b=3 B=O_K conditional finite deficit is

    D_3=408/41 log12301=93.71497127459669...,
    A=11.5 log pi=13.164393687268102...,
    D_3-A=80.55057758732859... .                            (1.2)

b=273 B=O_K: `D_273=8931.174578603292`, `D_273-A=8918.010184916024`; the
b=273 B=I value is `(38463/41)logp=8834.703284644149`, residual after A
`8821.538890956881`.

## 2. Theorem (no source-derived positive finite/global term)

Theorem 2.1. Assume the corrected C1 assembly and the conditional local
formulas. Let E be any source-derived finite/global correction beyond C1
that is available in the current corpus (good finite places, tensor/order,
Ind1-3, target saturation, row/Theta weights, other local types, B=I
b=3). Then any **actual, branch-independent** lower bound on E is <=0.
In particular E cannot supply +80.55 for b=3 or +8808 for b=273.

Proof. We exhaust the source branches:

1. Good finite places. At a good selected place the Gaussian profile is the
   unit and the tensor hull is the reference O_E; the normalized
   contribution relative to the reference is 0. Q_C has no good place term.
   Hence E_good=0 exactly.

2. Tensor/order. The tensor order D_r differs from the integral closure by a
   nonnegative length; the normalized log-volume loss is
   `delta_r=(r-1)(e-1)/(2e)>=0`. It is subtracted from h_C, so its
   contribution to E_extra is `-delta_r<=0`. It cannot be positive.

3. Ind1 permutations. Full Ind1 is the procession automorphism group, not
   finite label translation. Pure factor permutations change the tuple/min
   threshold; the conditional permutation hull is bounded by the original
   average and does not add positive normalized volume. Target saturation
   of the full orbit is TC-B, which is missing; assuming it would be a new
   target-containment hypothesis, not a source-derived term.

4. Ind2/Ind3. Ind2 Ism/order-2 preserves the integer lattice; it can move the
   target hull branch but no positive normalized volume is proved. Ind3
   log-link indeterminacy is upper semi-compatible and does not add positive
   volume beyond the allowed branch; the second log-link on the same path is
   empty. Both contributions are 0 or conditional, not positive actual.

5. Row/Theta weights. The source weights are `rho_p^{j+1}` with
   `0<=rho_p<=1` in the uniform profile; in particular rho=1 is already the
   maximal weight and is included in C1. There is no free row/Theta weight
   >1 that could add +80.55; a larger weight would be arbitrary.

6. Other local types (wild/e!=ell). The absolute restricted-shell volume is
   `((n_exp-e)f/e)log p<=0`; larger f makes it more negative. The only
   nonnegative quantity is the normalization shift
   `Delta_shell=((n_exp-1)f/e)log p <= (f/(p-1))log p`, which is not an
   actual output-hull term and is not inserted into h_C by any source
   theorem. To cover b=3 one would need f>=122400, unconstructed/unbounded.

7. B=I b=3. The only finite negative-to-residual term is the conditional
   B=I b=3 surplus `S=(12/41)logp` (positive h relative to Q). It is
   branch-dependent: B=I is not actual under the natural trace alignment,
   is type-gapped at full source level, and has no constructed complete C.
   It is not an actual branch-independent contribution and cannot be used
   without the missing B/H_A-full/TC data.

8. Archimedean. h_inf is already in C1 and is bounded above by A; it cannot
   be increased beyond the paper-level container. A larger Green/radius term
   is a different normalization/auxiliary term, not source-derived.

No branch yields a positive actual `E_extra`; the theorem follows. QED.

Equivalently, for the actual C1 assembly,

    h_C <= sum_p alpha_p h_p + h_inf(C) + E_cond,             (2.1)

where `E_cond<=0` on the actual branches and the only positive case is the
conditional B=I b=3 term `S` (not actual, branch-dependent). Since the b=3
B=O_K residual after arch is `80.550577...`, no positive actual term of that
size exists.

## 3. Exact obstruction for the requested sizes

b=3 B=O_K: C1 gives `Q_C-h_C>=80.550577...`; a positive E would have to be
at least +80.55. The only positive finite candidate is B=I b=3 with
`S(12301)=2.7563226845`, and it would require at least 30 such places (or one
prime above `exp(41*80.55/12)`) with actual B=I/v/full barGamma/TC. This is
conditional and not a single source-derived term.

b=273: needs +8918 (B=O_K) or +8821.5 (B=I) after A; B=I b=273 is still
negative, and the only positive local term B=I b=3 is far smaller. Aggregate
B=I counts 3236/3201 etc are conditional and require arbitrary large distinct
primes; no construction.

Thus the exact non-positivity obstruction is quantitative:

    actual finite/global E_extra <=0;
    conditional B=I b=3 E_extra=+S(p) only;
    no branch-independent +80.55/+8808 term.

## 4. Why target saturation/Ind1 does not evade it

The phrase 'target saturation' could enlarge H_C to the hull of the full
union of possible images, which is monotone in volume. But this is exactly
TC-B/TC-C: it requires identifying the actual target union and its
normalized volume with h_C. The current source does not prove this; if one
enlarges the target arbitrarily, one changes the target object and no longer
proves P6. The conditional permutation bound is not a positive term beyond
C1; it is a bound on the hull already included in h_C.

Similarly, Ind1 automorphisms permute factors but do not create positive
volume; Ind2/Ind3 move branches, not volume; row/Theta weights <=1 are
already included.

## 5. Classification

PROVED (under C1/conditional local formulas):

- good finite E=0; tensor/order E<=0; Ind1/Ind2/Ind3 no positive actual E;
- row/Theta weights <=1 already in C1; other-local absolute shell <=0;
- arch h_inf<=A; B=O_K bad contributions positive-to-F (counterexample
  direction), not h_C positive;
- B=I b=3 is the only positive local E, conditional/type-gapped;
- no actual branch-independent E_extra of +80.55 or +8808.

CONDITIONAL:

- B=I actuality/v/full barGamma; TC-A..H/TC-S; target saturation;
- other-local Delta_shell; actual complete C; aggregate B=I.

IMPOSSIBLE as a source construction:

- a genuine positive finite/global contribution beyond C1 from good/tensor/
  Ind1-3/row-Theta/other-local data;
- using target saturation as a positive term without TC-B/TC-C;
- using arbitrary row/Theta weights >1 or arbitrary auxiliary cycles;
- branch-independent +80.55/+8808 from the current corpus.

OPEN/MISSING: complete C, H_A-full/B branch, TC, other local types, actual
archimedean data, fixed q class.

## 6. Conclusion

Short theorem: under the corrected C1 assembly, every actual source-derived
finite/global correction beyond C1 is zero or nonpositive; the only positive
finite term is the conditional B=I b=3 surplus, which is branch-dependent and
not actual. Hence no genuine positive contribution of +80.55 (b=3) or +8808
(b=273) exists in the current corpus. This is an exact non-positivity
obstruction, not a P6 proof and not an arbitrary enlargement of the target.

## 7. Status

Natural-language theorem/proof only. No arbitrary weights, no Lean/Project
edits. Only this file written. `target_accepted=false`; P6 open.
