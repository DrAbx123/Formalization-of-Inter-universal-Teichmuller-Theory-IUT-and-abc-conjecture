# S852: p_v semantics in IUT III

Source text: `tmp/sheaf/n8/closure/sources/IUT-III.txt` (IUT III).

## Conclusion

`p_v` is the local uniformizer of the p_v-adic field K_v, i.e. `p_v = pi_v` with
`ord_v(p_v) = 1`. It is NOT the rational prime p.

Therefore for the local q-pilot:

```text
log(q_v) = ord_v(q_v) * log(p_v)
```

has no ramification exponent e: `ord_v` is the p_v-adic valuation normalized on the
local uniformizer, not the rational-prime valuation.

Paper qPilot local coefficient = `ord_v(q_v)`, equal to the Lean `order` of the
qVFamily completion candidate, not `order / e`.

## Direct textual evidence

1. IUT III, Remark 2.4.2(ii), lines 5042-5055:

```text
For v in V lying over ... and vQ in VQ^def = V(Q), write
  r_v = [(F_mod)_v : Q_vQ] * log(p_v) in R   if v in V_good,
  r_v = [(F_mod)_v : Q_vQ] * ord_v(q_v) * log(p_v) in R   if v in V_bad
- where, if v in V_bad, the notation ord_v : K_v^times -> Q denotes the natural
  p_v-adic valuation normalized so that ord_v(p_v) = 1, and q_v is as in
  [IUTchI], Example 3.2, (iv).
```

The clause `normalized so that ord_v(p_v) = 1` is exactly the local-uniformizer
normalization. If p_v were the rational prime p, then ord_v(p) would be e(K_v/Qp),
not 1 in general, contradicting the displayed normalization.

2. IUT III, Remark 3.9.1(iv), lines 7352-7357:

```text
maps N ni 1 |-> -log(q) in R
[where we write log(q) = ord_v(q_v) * log(p_v) in R -- cf. the notation of
Remark 2.4.2, (ii)].
```

Again `ord_v` is the p_v-adic valuation of item 1, so `log(p_v)` is the local
uniformizer log, not `log(p)`.

3. IUT III, Proposition 3.2 and its packet-normalization, lines 6744-6746:

```text
these log-volumes are normalized so that multiplication of an element of M(-)
by p_v corresponds to adding the quantity -log(p_v) in R; we shall refer to this
normalization as the packet-normalization.
```

Multiplication by the local uniformizer p_v acts by -log(p_v); this is the local
p_v-adic normalization, not rational-prime scaling.

## What is not concluded

- This does not assert e(K_v/Qp) = 1; it says the local q-pilot coefficient uses
  the p_v-adic order, hence there is no e denominator in the paper order formula.
- S840's separate ramification-exponent no-go is unaffected.
- The global weights 1/[K_v:(F_mod)_v] in IUT III lines 5326-5348 are degree
  normalizations, not the local ramification exponent.

## Lean consequence

Lean `FinitePlaceQCandidate.order` (the exponent of the completion element) matches
the paper coefficient `ord_v(q_v)` directly. Do not introduce `order / e` or require
`paperRamificationExponent = 1` for this local order identification.
