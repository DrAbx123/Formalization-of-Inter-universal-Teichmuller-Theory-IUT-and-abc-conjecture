# IUT-TEXT-LOGQ — repository search for IUT q-pilot/log q text (A1036)

Status: read-only repository audit; no compile.  **No verbatim IUT III/IV original
text was found in the searched repository locations.**  The executable definitions
below are lana formalizations, not quotations from the paper.

## 1. Search result

| location | content | has IUT III/IV text? |
|---|---|---|
| `tmp/lit/` | `UDC.pdf(.txt)`, `Holonomy.pdf(.txt)`, `pasten2018.html`, ABC scripts, build logs | no (UDC/Holonomy are unrelated documents; no IUT III/IV text extraction) |
| `coord/` | derived notes/excerpts (`ALPHA-DERIVATION.md`, `QORDER-NORMALIZATION.md`, `AUDIT-IV-LIT-QSTABILITY.md`, `CHAIN3-SECTION-EXPERIMENT.md`, ...) | no verbatim text; they cite IUT locations/paraphrase |
| `.claude/worktrees/roadmap-2026-11-review-cddd5f/papers/` | PDFs: IUT formalization report, LANA report, Motizuki corpus raw PDFs | PDFs present, but **no extracted text**; not parsed in this audit |
| `Iut/` source | lana formalization (definitions/lemmas) | lana only, not the original |

Therefore: the paper's exact wording/section numbers cannot be quoted from tree;
only lana's formal definitions and coord notes are available.  External literature
is required for the verbatim statements (see §4).

## 2. lana formal definitions

### qOrder (raw integer order)
`Iut/Cor312/ThetaData/TateParameterAt.lean:108-114`:
`qOrderAt := ((tateParameterAt E hw).toOrdered (isUniformizer_unifAt w)).orderNat`
(positive Nat; raw `v_π(q)`, no reduction modulo ℓ/2ℓ).
`Iut/Cor312/ThetaData/Basic.lean:171-194`:
`qOrder := qOrderAt`, `qOrder_eq_orderNat`, `qOrder_pos`, `coprime_qOrder`.

### qroot (2ℓ-th root)
`Iut/Concrete/ThetaRegion.lean:16`: `qroot` = `2ℓ`-th roots of the Tate
parameters at the bad places of `K`.
`Iut/Concrete/ThetaLocalConstruct/Data.lean:327-330` `ordp_qrootOf`:
`ord_p(q_v) = qOrder_w / (2ℓ · ramIdx(F,w))`.
So the local root order already contains the `1/(2ℓ)` factor (and the
ramification index `e` in the local coordinate).

### logQ and absLogQ
`Iut/Cor312/LeftHandSide.lean:81-84`:
`logQ := ∑_{w ∈ badFinset} weight_w * (qOrder_w : ℝ) * Real.log (residueChar w)`
(`weight_w = [F_w : ℚ_p]/[F : ℚ]` from `InitialThetaData.qPilot`).
`:88`: `absLogQ := logQ / (2 * ℓ)`.
`:93`: `lhs := -absLogQ`.

So:
- paper-facing `A = |log q| = logQ/(2ℓ)`;
- no real-number `log` of a real q-value: `logQ` is the **arithmetic** weighted
  degree `∑ weight·qOrder·log p`;
- the factor `1/(2ℓ)` is applied once at `absLogQ`, not inside `qOrder`;
- `qroot`'s local ord has `1/(2ℓ)` and `1/e`; the global weighted `logQ` uses
  raw `qOrder` and sums over places with weights, which reproduces the same
  normalized degree (the `e` is absorbed by the weighted global degree).

## 3. Comparison with our C-line quantities

- Our `A = qPilot.absLogQ = logQ/(2ℓ)` matches lana (`LeftHandSide:88`).
- Our `T`/`qSide` uses `j²·A_v`, consistent with `ord(qroot^{j²}) =
  j²·qOrder/(2ℓ·e)`: after global weighted summation, the coefficient is
  `j²/(2ℓ)·qOrder·log p`;
- `coord/ALPHA-DERIVATION.md` and `coord/AUDIT-IV-LIT-QSTABILITY.md` record the
  same normalization; `coord/QORDER-NORMALIZATION.md` records that `qOrder` is
  the raw integer, not `mod 2ℓ`.
- We do **not** have an IUT text asserting a different convention; any claim
  that `A` avoids the `2ℓ` factor would contradict `LeftHandSide:88`.

## 4. External literature needed

Verbatim/authoritative sections still outside the repo:
1. **IUT I, Example 3.2(iv)** — q-parameters and the `2ℓ`-th root at bad places;
2. **IUT III, Theorem 3.11** — (Ind1), (Ind2), (Ind3) and the label sets;
3. **IUT III, Corollary 3.12** — definition of the q-pilot and `−|log Θ|`;
4. **IUT III, Remark 3.9.4** — log-shell/log-Kummer value-group entry;
5. **IUT IV, Theorem 1.10, proof Steps (iv)-(v)** — IUT IV's `−|log Θ|`
   normalization (the `1/(2ℓ)` and the label-`j` reading);
6. **IUT IV, Proposition 1.4** — log-volume scaling/indeterminacy bounds.

These are the sections a literature-based audit must cite; the repo cannot supply
their wording.

## 5. Conclusion

- Repository has **no verbatim IUT III/IV text** in `tmp/lit`/`coord`; only lana
  source + derivational coord notes.
- lana definition: `qOrder` raw integer; `logQ = Σ weight·qOrder·log p`;
  `absLogQ = logQ/(2ℓ)`; qroot local ord `= qOrder/(2ℓ·e)`.
- Paper normalization `A=|log q|` is implemented as `logQ/(2ℓ)`; this is the
  only executable convention in tree.
- Verbatim confirmation requires the external IUT sections listed in §4.

## 6. Update (A1037)

The IUT I-IV PDFs were subsequently found at
`papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory I-IV.pdf`
and extracted by `tools/pdftotext_iut.py` to `coord/IUT-TEXT/{I,II,III,IV}.txt`.
Verbatim excerpts are now in `coord/IUT-TEXT-COR312.md` and
`coord/IUT-TEXT-THM110.md`.

Confirmed verbatim from IUT IV p. 23:
`|log(q)| = 1/(2l)·log(q)` (the `1/(2ℓ)` normalization).
