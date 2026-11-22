# C9 adversarial review of the C1 domain correction and repaired route

Task ID: task-455 / C9-C1-DOM-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-C1-DOMAIN-CORRECTION-20261025.md (68 lines).
Scope: independent adversarial review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the domain correction. It misquotes LANA 9.2.** The source text says

    Once we fix S subset VC(LS_uv), this provides an isomorphism ...        (0.1)

where `VC(LS_uv)` is the log-shell/small volume container; the target is

    Rss = {T subset VC(I_uv) | adelic and measurable}/~,                  (0.2)

the large container. The correction replaces (0.1) by 'S subset VC(I_v)' and declares the earlier container-mismatch rejection false. That is a source-reading error, not a correction. The original small/large distinction stands, and the repaired route is invalid at the domain level.

C1 remains open. Prior container-mismatch verdicts are **not** retracted.

## 1. Source accuracy: REJECT

Exact LANA 9.2 text in C9-STRICT-DEFICIT-LANA-SNAPSHOT-20261024.tex (around the main-goal subsection) reads:

    'Once we fix S subset VC(LS_uv), this provides an isomorphism ...'
    'Rss = {T subset VC(I_uv) | adelic and measurable}/~'
    'we define M=1·S ... put the class of M in Rss to be the pilot.'

The correction's quote 'Once we fix S subset VC(I_v)' and its claim 'The correct domain is the LARGE container VC(I_v)' are **not** the source statement. The source's `S` is a subset of `VC(LS_uv)`, not `VC(I_uv)`. The target `Rss` and the q-pilot target pilot are in the large container `VC(I_uv)`; that does not make the domain of eta^anab_S large.

Therefore §0/§4 of the correction are wrong: there was no misreading in the earlier audits. The container mismatch is real: eta^anab_S takes S in the small log-shell container; the q-pilot target class is in the large container.

## 2. Repaired volume-scaling route: REJECT

The repaired route chooses S in `VC(I)` (large) and applies the LGP action `T_1: VC(I)->VC(I)`. But eta^anab_S is defined for `S subset VC(LS)` (small). A large-container S is not a valid input for eta^anab_S. Volume scaling in the large container cannot repair a domain mismatch: it constructs a large S, while the anabelian construction requires a small S.

The route's step `[] T_1(S) has class [S_q]` is irrelevant if S is not in the domain of eta^anab. No bridge from the large S to the small-container integral structure is supplied.

## 3. Alternative LGP-inverse construction: REJECT/conditional

§3 says: if LGP is invertible on VC(I) (as an ambient K-vector space) and `S = LGP^{-1} S_q` lies in VC(I) and is admissible, then `1·S=S_q` exactly.

Problems:

1. **No source theorem of invertibility.** LANA constructs an action of N/LGP on the large volume container; it does not assert that LGP is an invertible linear map on the ambient K-vector space, nor that its inverse preserves the log-shell container.
2. **Wrong container again.** `S=LGP^{-1}S_q` is in the large container (if defined), not in `VC(LS)`. It is not an admissible S for eta^anab.
3. **Admissibility unproved.** Even if S is in VC(I), it is not shown measurable/N-stable/integral for the anabelian construction.
4. **`1·S=S_q` exact** would be a strong compatibility, but its hypothesis already assumes the action is defined/invertible on the q-pilot region; that is precisely part of the missing LGP domain theory.

Thus the alternative does not avoid the domain problem; it relocates it.

## 4. LGP invertibility: REJECT as unproved

The correction treats `1 in N` as acting by LGP multiplication on the large container. LANA says an action of N on `VC(I_uv)` is constructed anabelianly, subject to Ind1/Ind2; it does not state that this action is a bijection/invertible linear map or that it has a well-defined inverse on the q-pilot region. APT/Ind3 again warn against treating it as a set-theoretic invertible transport. No source theorem supports the invertibility hypothesis.

## 5. Admissibility: REJECT

Whether S is in the large or small container, the correction does not prove:

- S is adelic measurable;
- S is N-stable/compatible with the LGP action;
- S is an integral structure in the domain of the anabelian construction;
- S has finite positive volume/nonzero pilot class.

These are unchanged gaps, not removed by the domain correction.

## 6. Output bridge: REJECT; still C1

Even if eta_q=eta^anab_S held, the correction's own D4 asks whether eta equality gives an actual output D0 with logVol(D0)=Q. This bridge is C1; no proof is supplied. The correction only restates it as D4.

## 7. What the correction actually establishes

Only that the q-pilot target pilot is a class in the large container (true). It does not establish that the eta^anab domain is large. The repaired route therefore inherits all previous failures plus a new source misquote.

## 8. Accept/reject table

| item | verdict | exact reason |
|---|---|---|
| domain correction 'S subset VC(I)' | REJECT | LANA says S subset VC(LS_uv); misquote |
| retraction of container-mismatch verdicts | REJECT | based on false quote; mismatch real |
| repaired volume-scaling in VC(I) | REJECT | S not in eta^anab domain |
| LGP invertibility/alternative | REJECT/CONDITIONAL | no source invertibility; S still large; admissibility unproved |
| admissibility | REJECT | measurable/N-stable/integral/domain unproved |
| output bridge | REJECT | C1 itself; no D0 construction |

## 9. Final review verdict

**REJECT the domain correction and the repaired route.** The correction misquotes LANA 9.2: the eta^anab domain is `S subset VC(LS)`, the log-shell container, while the target `Rss`/q-pilot class is in `VC(I)`. The small/large mismatch was correct and is not retracted. LGP invertibility, admissibility, and the output bridge remain unproved; C1 remains open.

No Lean; no mixed/E3; no source misquote adopted.

target_accepted=false.
