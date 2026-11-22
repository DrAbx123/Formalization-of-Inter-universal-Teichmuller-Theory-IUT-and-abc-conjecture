# RETRACTION: LANA eta domain correction was wrong

Date: 2026-10-25. Status: C1 OPEN.

## 0. What happened

C9-C1-DOMAIN-CORRECTION-20261025.md claimed LANA 9.2 says
  'Once we fix S subset VC(I_v) ...'
and concluded that the small/large container mismatch was a misreading.

This is WRONG. The LANA TeX source says exactly:

  'Once we fix $S \\subset \\VC(\\LS_{\\uv})$, this provides an isomorphism ...'
  'R^{ss} = {T \\subset \\VC(\\cI_{\\uv}) | adelic and measurable}/~'

So:
  eta^anab_S domain:     S subset VC(LS_uv)   (small / log-shell container)
  Rss / target pilot:    T subset VC(I_uv)    (large container)
  q-pilot target pilot:  {q_v O_v} embedded diagonally in VC(I_uv).

The PDF text extraction had dropped the 'LS' subscript; the TeX source
restores it. The correction conflated domain and target.

## 1. Retraction

C9-C1-DOMAIN-CORRECTION-20261025.md is RETRACTED.
The prior container-mismatch verdicts (task-436, 438, 439, 446, 447, 448, 450)
stand. S_q is a large-container pilot class, not an admissible S in VC(LS).

## 2. Consequence

- S_q route: DEAD (container mismatch).
- volume-scaling with S in VC(I): S is outside eta^anab domain.
- log-shell S_q^LS: no source-defined object in VC(LS).
- C1: OPEN.

No source misquote is adopted. No Lean. target_accepted=false.