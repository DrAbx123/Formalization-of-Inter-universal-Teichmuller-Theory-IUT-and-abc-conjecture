# FACE5-PER-PLACE-TARGETS — l=5, p=2,11 (A910)

Status: model-level per-place decomposition using lana source formulas
(`Iut/WallEquiv/VcI.lean`), not an IUT theorem, not Lean evidence.

## 1. Sources

- `hullPacket` def: VcI.lean:689;
- `hullPacket_finite`: VcI.lean:806:
    hullPacket i (finite p) = sum_c w_c * sum_j logShellRadius(finPart) * log p;
- `hullPacket_tame`: VcI.lean:844:
    hullPacket i (finite p) = sum_c w_c * sum_j (1 - 1/e_cj) * log p (tame);
- `logVol_hull_vcI_eq`: VcI.lean:741:
    V = logVol(hull(vcI)) = (1/nC) * sum_i finsum_v hullPacket i v;
- `logVol_lgp_integral`: IdentifiedCopies.lean:444:
    logVol(LGP.O) = -sFactor(nC) * absLogQ.

## 2. l=5 data

- nC = (l-1)/2 = 2 capsules;
- sFactor(2) = (sum_{j=1}^2 j^2)/2 = 5/2; sF - 1 = 3/2;
- A = absLogQ = |log q|/(2l) = |log q|/10;
- per-place A_p = ord_p(q) * log p / 10  (sum_p A_p = A for q supported on bad p).

## 3. Exact decomposition

From VcI.lean:741:
    V = (1/nC) * sum_i sum_p hullPacket i p + (1/nC) * sum_i hullPacket i infinity.
Hence, with sum_p A_p = A:
    V - (sF-1)A
      = (1/nC) * sum_i [ sum_p ( hullPacket i p - (sF-1) A_p ) + hullPacket i infinity ].

This is exact (finite support from `finite_support_hullPacket`); the infinity term
is the arch packet (`hullPacket ... .infinite`), and has no A_infinity subtraction.

## 4. Numeric model table (ord_p(q)=1, l=5)

| p | A_p | (sF-1)A_p | hullPacket_p model | hullPacket_p-(sF-1)A_p |
|---|---:|---:|---:|---:|
| 2 | log2/10 = 0.06931 | 0.10397 | log2 = 0.69315 (p=2, e=2,r=1,n=2 model) | 0.58918 |
| 11 | log11/10 = 0.23979 | 0.35968 | 0 (tame e=1) | -0.35968 |

Arch packet: `hullPacket infinity` is the `.infinite` component; its model value is
`(1/nC) sum_i hullPacket_i(infinity)` and is bounded by |I| log(sqrt2*pi) in the
paper normalization (see FACE2-VERDICT2); sign depends on actual arch data.

## 5. Conclusions

- Per-place target is exact: `hullPacket_p - (sF-1)A_p` for finite p, plus
  `hullPacket_infinity` for the arch place; averaging over i and dividing by nC.
- At tame p=11 with e=1, hullPacket_p = 0, so the p=11 contribution is negative
  (-(sF-1)A_11); at wild p=2 with the model e=2,r=1,n=2, hullPacket_2 = log2 and
  the contribution is positive.
- The accumulated sign is NOT determined without actual ramification data/arch;
  this is the per-place target for the Face5 section construction.
