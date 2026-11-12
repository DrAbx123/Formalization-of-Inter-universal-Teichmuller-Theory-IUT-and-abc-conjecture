# FACE5-WILD-NUMERICS — wild/arch per-place check (l=5)

Status: model-level numerical check using the A893/A892 Theta-data and hull volumes.
qpilot's SSINEQ-ANATOMY.md is still absent; this is not a compiled lana computation and not
a proof of SSIneq.

## 1. Per-place objects

For a bad finite place v = p:
    H_v := hullPacket_p (paper-normalized finite hull term, logMuPaper),
    T_v := (sF-1) * A_v,
where sF-1 = 1.5 for l=5 and A_v is the local share of
    A = absLogQ = logQ/(2l),  l=5 => A = logQ/10.
The archimedean term is
    H_inf = arch = 1.491303,   T_inf = 0.
The global target inequality is
    sum_v T_v <= sum_v H_v + H_inf.

For the example D with bad {2,11}, q=22, logQ=log22=3.091043, A=0.309104.
Take the proportional local split
    A_v = A * (ord_v(q) log p) / logQ,
with ord_2(q)=ord_11(q)=1.

## 2. Wild data (p=2, e=2, r=1, n=2)

    H_2 = (1 + [p=2] - 1/e - r/n) log2
        = (1 + 1 - 1/2 - 1/2) log2 = log2 = 0.693147.
    A_2 = 0.309104 * log2/log22 = 0.069315,
    T_2 = 1.5 * A_2 = 0.103972.

For comparison, the non-wild A893 p=2 data (e=1,n=4,r=1) has
    H_2(e=1) = (3/4)log2 = 0.519860,
so the wild term adds 0.173287 to H_2.

## 3. Per-place sign table

| place | H_v | T_v | H_v - T_v | sign |
|---|---:|---:|---:|---|
| p=2 wild (e=2,r=1,n=2) | 0.693147 | 0.103972 | +0.589175 | + |
| p=11 odd (1,1,0) | 0.000000 | 0.359684 | -0.359684 | - |
| arch | 1.491303 | 0 | +1.491303 | + |
| total | 2.184450 | 0.463656 | +1.720794 | + |

The odd p=11 place alone is negative: its local hull term is zero, while it must carry
0.359684 of the target. The negative place is covered by the p=2 wild term and especially
by the arch term. The global inequality holds with margin +1.720794.

## 4. Global inequality

    sum T_v = 0.463656,
    sum H_v + H_inf = 0.693147 + 0 + 1.491303 = 2.184450,
    margin = 2.184450 - 0.463656 = +1.720794 > 0.
So the example satisfies sum T_v <= sum H_v + H_inf.

If the requirement is allocated entirely to p=2 (allocation B of A910):
    T_2 = 0.463656, T_11 = 0,
    H_2 - T_2 = 0.229491, H_11 = 0, arch = +1.491303,
    total margin = 1.720794 (same global value).
If p=11 is charged with its proportional T_11=0.359684, its per-place sign is negative but
the global margin is unchanged.

## 5. Wild coverage gap

- Using the wild p=2 value H_2=log2 instead of the non-wild H_2=(3/4)log2 increases the
  global margin by exactly 0.25 log2 = 0.173287.
- Excluding the wild term (using only e=1 data) would give margin
  2.011163 - 0.463656 = 1.547507, still positive.
- Excluding the arch term would leave
  0.693147 + 0 - 0.463656 = +0.229491; still positive but tight.
- Thus in this example the wild coverage is not the binding item; the arch term dominates
  (1.491303), and the p=11 finite place is negative (-0.359684) but globally covered.

## 6. Verdict

- Wild (p=2, e=2) example: H_2=0.693147, T_2=0.103972, local sign +.
- Odd p=11: H_11=0, T_11=0.359684, local sign -.
- Arch: H_inf=1.491303, sign +.
- Global: sum T = 0.463656 <= sum H + H_inf = 2.184450; margin +1.720794.
- The wild term contributes +0.173287 relative to the non-wild e=1 model; the arch term is
  the dominant positive contribution. No wild-coverage deficit appears in this example;
  the only negative place is p=11, covered globally.

Caveat: qpilot's SSINEQ-ANATOMY.md and a compiled explicit D are still absent; the
allocation A_v is a model choice (proportional or all-to-p=2), and the numbers use the
A893/A892 data. Not a Lean/lana theorem.
