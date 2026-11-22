# S2774 — 196a1 local Frobenius data audit (Sage)

Date: 2026-11-07. Data/audit; NO fake matrices, NO global image claim.

## 1. Sage runtime and job status

WSL Sage command:

```text
wsl -d Ubuntu-24.04 -- /opt/miniconda/envs/sage/bin/sage
Sage version 10.9
```

### /tmp/extract196b.out

Content: only `curve ok` (9 bytes).  The division_field(5) call did not finish;
process exited without printing a degree.  (Earlier /tmp/extract196.out has a
PARI stack overflow at 1GB during `splitting_field`/`polredbest`.)

### /tmp/extract196c.py

Runs `E.division_field(5, simplify=False)` and saves K/basis; it is still
running (PID 1162, ~2 min CPU).  No K196_5.sobj or B196_5.sobj yet.

So: global division-field basis is NOT YET extracted; no global matrices.

## 2. Local finite-field extraction (completed)

Script: `/tmp/local196.py` (Sage, finite fields).

For each auxiliary good p, k with 5 | p^k-1, it computes E(F_{p^k}), a
torsion_basis(5), then the p-power Frobenius matrices in that basis.

Output: `/tmp/local_matrices.jsonl`, 14 exact records:

```json
{"p": 3, "k": 4, "card": 75, "M": [[3, 4], [0, 1]]}
{"p": 17, "k": 4, "card": 83475, "M": [[3, 4], [0, 4]]}
{"p": 43, "k": 4, "card": 3417600, "M": [[2, 1], [0, 4]]}
{"p": 67, "k": 4, "card": 20152875, "M": [[1, 4], [0, 2]]}
{"p": 71, "k": 4, "card": 25401600, "M": [[1, 3], [1, 4]]}
{"p": 73, "k": 4, "card": 28387875, "M": [[4, 3], [0, 2]]}
{"p": 89, "k": 2, "card": 7875, "M": [[4, 3], [0, 1]]}
{"p": 89, "k": 4, "card": 62755875, "M": [[4, 4], [0, 1]]}
{"p": 101, "k": 4, "card": 104080275, "M": [[1, 3], [1, 4]]}
{"p": 103, "k": 4, "card": 112564875, "M": [[3, 2], [0, 1]]}
{"p": 113, "k": 4, "card": 163036800, "M": [[4, 1], [0, 2]]}
{"p": 127, "k": 4, "card": 260140800, "M": [[2, 2], [0, 1]]}
{"p": 139, "k": 2, "card": 19200, "M": [[1, 2], [0, 4]]}
{"p": 139, "k": 4, "card": 373324800, "M": [[2, 4], [3, 3]]}
```

Matrix convention in `local196.py`: columns are Frobenius images of the two
basis points P,Q, i.e. M = [[a,c],[b,d]] where Fr(P)=aP+bQ, Fr(Q)=cP+dQ.

## 3. Numerical checks (raw JSON only)

- All 14 matrices have determinant p mod 5; det values observed
  {1,2,3,4}.
- If the 14 matrices are naively multiplied as if in ONE basis, the generated
  subgroup has order 480 = #GL2(F5), and the determinant-1 subgroup has order
  120 = #SL2(F5).
- BUT this is NOT a valid global image computation: each local matrix is in a
  DIFFERENT finite-field torsion basis.  The raw matrices cannot be combined
  into a common basis.

## 4. Exact remaining gap

```text
GAP: no common-basis E[5] basis and no global Frobenius matrices for 196a1.
```

To get them:

1. finish division field K = Q(E[5]) (extract196c, simplify=False);
2. choose a single basis P,Q of E(K)[5] (Sage torsion_basis(5));
3. for each good rational ell, choose a prime ideal above ell, compute
   frobenius(P), frobenius(Q), solve coordinates in (P,Q) mod 5;
4. only then the generated matrix group is meaningful for the global mod-5
   image.

The local finite-field matrices are useful as local checks, not as global
image data.  No SL2 containment claim is made.

## 5. Lean interface (unchanged)

`S196a1Curve`, `S196a1FiveBasis`, `S196a1_frobMatrix`,
`S196a1_SL2_le_range` remain empty until global data exists.  Do not fill
with local-basis matrices.
