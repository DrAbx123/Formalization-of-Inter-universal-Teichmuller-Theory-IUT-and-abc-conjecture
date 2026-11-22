# C9 arch S3 lower bound via the B=I region: independent attack

Task: task-287. Owner: qside. Date: 2026-10-25.
Stage: short natural-language theorem/proof and exact obstruction; no Lean/
Project edits; no arbitrary region, point, or r_v; only this file written.

## 0. Verdict

The B=I possible-image region and its fixed-gluing transport do **not** yield a
new lower bound h_inf >= -S3.  The B=I region is a finite bad-place lattice
family with normalized height

    H_B = (9/41) log 12301 = 9/41 S_3' (with S_3' = (4/3) S3? no:
    H_B = (9/41) log p, Q_p = -(3/41) log p,
    S3 = (12/41) log p, H_B + Q_p = S3),

but it carries no archimedean radial/angular data and no point-to-arch-hull
map.  Theta-gluing transports row packets in the finite/target packet
category; it does not construct an archimedean unit ball, global unit, or
global point inside H_C,inf.  The archimedean product formula remains a
pointwise identity for global points already known to lie in the hull.

Therefore the desired lower bound is **not proved**; the exact obstruction is
the absence of an archimedean component/point in the B=I region and the
absence of an actual archimedean hull.  The b=3 B=I corridor remains
conditional.  No new arbitrary region or radius is introduced.

## 1. Inputs

| file | SHA256 | role |
|---|---|---|
| C9-BI-REGION-CONSTRUCTION-20261025.md | 3726F7300CD099E4DA97F9FB0C5B810DF11F9A7BF62E8ED48BAC5A987CA53655 | explicit B=I row lattices/transport |
| C9-B3-P6-ASSEMBLY-20261025.md | A674FD983F1CBEA7B5293559A37CC4CD613BA4DE8EBCFEA4822CEE7A2C55E4A1 | conditional b=3 P6 theorem |
| C9-BI-REGION-HULL-20261025.md | 66F7871676321F8E15C5F6D24F013A85BC9AFEE138FCEF9FA8C2E02B7E8B6B76 | R_B subset H_C conditional |
| C9-ARCH-LOWER-NEW-20261025.md | DD98B2E25F071A580A574D502A25779CC6D6D77A464A9A09610E7B95E414A2B7 | prior arch lower obstruction |

Conventions: B_I-zero normalization; p=12301; e=41; b=3; S3=(12/41)logp;
H_B=(9/41)logp; Q_p=-(3/41)logp; F=Q_p-h_C; P6 is h_C>=Q_p.

## 2. What the B=I region actually is

From task-274/task-272, for j=1,...,20:

    s_j = floor(3 j^2 / 41),  r=j+1,
    L_B,j = p^{s_j-r+1} J^{tensor r},  R_B,j = Hull(L_B,j),
    nu(R_B,j)/log p = -s_j + j - (j+1)/41,
    H_B = (1/20) sum_j nu(R_B,j) = (9/41) log p.

Let T be the fixed-gluing common terminal packet transport, and

    R_B = union_j T(R_B,j).

Under the conditional B=I branch and TC-B target saturation:

    R_B subset H_C  =>  h_C >= H_B + h_inf.                    (2.1)

This is a lower bound for h_C, not for h_inf.  It gives

    F = Q_p - h_C <= -S3 - h_inf.                              (2.2)

So P6 follows from (2.1) iff h_inf >= -S3.  The B=I region supplies the
finite term H_B; it does not supply the arch term.

## 3. Conditional arch theorem (valid but hypothesis missing)

Theorem 3.1.  If the actual archimedean hull H_C,inf contains, or contains the
archimedean image of, one of:

(a) the unit ball B_I;
(b) a global unit u of F;
(c) a global point x with sum_p alpha_p v_p(x) log p <= S3,

then h_inf >= -S3.

Proof.  This is the same as task-278 Theorem 1: (a) monotonicity from
logvol(B_I)=0; (b) product formula with v_p(u)=0; (c) product formula with
finite valuation sum <=S3.  QED.

The new angle would be to produce (a)/(b)/(c) from the B=I region rather than
from an arbitrary point.  The B=I region construction gives no such object.

## 4. Attempt: transport B=I to an archimedean unit ball

One might hope that the fixed-gluing transport T, being volume-preserving on
the row packets, sends the B=I integral lattice J^{tensor r} to an
archimedean B_I unit ball.

Why this fails:

- T is a transport of finite/target row packets preserving q/BPS/row labels and
  normalization (task-274 §3); its construction does not include an
  archimedean component map to H_C,inf.
- A volume-preserving transport does not preserve radial radius or angular
  region.  h_inf is a log of radial radius plus a log angular volume, not the
  finite normalized height H_B.
- The B=I row lattice L_B,j is a p-adic fractional lattice at the bad place;
  its tensor factors are finite local fields, not archimedean tensor packet
  factors.
- Even if T mapped a set of normalized volume H_B into the archimedean target,
  a lower bound on h_inf would require a radial/angular containment, not just
  volume equality.  The IV container gives only an upper bound in the opposite
  direction.
- The source theorem "R_B subset H_C" is conditional on TC-B and actual B=I;
  it is a finite/target inclusion, not an archimedean inclusion.

Thus the transport route does not produce B_I subset H_C,inf.

## 5. Attempt: global point from the B=I lattice

L_B,j = p^{s_j-r+1} J^{tensor r} is a full Z_p-lattice.  It contains p-adic
points, but not automatically a global element of F or a point of the
archimedean tensor packet:

- the lattice lives in (K_v)^{tensor r} at the bad place, not in F;
- the theta-gluing T is a packet transport, not a map from F to H_C,inf;
- no global unit/point of F is identified with a point of L_B,j;
- even if a p-adic point were selected, the archimedean product formula does
  not apply to a local p-adic point.

Choosing a lattice vector and calling it a global point would be arbitrary.
The B=I region gives no canonical global point.

## 6. Attempt: product formula over the B=I region

Product formula is pointwise:

    sum_v alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0,   x in F^times.

It cannot be integrated over a region without a measure-theoretic identity; no
such identity is supplied.  A region lower bound for h_inf is not obtained by
applying a pointwise formula to an arbitrary lattice or hull.  The B=I region
has no distinguished point in H_C,inf, so the product formula gives no lower
bound for h_inf.

## 7. Exact obstruction

Theorem 7.1.  The frozen source does not provide any of:

(i) an archimedean component of R_B inside H_C,inf;
(ii) B_I subset H_C,inf;
(iii) a global unit/global point of F in H_C,inf with finite valuation
     sum <=S3;
(iv) a direct lower bound h_inf>=-S3 from R_B/T/Theta-gluing.

Proof.  The B=I construction is a finite bad-place lattice family plus a
finite/target packet transport; its row height H_B is finite local data and
its inclusion R_B subset H_C is a conditional finite/target TC-B statement.
It contains no archimedean radial/angular coordinates.  The archimedean hull
H_C,inf is not constructed (task-232).  T is not an archimedean
point/ball transport, and no global point of F is mapped into H_C,inf.  The
product formula needs a point already in the hull.  IV gives only the upper
container.  Hence (i)-(iv) fail.  QED.

Corollary 7.2.  The b=3 B=I P6 implication remains conditional on
H1-H4 of task-280; in particular h_inf>=-S3 is still missing.  The corridor is
neither closed nor realized.  No counterexample and no unconditional P6
follow.

## 8. Conclusion

The B=I region is genuinely useful on the finite side: it gives the explicit
lower bound h_C >= H_B + h_inf with H_B=(9/41)log p, hence F <= -S3 - h_inf.
But it does not touch the archimedean radial/angular term.  Theta-gluing is a
finite/target row transport, not a construction of B_I, a global unit, or a
global point in H_C,inf.  Therefore the new B=I-region attack does not prove
h_inf>=-S3; the exact obstruction is the absence of an archimedean component
and point map.  No arbitrary r_v or global point was chosen.

target_accepted=false; P6 remains open/conditional.

## 9. Sources

- C9-BI-REGION-CONSTRUCTION-20261025.md: explicit R_B,j, H_B, fixed T.
- C9-BI-REGION-HULL-20261025.md: conditional R_B subset H_C and exact
  obstruction.
- C9-B3-P6-ASSEMBLY-20261025.md: conditional b=3 P6 theorem H1-H4.
- C9-ARCH-LOWER-NEW-20261025.md / C9-ARCH-LOWER-S3-20261025.md: arch lower
  obstruction, B_I-zero/IV directions, product formula is pointwise.
- C9-ARCH-ACTUAL-RINF-20261025.md: actual archimedean hull/r_v missing.
