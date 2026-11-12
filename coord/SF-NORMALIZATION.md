# SF-NORMALIZATION — lana sF vs paper Cor 3.12 / Thm 1.10 (A1118)

Status: source comparison; no compile.

## 1. lana definitions

- nC D := (D.ell - 1) / 2  (Iut/Wall/Rss.lean:303; same as lEll*).
- sFactor n := (sum_{j in range n} (j+1)^2) / n  (Iut/Wall/Pilots.lean:55).
- sFactor_eq (Pilots:67): sFactor n = (n+1)(2n+1)/6 for n>0.
- gap_eq_rhs_add (Gap:523):
  gap = rhs + sFactor(nC) * qPilot.absLogQ - logVol(hull(vcI)).
- absLogQ := qPilot.logQ / (2 * ell)  (Iut/Cor312/LeftHandSide.lean:88).

Therefore, with n = nC = (ell-1)/2:

  sFactor(nC) = (nC+1)(2nC+1)/6
              = ((ell+1)/2 * ell)/6
              = ell(ell+1)/12.

This is the average of j^2 over the capsule labels j=1,...,nC.

## 2. Paper Cor 3.12 / Thm 1.10

Extract coord/IUT-TEXT-THM110.md:
- p.23, normalization: |log(q)| = (1/(2l)) * log(q).
- Step (v), before averaging:
    (j+1)log(d^K) - j^2/(2l) log(q_{vQ}) + ...
  (THM110 text line 111).
- Average over j in {1,...,l* = (l-1)/2}:
    -(2l*+1)(l*+1)/(12l) log(q_{vQ})
  (line 116),
  which equals
    -(l+1)/24 log(q_{vQ})   (line 118).

The extracted Cor 3.12 text (coord/IUT-TEXT-COR312.md) says -|log(Theta)|
is the procession-normalized log-volume where the average is over j in F_l^*,
and does not spell out a separate 1/(2l) for Theta. The explicit 1/(2l) is
stated in IUT IV Thm 1.10 p.23 for |log(q)|.

## 3. Coefficient table

| quantity | lana | paper | match |
|---|---|---|---|
| ell* / nC | (ell-1)/2 | l* = (ell-1)/2 | yes |
| average of j^2 | (1/nC) sum_{j=1}^{nC} j^2 | (1/l*) sum_{j=1}^{l*} j^2 | yes |
| sF | ell(ell+1)/12 | (l*+1)(2l*+1)/6 = ell(ell+1)/12 | yes |
| |log q| | logQ/(2 ell) | (1/(2l)) log(q) | yes |
| sF * |log q| | ell(ell+1)/12 * logQ/(2ell) = (ell+1)/24 logQ | -(ell+1)/24 log(q) (sign in rhs) | yes |
| pre-average q term | -j^2/(2ell) log(q) per capsule | -j^2/(2l) log(q) | yes |

Note the sign: in Gap gap_eq_rhs_add the sF term is +sF*absLogQ, while the
paper's upper-bound q term is negative inside rhs; the sign of gap is fixed by
gap = rhs + sF*A - V.

## 4. Is sF = (1/(ell^2-1)) sum j^2?

No.

Compute the alternative over all nonzero residues:

  (1/(ell^2-1)) sum_{j=1}^{ell-1} j^2
    = [ell(ell-1)(2ell-1)/6] / (ell^2-1)
    = ell(2ell-1) / (6(ell+1)).

Times |log q| = logQ/(2ell) gives

  (2ell-1)/(12(ell+1)) logQ,

which is NOT (ell+1)/24 logQ. So this normalization would change the paper
coefficient and is not the one used by lana.

Why the factor is not ell^2-1: F_l^* has ell-1 elements, but the pairs
+j and -j have the same j^2. The procession normalization is over the positive
half {1,...,l*}, each representing its +/- pair. Hence the average is
sum_{j=1}^{l*} j^2 / l*, not sum over all ell-1 elements divided by ell-1.

Equivalently, average over all F_l^* of j^2 equals the average over the positive
half:

  (2 sum_{j=1}^{l*} j^2)/(ell-1) = sum_{j=1}^{l*} j^2 / l*.

So lana's (1/nC) sum is exactly the F_l^*-average, not a different
normalization.

## 5. log Theta normalization

- In Cor 3.12, -|log(Theta)| is the procession-normalized log-volume of the
  holomorphic hull; the normalization is the j-average over F_l^*, with no
  separate 1/(2l) factor on Theta itself.
- In the extracted text, 1/(2l) appears only for |log(q)| (IUT IV Thm 1.10 p.23).
- The j-average is already the (1/l*) sum_{j=1}^{l*} j^2 in the q-term; after
  applying 1/(2l) to log(q), it produces (l+1)/24.
- No 1/(ell^2-1) normalization is present in the extracted Cor 3.12 or Thm 1.10
  passages.

## 6. Verdict

- lana sF = (1/nC) sum_{j=1}^{nC} j^2 = ell(ell+1)/12 is paper-faithful.
- With absLogQ = logQ/(2ell), sF * absLogQ = (ell+1)/24 logQ, matching
  THM110 lines 116/118.
- The alternative (1/(ell^2-1)) sum_{j=1}^{ell-1} j^2 is NOT the paper
  normalization and would give (2ell-1)/(12(ell+1)) logQ.
- No normalization correction to Gap.sFactor or absLogQ is needed on this
  point; the only care is the sign and whether the average is over the positive
  half (l*) or over all F_l^* with +/- pairs (they agree for j^2).
