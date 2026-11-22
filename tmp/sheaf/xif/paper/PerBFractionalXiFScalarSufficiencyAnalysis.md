# Per-b fractional tensor route: sufficiency for the xi-f scalar

Question: is the per-b fractional tensor route already enough for the xi-f
scalar, and are LGP/Kummer/Ind structures unnecessary?

Answer for the scalar target: **yes, if the direct per-b construction is
completed and its normalized log-volume is identified with the paper scalar.**
The LGP/Kummer/Ind machinery is not needed to define or compare the scalar
itself.  It is still needed for the full Theorem 3.11 multiradial representation,
but not for the numerical xi-f scalar if that scalar is constructed directly
from the actual q_v data and Haar/tensor structure.

## 1. Minimal scalar ingredients

The xi-f target only needs:

1. the finite actual bad-place set
   Bad (nativePlaceSelection T),
   with its actual Fintype from NativeBadFintypeClosed;

2. for each b, the actual q_v
   qVFamily T b : FinitePlaceQCandidate ((nativeBadLift T).lift b);

3. per factor, the actual completion
   CommonPrimeCompletion ((nativeBadLift T).lift b)
   and the actual integral/unit log-shell;

4. the tensor factor over all b:

   B_T = tensor over b of CommonPrimeCompletion (lift b),

   with the actual additive Haar measure;

5. an actual tensor unit region O and an actual nonzero scalar lambda
   chosen from the q_v data;

6. the actual lambda-O region lambda * O and its relative Haar log-volume

   log Haar(lambda * O) - log Haar(O);

7. the actual theta values q_v^(j^2) and the signed-label procession average;

8. the actual q-pilot scalar -log q, or its normalized q-family scalar.

No global IQ-to-C3 transport, no full multiradial representation, and no
line-bundle/theta-function identification is required for these scalar pieces.

## 2. Why LGP/Kummer/Ind are not necessary for the scalar

The scalar is a function of:

- the actual q_v values;
- the actual tensor completion structure;
- the actual Haar measure;
- the explicit lambda from q_v;
- the finite signed-label weights.

None of these depends definitionally on:

- the LGP splitting monoid action;
- the Kummer isomorphisms of tensor packets;
- the Ind1 procession action;
- the Ind2 per-summand Ism action;
- the Ind3 log-Kummer upper-semi correspondence.

Those structures are needed in the paper to prove that the multiradial
representation is well-defined up to indeterminacies and to identify the
paper's global scalar with the constructed one.  They are not needed to compute
a per-b tensor Haar ratio or to state the resulting scalar comparison.

## 3. What the per-b route must still prove

The route is sufficient only after these actual claims are proved:

1. O and lambda*O are actual subsets of the same finite-dimensional tensor
   block and O has positive finite Haar measure.

2. The actual theta-image points lie in the actual lambda*O hull; otherwise
   the hull scalar is not the theta-hull scalar.

3. The actual Haar scaling law gives the exact ratio

   Haar(lambda*O) / Haar(O)

   and the log is finite, positive, and nonzero for lambda nonunit.

4. The finite signed-label procession average is the actual normalized
   mono-analytic log-volume; this is a normalization equality, not an
   indeterminacy action.

5. The scalar comparison is exactly the xi-f scalar comparison, not a
   different q = 1/5 substitution or a finite concrete C3 model.

If (2) or (4) is not proved, the per-b object is a valid actual tensor/log
object but not yet the paper xi-f scalar.  The exact gap is then the image/hull
landing or the normalization equality, not LGP/Kummer/Ind compatibility.

## 4. What is unnecessary on the critical path

Do not build, for the scalar target:

- GlobalIQAmbient -> C3LogShellTensorBlock value-level transport;
- LGP monoid actions/poly-isomorphisms;
- Kummer correspondence squares;
- Ind1/Ind2/Ind3 quotient/action data;
- source theta function/line bundle identification;
- global Theta-pilot arithmetic divisor (unless needed for a separate semantic
  comparison).

Keep those as separately audited objects for the full Theorem 3.11 target.
Do not add them as prerequisites for the per-b scalar inequality.

## 5. Remaining non-scalar obligations

The following remain genuine for the full paper-level object but are not
scalar prerequisites:

- the global multiradial representation;
- the LGP/Kummer/Ind compatibility;
- the source theta line bundle/function and its divisor identification;
- the global Theta-pilot arithmetic divisor and Theta-link relation.

They should not be conflated with the xi-f scalar proof.

## 6. Decision

Use the per-b fractional tensor route as the minimal xi-f scalar layer.
Do not continue constructing unnecessary GlobalIQ->C3, LGP, Kummer, or Ind
compatibility for this scalar.  The only required next actual steps are:

1. actual per-b tensor unit region and lambda from qVFamily;
2. actual theta-image inclusion in lambda*O;
3. actual Haar scaling ratio and nonzero log;
4. actual procession normalization/average;
5. actual q-pilot scalar and the exact scalar comparison.

No fake inequality, no fake carrier comparison, and no unnecessary
compatibility is asserted by this decision.
