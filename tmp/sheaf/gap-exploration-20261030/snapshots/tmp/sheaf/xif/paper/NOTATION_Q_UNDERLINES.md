# q-underline notation (authoritative quick note)

Machine underline extraction (annotated.txt / SYMBOL_SIGNIFIER_REGISTRY.md;
IUT I p.71, IUT III p.173) uses:

  q[1u] = q with ONE underline
  q[2u] = q with TWO underlines
  v[1u] = v with one underline

## IUT I Example 3.2(iv)

  q[1u] v[1u]   = the q-parameter q_v  (ONE underline under q)
  q[2u] / v[1u] = q[1u]^{1/2l} / v[1u]  (TWO underlines under q)

Thus:

* q-parameter:                q with ONE underline (q[1u]).
* 2l-th root q_v^(1/2l):      q with TWO underlines (q[2u]).
* Theta values:               powers of the DOUBLE-underlined q:
                              q[2u]^{j^2}, j=1,...,l*.

## Consequences

* qVFamily is the SINGLE-underlined q-parameter (q[1u]), not the paper root.
* Paper Theta values use q[2u]^{j^2}, with mu_{2l} indeterminacy.
* OCR loses underlines; do not confuse q[1u] with q[2u].
* If a Lean object is named `q` without underline information, record which
  one it is: q[1u] (q-parameter) or q[2u] (2l-th root).

## Corrected working extract
The q-passage in tmp/source-extract/iut1.txt was replaced with explicit
q[1u]/q[2u] markers. Original backup: tmp/source-extract/iut1.txt.orig.bak

## CRITICAL: the 2l normalization (do not lose this again)

Paper:

  q[1u] = q_v                  (single underline, q-parameter)
  q[2u] = q[1u]^(1/(2l))       (double underline, 2l-th root)

  Theta value at label j:
    q[2u]^(j^2) = q[1u]^(j^2/(2l))

Thus:

  log(q[2u]^(j^2)) = (j^2/(2l)) * log(q[1u])

and the q-pilot magnitude is:

  |log q[1u]| = 2l * |log q[2u]|

WARNING about current Lean code:

* `C3.q` is q[1u] (q-parameter), NOT q[2u].
* `realThetaValue q j := q^(j^2)` therefore treats q as q[2u].
* If q is q[1u], the correct Real magnitude is
    q^(j^2/(2l))
  i.e. `Real.rpow q ((j^2 : Real)/(2*l))` (or an actual q[2u] root).
* Omitting the 1/(2l) factor makes the signed theta average too large by
  factor 2l and produces false `q = 1/5` counterexamples.
* Completion 2l-th roots are impossible (S342); q[2u] must live in the
  extension/root-stack carrier, not in the completion.

Any theta packet/comparison using `realThetaValue q j` with q = q[1u] must
first fix this normalization. Do not prove the resulting false inequality.
## Existing normalization implementation (REUSE, do not rebuild)

* tmp/sheaf/xif/paper/BadPlacePaperConstantsActual.lean
  - paperRootCoefficient
  - s13ThetaCoefficient = j^2 * c_norm/(2l)
  - paperThetaCoefficient = qVFamPaperThetaTensorCoefficient
  - classicalThetaCoefficient_eq_twoL_mul_paper:
      classical q^(j^2) coefficient = (2l) * paper root theta coefficient
  - paperThetaValueRoot_is_root_power:
      qVFamPaperThetaValueRoot = root^(j^2)
* tmp/sheaf/xif/paper/BadPlaceHalfRootSupplyActual.lean
  - actual root r with r^(2l) = qVFamNormalizedGenerator.
* QVFamNormalizedGeneratorSupplyActual
  - qVFamNormalizedCoefficient / normalized generator.

Therefore the paper theta value is NOT realThetaValue q j = q^(j^2).
Use the existing paperThetaCoefficient / qVFamPaperThetaValueRoot.
realThetaValue q^(j^2) is the classical coefficient and is 2l times the
paper root coefficient.
