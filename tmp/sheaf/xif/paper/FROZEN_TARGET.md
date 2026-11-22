# FROZEN PAPER TARGET (do not redefine)

Target is fixed by IUT III Corollary 3.12:

  -|log(Theta)| >= -|log(q)|.

Objects:
- Theta side: actual holomorphic hull of the union of possible images of the
  Theta-pilot under (Ind1),(Ind2),(Ind3), with the procession-normalized
  mono-analytic mu_log.
- q side: the q-pilot object determined by the local q-parameters q_v
  (single-underlined q_v), with

      log(q) = ord_v(q_v) * log(p_v)        (IUT III lines 7475-7480),

  and procession-normalized mono-analytic mu_log.

## Prohibited target changes

Do NOT replace the q-pilot by a normalized-coefficient object such as

  c_norm * log p,

or by qVFamNormalizedNorm, in order to make the correction disappear.  That
changes the target.  A theorem about the changed object is a model comparison,
not paper xi-f, even if it compiles.

## Required bridge

To connect the normalized Theta coefficient c_norm to the paper q-pilot, prove
the actual identity

  c_norm * log p = ord_v(q_v) * log(residueNormBase)

(or the equivalent per-b coefficient identity).  If it is false, the normalized
generator/norm definition is wrong; fix that, do not redefine q-pilot.

## Naming rule

Any theorem whose q-pilot is c_norm or qVFamNormalizedNorm must be named
`...ModelComparison...` or `...Intermediate...`, never `paperXiF` or
`ActualPaperXiFTarget`.
