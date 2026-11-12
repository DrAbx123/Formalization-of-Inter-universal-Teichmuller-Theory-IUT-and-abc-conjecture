# FEAS-YUAN — Arakelov arithmetic volume and our detBundle/theta-hull comparison

Status: READ-ONLY feasibility, 2026-11-12. No compile.
Target: V + gap >= (sF - 1) * A, equivalently M = A - R >= 0,
V = theta-hull log-volume, A = qPilot.absLogQ, gap = rhs + sF A - V,
detBundle/theta hull are our arithmetic determinant/line-bundle objects.
Judgments: A = direct instance of a proved theorem; B = conditional with new
model; C = only analogy/restatement.

VERDICT: A = NO. B = only after a substantial new Arakelov model and metric
identification. C = current unconditional status (analogy, not proof).

## 1. What the Arakelov theory provides

Standard objects:
- X projective variety over a number field K, flat projective arithmetic model
  X -> Spec O_K;
- adelic/hermitian R-line bundle ar L = (L, ||.||_v) with metrics at all
  places (Zhang adelic metrics; semipositive/positive metrics);
- arithmetic volume widehat{vol}(ar L): the leading asymptotic of
  h^0(X, nL) / n^d, normalized by d!; equivalently characterized as a sup/inf
  of normalized heights/volumes of metrics;
- arithmetic intersection numbers widehat{c}_1(ar L_1)...widehat{c}_1(ar L_d)
  (Gillet-Soule), with arithmetic Hilbert-Samuel and arithmetic bigness;
- bigness/positivity: widehat{vol}(ar L) > 0, and comparison theorems for
  adelic line bundles (Yuan; Zhang; Gillet-Soule).

These are asymptotic/positivity/continuity theorems. They do not supply a
finite scalar inequality with the specific weights, arch correction and gap of
our target without a model identifying those terms.

## 2. Candidate mapping

Natural formal mapping attempt:
- detBundle -> an adelic R-line bundle ar L_det on an arithmetic model;
- theta hull -> a metric/adelic structure ar L_theta whose arithmetic volume
  or normalized arithmetic degree is V;
- q-pilot line -> ar L_q with widehat{deg} = A;
- sF -> a tensor power/multiplicity of ar L_det or ar L_q;
- gap -> archimedean Green-function/error term in the adelic metric;
- target -> an arithmetic volume/intersection comparison
    widehat{vol}(ar L_theta) + arch-term >= (sF-1) widehat{deg}(ar L_q).
Equivalently, form a difference bundle
    ar L_diff = ar L_theta^{m} otimes ar L_q^{-n}
and ask for widehat{vol}(ar L_diff) >= 0 or an arithmetic intersection
inequality.

## 3. Why A fails

1. No arithmetic model/metric is defined in our tree. Our actual objects are
   p-adic Haar log-volumes on C3 tensor blocks and adelic/Frobenioid local
   regions, not a flat projective model with a Kähler/hermitian metric.
2. The target is not a standard bigness statement. It is a comparison of a
   theta-hull log-volume, a q-pilot degree A and a gap/arch correction with a
   rational weight sF. Yuan's arithmetic volume extremal characterization gives
   sup/inf formulas and continuity/asymptotics; it does not evaluate our
   specific Haar volumes or produce the exact gap.
3. The archimedean term. Our archDefect is a log of a factorial/ball-volume
   expression from local Haar measures; an Arakelov Green function contributes
   a different normalized archimedean metric. Matching them requires a new
   normalization theorem, not an instantiation.
4. The weight sF. sF is a rational average of j^2, not an integer tensor power.
   An adelic R-line bundle can carry rational coefficients, but the exact
   determinant/tensor-power identification with sF is a new arithmetic identity.
5. The target direction. Bigness gives positivity of a volume, while our target
   is a lower bound with an explicit gap and a sign convention. Even if a
   difference bundle has positive volume, that is weaker/different from the
   exact M >= 0 unless the equality of the volume with M is proved.

## 4. What a B route would require

To make the target an instance of a Yuan/Zhang/Gillet-Soule theorem, one needs:
1. A flat projective arithmetic model X -> Spec O_K for the relevant
   determinant/line-bundle data (currently no such model in the tree).
2. Adelic metrics whose archimedean and p-adic parts are proved to reproduce:
   - V = theta-hull log-volume (or an arithmetic volume/degree),
   - A = q-pilot degree,
   - gap = archimedean/error term.
3. A tensor-power/multiplicity identification of sF with an integral or rational
   adelic line bundle.
4. A proof that the target is exactly widehat{vol}(ar L_diff) >= 0 (or an
   arithmetic intersection inequality), not merely analogous.
5. Then use Yuan's arithmetic volume extremal characterization/bigness, Zhang's
   adelic metric positivity, or Gillet-Soule arithmetic intersection.
Items 1-4 are substantial new mathematics; item 4 is essentially the target
rephrased. Without them, the Arakelov theorem is an analogy, not an instance.

## 5. Gillet-Soule / Zhang specifics

- Gillet-Soule arithmetic intersection: if one had cycles and metrics, the
  target could be an arithmetic intersection number inequality. No cycles,
  models or intersection numbers are constructed for detBundle/theta hull in
  the current tree.
- Zhang adelic metrics: semipositivity/positivity gives concavity/volume
  inequalities for adelic line bundles; our theta-hull Haar metric is not shown
  to be semipositive, and the q-pilot line bundle is not given an adelic metric.
- Yuan arithmetic bigness: bigness/volume positivity is a qualitative
  asymptotic statement; our target is a finite quantitative inequality with
  explicit arch/gap terms.

## 6. Judgment

A (direct instance): NO.
  There is no arithmetic model, adelic metric, or line-bundle identification,
  and the available Arakelov theorems are asymptotic/positivity results, not our
  finite weighted inequality.

B (conditional reduction): YES, but only after constructing the arithmetic
  model, the adelic metrics, the V/A/gap identifications, the sF tensor-power
  identity, and proving the target equals an arithmetic volume/intersection
  statement. This is a large new program; none of it exists now.

C (restatement): The current unconditional route is C. Calling the target an
  "arithmetic volume comparison" without the model is only an analogy; it does
  not prove M >= 0 and risks hiding the missing arch/gap identification.

Recommendation: do not pursue Arakelov theory as a primary route. Keep it as a
conceptual reference for the archimedean normalization; the direct proof still
needs the local Haar/q-pilot/CTheta assembly. Our target remains the weaker
variant V + gap - (sF-1)A >= 0, not lana SSIneq.

No Lean file written; no compile claimed.
