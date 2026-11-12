# OUTSIDE-ENTROPY-TROPICAL — external theorems and their volume-comparison mapping

Status: READ-ONLY external-tool survey, 2026-11-12. No compile.
Scope: find 1-2 directly instantiable theorems among entropy/data-processing,
tropical valuation, Alexandrov-Fenchel; map to our volume comparison. All items
below are TOOLS, not our variant and not lana SSIneq.

## 1. Direct candidate 1: log-submodularity of a finite positive measure
(tropical valuation form; elementary, no new analysis)

Statement. Let X be a measurable space, mu a measure, A B : Set X, with
  0 < mu (A ∩ B), 0 < mu A, 0 < mu B, mu (A ∪ B) < top.
Then
  mu (A ∩ B) * mu (A ∪ B) <= mu A * mu B
and, taking Real.log,
  log (mu (A ∩ B)) + log (mu (A ∪ B)) <= log (mu A) + log (mu B).

Proof. Put x = mu (A \ B), y = mu (B \ A), z = mu (A ∩ B). Additivity gives
mu A = x+z, mu B = y+z, mu (A∪B) = x+y+z; the inequality is
z(x+y+z) <= (x+z)(y+z), i.e. 0 <= xy. Then Real.log_le_log applies when the
arguments are positive.

Objects needed:
- a measure mu on X (our actualC3LogShellTensorHaar works),
- measurable A,B (our actualC3LogShellTensorRegion / qPilotHaarRegion),
- positivity of the intersection and finiteness of the union.

Lean template (no compile):
  theorem log_measure_submodular
      {X} [MeasurableSpace X] (mu : Measure X) {A B : Set X}
      (hInter : 0 < (mu (A ∩ B)).toReal)
      (hA : 0 < (mu A).toReal) (hB : 0 < (mu B).toReal)
      (hUnion : mu (A ∪ B) < ⊤) :
      Real.log ((mu (A ∩ B)).toReal) + Real.log ((mu (A ∪ B)).toReal) <=
        Real.log ((mu A).toReal) + Real.log ((mu B).toReal)

Mapping to our volumes:
- mu = actualC3LogShellTensorHaar C3;
- A = actualC3LogShellTensorRegion C3 (theta hull),
  B = qPilotHaarRegion C3 (the missing q-side region);
- the conclusion is a valuation inequality for
  V (S) := log (mu S), the same shape as Haar log-volume.
- If theta subset q (the direction needed for negHaarLog), then
  A ∩ B = A and A ∪ B = B, so the inequality is an equality; it does NOT
  prove the qLog <= thetaLog comparison by itself. It is useful for non-nested
  component regions (union/intersection of hull components) and for proving
  additive/valuation identities, not for the final M >= 0.
- This is the honest "tropical valuation" tool: log of a measure is a
  submodular valuation on the set lattice; no tropical semiring formalism is
  required.

## 2. Direct candidate 2: Mathlib KL chain rule / data-processing inequality

Mathlib already has the KL divergence and its chain rule:
  Mathlib.InformationTheory.KullbackLeibler.ChainRule
  theorem klDiv_compProd_eq_add :
    klDiv (mu ⊗ₘ kappa) (nu ⊗ₘ eta)
      = klDiv mu nu + klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta)
  lemma klDiv_compProd_left :
    klDiv (mu ⊗ₘ kappa) (nu ⊗ₘ kappa) = klDiv mu nu
(no assumptions on the measurable spaces; finite-measure/kernel side conditions
as in the file).

Data-processing consequence (same channel/forgetful map):
  klDiv mu nu <= klDiv (mu ⊗ₘ kappa) (nu ⊗ₘ eta)
because the second term is a nonnegative ENNReal KL divergence:
  rw [klDiv_compProd_eq_add]; exact le_add_right le_rfl.
For the same kernel kappa = eta, the chain rule gives equality, not a strict
improvement.

Objects needed:
- finite measures mu, nu on a source space;
- Markov kernels kappa, eta (or composition-products mu ⊗ₘ kappa);
- Mathlib's klDiv, Measure.compProd, information-theory imports.

Mapping to our volumes:
- Let mu, nu be normalized Haar restrictions to the theta/q-pilot regions, and
  kappa the component-projection/coarsening map to a tensor factor or bad-place
  partition. DPI says coarsening cannot increase distinguishability:
  a lower bound for the component KL gives a lower bound for the full KL.
- For uniform densities on atoms, KL between normalized restrictions equals
  log (reference mass / region mass) plus constants; this can certify a
  volume gap between two regions, but it is a KL/relative-entropy statement,
  not an inequality for V + gap - (sF-1)A. It cannot replace the missing
  qRegion/volume identification or the theta subset q inclusion.
- Classification: TOOL. No lana SSIneq/strong inequality is assumed.

## 3. Entropy submodularity (external, not directly instantiable)

Standard theorem. For finite random variables X,Y,Z,
  H(X) + H(Y) >= H(X,Y)  (submodularity),
  H(X,Y) + H(Y,Z) >= H(X,Y,Z) + H(Y) (strong subadditivity).
Objects: finite probability space, random variables, Shannon entropy
  H(X) = - sum_x p(x) log p(x).

Why not direct:
- Our fundamental object is the log of a Haar measure of a set, not the
  entropy of a random variable. The set-measure analogue is the
  log-submodularity of candidate 1, not Shannon entropy.
- To use entropy one must first define a random variable from the volume
  profile (e.g. a component label with distribution mu(S_i)/mu(X)); then the
  conclusion is about the entropy of that label law, not about
  V(hull) or V(qRegion) directly.
- No entropy API is present in the local Mathlib checkout used here; this is
  external literature, not an existing Lean theorem.
Classification: ADAPT/GAP for our target; not a direct volume inequality.

## 4. Alexandrov-Fenchel inequality (external, not directly instantiable)

Statement (standard). For nonempty compact convex bodies K_1,...,K_n in R^n,
mixed volumes satisfy
  V(K_1,K_2,K_3,...,K_n)^2 >= V(K_1,K_1,K_3,...,K_n) V(K_2,K_2,K_3,...,K_n)
(Alexandrov-Fenchel); in particular the volume is log-concave under Minkowski
sums (Brunn-Minkowski):
  vol(K+L)^(1/n) >= vol(K)^(1/n) + vol(L)^(1/n).

Objects needed:
- real finite-dimensional vector space R^n,
- compact convex bodies,
- mixed volumes / intrinsic volumes (Steiner formula),
- a proof that our local regions are convex bodies in that vector space.

Why not direct:
- Our actual C3 tensor block is a p-adic / non-Archimedean product of local
  fields, not a real convex body. There is no in-tree convex-body model of the
  theta hull or q-pilot region, and no mixed-volume API in the local Mathlib
  checkout (searched: no Alexandrov/Fenchel/mixedVolume/logConcave).
- A tropical/logarithmic chart could turn product log-shell regions into
  polytopes, but constructing that chart and proving volume compatibility is
  new mathematics, not an instantiation.
Classification: GAP for the current carrier; AF is a conceptual guide only.

## 5. Tropical valuation summary

- The set-lattice identity behind candidate 1 is the valuation/modularity
  identity for a measure:
    mu(A∩B) + mu(A∪B) = mu(A) + mu(B).
- Taking log yields submodularity of V(S)=log mu(S) (candidate 1).
- In min-plus ("tropical") language this is the valuation property of the
  log-volume functional; it does not by itself give the sign/lower bound
  V + gap - (sF-1)A >= 0.
- Our target remains the weaker variant M>=0; external tools must not be
  presented as lana SSIneq or as already proving the variant.

## 6. Recommendation

Use candidate 1 as the primary directly instantiable tool:
  log_measure_submodular (measure valuation) with
  mu = actualC3LogShellTensorHaar, A/B = theta/q regions.
Use candidate 2 (Mathlib KL chain rule/DPI) only for relative-entropy
diagnostics of component projections; it is already formalized, but it does
not replace any of the three missing q-side bridge fields.

Do not attempt to instantiate AF on the current p-adic carrier without a new
convex/logarithmic model. Do not use Shannon entropy submodularity as if it
were a statement about Haar log-volumes; its mapping requires a new random
variable/volume-profile definition.

No Lean file written; no compile claimed.
