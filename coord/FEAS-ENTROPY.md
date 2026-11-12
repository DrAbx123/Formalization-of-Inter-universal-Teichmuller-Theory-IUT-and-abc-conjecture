# FEAS-ENTROPY — can entropy/SSA/Araki-Lieb/DPI prove our lower bound?

Status: READ-ONLY feasibility, 2026-11-12. No compile.
Target: V + gap >= (sF - 1) * A, equivalently M = V + gap - (sF-1)A >= 0,
equivalently A - R >= 0 / -A <= rhs. This is our weaker variant, not lana
SSIneq (V - (sF-1)A >= 0).

Judgments:
  A = directly instantiable from an already-proved entropy inequality
  B = reducible only with new definitions and/or extra explicit hypotheses
  C = only restatement/renaming; no independent proof content

VERDICT: A = NO. B = only conditional and with a gap/entropy identification that
is itself the hard content. C = the honest status of the current unconditional
route. Details below.

## 1. Exact shape of our target

From coord/C-MARGIN-FIX.md / DECOMP-EXISTING-LEMMAS.md / CONDITION-LATTICE.md:
  M := V + gap - (sF - 1) * A,
  gap := rhs + sF(nC) * A - V(hull VC),
  hence V + gap = rhs + sF(nC) * A and
  M = A + rhs = A - R, R = -rhs.
So the target is a scalar inequality between:
- V = log-vol(hull VC) (a Haar log-volume, may be negative),
- A = qPilot.absLogQ (a positive log magnitude),
- rhs = -|log Theta| / R (another log-volume),
- sF = (sum_{j=1}^{nC} j^2)/nC (a rational > 1),
- gap, which is defined by the identity above, not an independent quantity.

The equivalent form -A <= rhs is important: after substituting gap, the target
is just a comparison of two signed scalar log-volumes. It is not a statement
about an entropy of a random variable.

## 2. What entropy inequalities actually say

Classical SSA / submodularity (finite random variables):
  H(X) + H(Y) >= H(X,Y)  (submodularity),
  H(X,Y) + H(Y,Z) >= H(X,Y,Z) + H(Y)  (strong subadditivity).
Araki-Lieb (quantum/classical bipartite):
  H(A,B) >= |H(A) - H(B)|.
DPI (KL):
  klDiv(mu,nu) >= klDiv(mu K, nu K) for a channel K.

Structural mismatches:
1. Coefficients. SSA/submodularity have unit coefficients and positive signs.
   Our target has coefficient 1 on V and gap, coefficient (sF-1) on A with a
   negative sign; sF is a nontrivial rational function of nC. To realize it by
   unit-coefficient entropy inequalities one needs q copies (q = denominator)
   and a mixture/tensor construction. That is new structure, not an instance.
2. Signs. Shannon entropy is nonnegative; log-volumes are signed. A shifted
   entropy H + C can model a signed log-volume, but the constants must cancel
   exactly in the target; no entropy theorem supplies that cancellation.
3. Gap is a definition. gap = rhs + sF A - V is an identity, so the target
   after substitution is rhs >= -A. Entropy cannot prove this scalar comparison
   unless gap (or an equivalent scalar) is independently identified with a
   conditional entropy. That identification is precisely the missing content.
4. Archimedean/weight terms. Our V includes an archimedean contribution
   (archDefect and continuous factors); discrete Shannon entropy gives no such
   real factors. Differential entropy has no in-tree SSA/DPI API and is not
   directly comparable to Haar log-volume without a normalization theorem.

## 3. Attempt 1: uniform finite model (can it make log-volume an entropy?)

Take a finite probability space with N equal atoms. The Shannon entropy of the
uniform distribution is log N. If a region S is modeled by N_S equal cells and
the measure is counting/scaled, then
  log mu(S) = log N_S = H(uniform on S) + const.
So a single log-volume can be matched to an entropy up to an additive constant.
For a product of independent cells, entropy is additive, so SSA is an equality,
not an inequality with a gap.

To get our gap, one must replace the product/uniform model by a non-product
channel K and set
  gap := H(conditional distribution of the channel) + constants.
Then SSA/DPI can produce an inequality involving H(V)+H(gap)-... only if the
channel is independently constructed and its conditional entropy is proved equal
to the paper's gap. That is a new definition plus a new entropy identity; it is
not a direct instance.

The weight sF can in principle be encoded by q copies (q denominator of sF) or
by a tensor power of size q, but sF is an average of j^2, not a natural block
dimension; the construction would be ad hoc and would still leave the gap and
arch terms to be matched.

## 4. Attempt 2: Araki-Lieb / SSA lower bound

Araki-Lieb gives a lower bound on a joint entropy:
  H(A,B) >= |H(A)-H(B)|.
If one could set
  H(A,B) = V + gap (up to constants),
  H(A)   = V, H(B) = (sF-1)A,
then target would follow from H(A,B) >= H(B)-H(A) (one sign of Araki-Lieb).
But this requires:
- a bipartite system whose joint entropy is V+gap,
- marginals whose entropies are V and (sF-1)A,
- the exact identification of gap with the conditional entropy H(A|B),
- the weight (sF-1) as a dimension/multiplicity,
- all constants from the arch/torsion terms.
The first three are the hard paper content; the fourth is a new arithmetic model.
Thus this is a conditional B route, not an A route.

## 5. Attempt 3: DPI

DPI gives
  klDiv(mu,nu) <= klDiv(mu compProd K, nu compProd eta).
It controls relative entropy under coarsening; it does not compare two log-volumes
with a weight sF. The only direct volume statement from normalized Haar
restrictions is the nested KL identity
  klDiv(mu|A, mu|B) = log(mu B / mu A) for A subset B,
which is automatic and does not give the signed target. DPI is a TOOL for
approximation/error control, not a source of M >= 0.

## 6. Required new definitions for a B route

If one insists on a conditional entropy reduction, the minimal new objects are:
1. Finite probability spaces / measurable partitions Omega_theta, Omega_q,
   Omega_gap with maps to the actual C3 tensor block.
2. Equal-cell volume theorem: H(uniform on Omega_S) = log mu(S) + const_S for
   each region, with constants that cancel in the target.
3. A channel K (Markov kernel) with a proved conditional-entropy identity
   gap = H(conditional of K) + constants (or an equivalent entropy expression).
4. Weight realization: a tensor/copy construction of size q such that
   (sF-1) = (p-q)/q is represented by entropy multiplicities.
5. Archimedean/torsion normalization: a proof that the archDefect and torsion
   terms are absorbed into the entropy constants, not assumed.
6. A final SSA/Araki-Lieb instance proving the resulting entropy inequality.
Items 2-5 are new substantive theorems; item 3 is essentially the target in
entropy language.

## 7. Circularity check

The dangerous pattern is:
  define gap := H(conditional) (or define a probability model so that this holds),
  then quote SSA to get V+gap >= (sF-1)A.
This is circular if the definition of the probability model/conditional entropy
is chosen to make the inequality true. A legitimate B route must construct the
model independently from the actual Haar/q-pilot geometry and prove the entropy
identification without using the target inequality. No such construction exists
in the tree.

## 8. Judgment

A (direct instance): NO.
  No existing entropy/SSA/Araki-Lieb/DPI theorem has the right objects, signs,
  coefficients (sF), arch terms, or gap identification. Local Mathlib has KL
  chain rule but no Shannon entropy/SSA development; differential entropy has no
  in-tree SSA.

B (conditional reduction): ONLY with an explicit EntropyModel plus independent
  gap=conditional-entropy and weight/arch identifications. These are new
  substantive theorems; currently none exist. The result would be conditional,
  not an unconditional proof of M >= 0.

C (restatement): The current unconditional route is C. Without new definitions,
  any claim that SSA/DPI proves our lower bound is a renaming of the target; the
  gap identity alone reduces it to rhs >= -A, and entropy supplies no independent
  comparison of those two log-volumes.

Recommendation: do not pursue entropy/SSA as a primary proof route. Keep KL DPI
as a TOOL for diagnostics only; keep the target as our variant, not lana SSIneq.
No Lean file written; no compile claimed.
