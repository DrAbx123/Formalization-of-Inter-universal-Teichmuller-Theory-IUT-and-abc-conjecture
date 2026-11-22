# S728 memo: far-field tools for paper Θ-pilot hull log / root stack

Date: 2026-10-30
Status: research memo; no Lean claims. No fake construction.

## 0. Paper-faithful target (current repo state)

The missing paper object is not a radius or a theta-average surrogate. It is:

1. the **paper Θ-pilot holomorphic hull log**:
   `-|log Θ| = paperRootThetaHullLog`, with the exact remaining formula gap
   `PaperRootHullFormulaGap T b`:
   `paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b`;
2. the **root stack / q[2u] carrier**:
   actual `q[2u] = q[1u]^(1/(2l))` already lives in the finite extension
   `L = K(root)`:
   `rootNormedElement`, `rootNormedExtension`,
   `rootNormedThetaValueInL`, and S709:
   `(rootImageRadius T b : Real) =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * l.value))`.

The paper-level signed hull is `PaperSignedHull` with
`signedHullLogVolume = -ambient.logVolume ambient.hull`; the missing link is
the normalized hull log identification, not a generic measure on an unrelated
space. `RootThetaToCompletionHullMapGap` records the extension-valued
root hull to completion-valued root-coefficient hull transport, still open.

Criterion for "paper-faithful" in this memo:

* supplies an actual object with the same Kummer/procession normalization as
  `PaperSignedHull`, and
* yields a theorem identifying its log with `paperRootThetaHullLog` /
  `signedHullLogVolume` (or supplies the actual q[2u] root carrier used by
  `rootNormedThetaValueInL`).

Anything that only gives an asymptotic, model-dependent, or quotient-level
measure is auxiliary, not a replacement.

## 1. Berkovich skeleta / p-adic pluricanonical measures

Concrete tools:

* Berkovich analytification `X^an`, skeleton `Σ` of a semistable/SNC formal
  model, retraction `r_Σ : X^an -> Σ`.
* Chambert-Loir canonical measures on `X^an`; Jonsson-Nicaise,
  "Convergence of p-adic pluricanonical measures to Lebesgue measures on
  skeleta in Berkovich spaces": p-adic pluricanonical measures converge to a
  Lebesgue measure on the skeleton.
  <https://jep.centre-mersenne.org/article/JEP_2020__7__287_0.pdf>
* Survey: Chambert-Loir, "Heights and measures on analytic spaces".
  <https://ar5iv.labs.arxiv.org/html/1001.2517>

What it can do:

* model a Haar/Lebesgue measure on a **formal-model skeleton** of a
  finite-type Berkovich space;
* produce canonical measures independent of the model in the pluricanonical
  setting;
* in principle measure a compact p-adic analytic region (unit ball / hull)
  after choosing an SNC model and normalizing.

Why it does not give the paper object:

* The root extension `L = K(root)` is a complete non-archimedean **field**.
  Its Berkovich space `M(L)` is a single point; it has no skeleton and no
  Lebesgue measure. Berkovich measure theory cannot construct the root stack
  `q[2u]` carrier. The actual root carrier is already the finite extension
  `rootNormedExtension`; this direction adds nothing there.
* The paper Θ-pilot hull log is a **finite, procession-normalized** log-volume
  on an IQ/log-shell hull. Jonsson-Nicaise convergence is an asymptotic
  statement about pluricanonical measures, not an equality with
  `paperRootThetaHullLog`.
* A skeleton measure depends on a formal model and its canonical
  normalization, while the paper normalization is the procession/`q[2u]`
  normalization. No theorem in the literature identifies the two on this
  data, and the repo has no such bridge.

Verdict: **cannot construct a paper-faithful Θ hull log or root stack from
this direction alone.** It is at best an auxiliary measure model. A Lean
bridge would need a new object (formal model + skeleton) and an exact theorem
`skeletonMeasure hull = paperRootThetaHullLog`, which is currently missing.
The actual root stack should stay the finite extension already formalized in
`RootThetaExtensionHullCarrierActual` / `PaperRootCompletionTensorActual`.

## 2. Newton-Okounkov bodies / volumes

Concrete tools:

* Newton-Okounkov body `Δ(D)` of a divisor/line bundle with a valuation;
* Kaveh-Khovanskii / Lazarsfeld-Mustaţă theorem:
  `Vol(Δ(D)) = lim_{n} d! h^0(X, nD) / n^d`;
* convex-geometric computation of asymptotic section-volume.

What it can do:

* compute the asymptotic volume/degree of a Θ divisor or line bundle;
* prove convexity/body identities for Kummer/root line bundles.

Why it does not give the paper object:

* Newton-Okounkov volume is an **asymptotic Hilbert-function** invariant. The
  paper target is a finite normalized Haar log-volume on a compact analytic
  hull (`paperRootThetaHullLog`, `signedHullLogVolume`), not a leading
  coefficient of `h^0(nD)`.
* The root stack `q[2u]` is not a Newton-Okounkov body; its actual carrier is
  the finite extension `rootNormedExtension`. A body/valuation semigroup would
  not construct the root unit or its `2l`-power relation.
* No equality between `Vol(Δ)` and the procession-normalized paper log is
  available.

Verdict: **reject as paper-faithful for the Θ hull log/root stack.** It can
only be an auxiliary asymptotic/combinatorial computation, not the target.

## 3. Model theory of adeles / valued fields, elimination of imaginaries, Haar

Concrete tools:

* `ACVF` elimination of imaginaries; valued-field imaginaries;
* Hrushovski-Kazhdan motivic integration on valued fields;
* Cluckers-Loeser constructible motivic Haar measures; definable integration;
* adelic/definable quotient descriptions of `G_m/G_m^{2l}`, i.e. the
  `mu_{2l}`-torsor/root ambiguity as an imaginary quotient.
  Survey: <https://www.math.ens.psl.eu/~rideau/publication/book/pdf/VF-Fields.pdf>

What it can do:

* formalize the `mu_{2l}` indeterminacy as an imaginary/definable quotient;
* produce definable Haar measures and integration on valued-field definable
  sets;
* prove elimination-of-imaginaries statements for the root torsor.

Why it does not give the paper object:

* The paper root stack is a **geometric actual carrier**: `q[2u]` lives in
  the finite extension `L = K(root)`, and its norm/power relation is used by
  `rootNormedThetaValueInL` and S709. A definable quotient
  `G_m/G_m^{2l}` is only an imaginary class; it does not supply the actual
  root unit or the actual norm.
* A definable Haar measure is canonical only after model-theoretic
  normalization choices. It is not the same as the paper's mono-analytic
  procession-normalized Haar/log on the Θ hull; no comparison theorem exists.
* The paper's local bad-place θ/Θ data are not an adelic first-order structure;
  encoding them in `ACVF` would add a translation layer without proving the
  log identity.

Verdict: **reject for the Θ hull log.** It is a plausible auxiliary for
proving the `mu_{2l}` ambiguity quotient, but not for constructing the paper
root carrier or the normalized hull log. The actual root carrier should remain
the extension `rootNormedExtension`.

## 4. Condensed / almost mathematics, Banach modules

Concrete tools:

* almost ring theory (Gabber-Ramero), almost zero ideals, almost finitely
  presented modules;
* condensed/almost modules and Banach/complete tensor constructions;
* perfectoid/algebraic-closure root stacks where `2l`-torsion is almost zero
  in suitable settings.
  <https://public.websites.umich.edu/~bhattb/almost_purity_2011/gabber-ramero_-_p-adic_hodge_theory.pdf>

What it can do:

* model the `2l`-root stack in an almost/perfectoid category;
* handle completed tensor products and Haar measure at the level of Banach
  modules;
* make the `mu_{2l}` action formally manageable.

Why it does not give the paper object:

* Almost mathematics quotients by an ideal; the actual root `q[2u]` and its
  unit/norm are lost or become non-unique. The paper uses the actual finite
  extension `rootNormedExtension`, not an almost quotient.
* Condensed/Banach abstraction does not compute the paper's
  procession-normalized `Real.log` / mono-analytic log-volume on the IQ hull;
  it supplies no theorem identifying its Haar with `paperRootThetaHullLog`.
* The root stack here is already concrete: S709 gives
  `rootNormedElement` in a finite extension and the closed form for
  `rootImageRadius`. Almost/condensed technology does not simplify or
  strengthen that; it changes the carrier.

Verdict: **reject as paper-faithful** for both Θ hull log and root stack. At
best a formal setting for root ambiguity, with a missing comparison back to
the actual carrier.

## 5. Summary table

| Direction | Paper Θ hull log | Paper root stack / q[2u] | Exact missing bridge |
|---|---|---|---|
| Berkovich skeleta / pluricanonical measures | auxiliary only | no (finite field has one-point Berkovich space) | skeleton measure = procession-normalized hull log |
| Newton-Okounkov body/volume | no (asymptotic only) | no | `Vol(Δ)` vs finite Haar log |
| Model theory / EI / definable Haar | no (definable Haar ≠ mono-analytic log) | quotient-level only | definable quotient vs actual root carrier/norm |
| Condensed / almost mathematics | no | almost quotient only | almost root vs actual `q[2u]` and normalized log |

## 6. Recommendation

None of the four directions currently supplies a paper-faithful Θ-pilot hull
log or root stack. Do **not** replace:

* `PaperRootHullFormulaGap` with a skeleton/Okounkov/definable measure;
* `RootThetaExtensionHullCarrierActual` / `rootNormedExtension` with an
  imaginary/almost quotient.

If one auxiliary route is pursued, Berkovich skeleta is the closest for the
**measure/log side**, but only after constructing an actual formal model of the
IQ hull and proving an exact equality to `paperRootThetaHullLog`; that model
and equality are not presently in the repo or the cited literature. For the
**root stack side**, keep the actual finite extension and S709 closed form;
model theory can at most prove the `mu_{2l}` ambiguity, not construct the
paper carrier.

No fake object, no fake identification, no target change is proposed.
