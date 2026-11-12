# R-PRODUCTION-STATUS — production ValueMonoid / posRealAction (A985)

Status: read-only survey. **No production nontrivial positive-real action exists**;
the paper D^⊢ source image action is only toy-modeled.  Model gap, not Lean gap.

## 1. Survey of ValueMonoid / action instances

Searched all `FPrimeStrip.Mon := ...` and `Multiplicative Real →*` occurrences:

- `SourceHaarActualValueMonoid` (`SourceUnitRegionHaarDataActual.lean:52`):
  `Multiplicative` of the nonpositive additive reals;
  `sourceHaarActualDegree` nonpositive (:57-66);
  `sourceHaarActualPositiveRealAction` is **constantly 1** (:76-82);
  used in `S1487Strip` (`S1487...:194`).
- `localFPrimeStrip` / `finiteLocalFPrimeStrip` (`LocalPrimeStrip.lean:30/52`):
  `Mon = (AlgebraicClosure ℚ_p)ˣ`, degree = p-adic norm log;
  **all units have norm 1**, so any positive-real action with this degree is trivial.
- `localIntegralFPrimeStrip` / `finiteLocalIntegralFPrimeStrip`
  (`LocalIntegralFPrimeStrip.lean:29/57`):
  `Mon = LocalIntegralMonoid`, degree = norm log (nonpositive on integral units);
  same triviality obstruction.
- `Example36PrimeStripComponentIdentification.lean:265/278`:
  `Mon = units of completions`, degree = norm; units have norm 1.
- `S1965FDoublePlusStripActual`, `S1969...`, `S1976AbstractDaggerFActionActual`:
  actions are by Galois groups / abstract kernels, not by `Multiplicative Real`.
- `SourceImageRealization` occurrences: all are hypotheses/consumers
  (`SourceImageHull`, `SourceImageHullVolume`, `SourceQSideComparison`, ...);
  **no producer/constructor** for a nontrivial action.

Conclusion: the only `Multiplicative Real →* Mon` in tree is the trivial
`sourceHaarActualPositiveRealAction`; every other Mon has degree = norm on units,
hence degree 0 on the image of any unit-group hom.  The paper's D^⊢ source
image action is not formalized (only a trivial toy model).

## 2. Mathematical obstruction for the existing models

For `SourceHaarActualValueMonoid`, any group hom
`f : Multiplicative Real →* SourceHaarActualValueMonoid` is trivial:
for x, f x and f x⁻¹ are both ≥1 in multiplicative value (degrees ≤0), and their
product is 1, so both have degree 0; hence f x = 1.  Thus no degree `log q ≠ 0`.
The same argument applies to any monoid whose elements have nonpositive degree and
whose only unit is 1.

## 3. Minimal data needed (new formalization)

For each `v` need:
1. a value monoid `M_v` with a genuine group action of `Multiplicative Real`;
2. a degree hom `d_v : M_v →* Multiplicative Real`;
3. a section at `log q`: an element `a ∈ M_v` or hom `f_v` with
   `d_v (f_v (ofAdd b)) = b` for all `b` (in particular `b = log q`).

Equivalently: a positive-real action whose degree is the identity on the real
parameter, i.e. the value monoid must contain the positive reals as a subgroup
(or a copy) and the degree must split the inclusion.

## 4. Consequence

- R = |log Θ| remains non-computable and `SourceImageRealization` is a **model
  gap**: it needs a new formalization of the paper's actual D^⊢ value monoid/
  positive-real action, not merely a missing Mathlib lemma.
- A *toy* model could be built with `M_v = Multiplicative Real`, `degree = id`,
  `action = id`; that would make R model-computable but would NOT be the paper R.
  Any such file must be labeled MODEL only.
- No green production file written in this pass; next step is a source-level
  definition of the actual value monoid/action (owner: paper/source lane).
