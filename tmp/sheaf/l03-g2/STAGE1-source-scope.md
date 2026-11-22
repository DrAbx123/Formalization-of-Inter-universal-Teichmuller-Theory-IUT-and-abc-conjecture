# STAGE 1 — Source scope for L0.3 G2

Status: phase-1 statement/scope record only. No Lean file created in this step. No statement below is asserted as proved.

Sources read:
- Iut/Foundations/Orbicurve.lean (OrbicurveFiniteEtaleCover at line 518; OrbicurveEtaleFundamentalGroup at line 855)
- tmp/l03-direct-consumer-audit-20261022/consumer_trace.md

## 1. Exact category / object / universe used by the actual source consumer

The source consumer is the orbicurve Galois-category route, not the scheme finite-etale-cover route.

From Orbicurve.lean:

- Universe: universe u; F : Type u with [Field F].
- Base schemes: SchemeOverField F := Over (Spec(F)), with the big etale topology SchemeOverField.etaleTopology F.
- Stacks: EtaleStackOverField F has
  fiber : LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u,u}
  and isStack : fiber.IsStack (SchemeOverField.etaleTopology F).
  Thus source objects are category-valued etale stacks over Spec F, not schemes.
- Covers: for X : HyperbolicOrbicurve F, an object of
  OrbicurveFiniteEtaleCover X is
  { source : EtaleStackOverField F, map : source.Hom X.stack, finiteEtale : EtaleStackFiniteEtaleMorphism map }.
  Here source.Hom X.stack is a strong transformation of pseudofunctors, and
  EtaleStackFiniteEtaleMorphism is the representable finite-etale condition.
- The Galois package is OrbicurveEtaleFundamentalGroup X G with
  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X),
  galoisCategory : @GaloisCategory (OrbicurveFiniteEtaleCover X) coverCategory,
  a base scheme and base point, a fiber functor to FintypeCat.{u}, a natural
  identification with literal geometric fibers, a bijective realization of every
  categorical arrow by a stack morphism over X, and an IsFundamentalGroup certificate.

From consumer_trace.md, the actual source consumers are:

- SourceCompletionSignQuotient A storing xF : HyperbolicOrbicurve A.F,
  xF_geometry : SourceOncePuncturedGeometry A.curve xF, and
  xFGroups : SourceOrbicurveGroupData xF (AbsoluteGaloisProfinite A.F),
  plus corresponding data for the sign quotient cF.
- SourceOrbifoldGroupData contains OrbicurveFundamentalGroupData.
- SourceClauseConstructors.ofFundamentalGroup consumes a real
  OrbicurveEtaleFundamentalGroup together with actual group projection/kernel data.

Consumer consequence: the required G2 is a quotient property of
OrbicurveFiniteEtaleCover xF, not of FiniteEtaleCover S for a scheme S.

## 2. Is the source G2 field literally
HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover xF)?

No, not as currently stated.

- OrbicurveEtaleFundamentalGroup has no separate field named
  hasQuotientsByFiniteGroups.
- The quotient/action requirement is carried indirectly by the
  galoisCategory : GaloisCategory ... field (and its underlying
  PreGaloisCategory axioms). It is not exposed as a standalone
  HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover xF) field.
- The scheme-side formulation does exist in
  GlobalQuotientUniversalProperty.GlobalQuotientCoconeResidual S, namely
  forall (G) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S),
  but it is a scheme-cover residual and is not a statement about
  OrbicurveFiniteEtaleCover X.

Therefore the target can be frozen in either of two equivalent-in-intent forms,
but they must not be identified by definition:

A. Direct source form:
forall (G : Type u) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X)
with the chosen coverCategory and Galois/fiber compatibility.

B. Galois-axiom form: prove the quotient axiom inside the actual
GaloisCategory (OrbicurveFiniteEtaleCover X) instance, with the fiber functor
and IsFundamentalGroup certificate preserved.

Neither is a literal field of the current
OrbicurveEtaleFundamentalGroup; both require a transport/construction proof.

## 3. Comparisons needed from scheme FiniteEtaleCover G2 to the source category

At minimum:

1. Representability comparison.
   For a scheme S : SchemeOverField F, the representable stack
   schemeRepresentableEtalePseudofunctor F S must be compared with
   X.stack.fiber. A source object X such as the once-punctured elliptic
   orbicurve must be represented by an actual scheme/stack together with the
   correct orbifold structure. For a stacky/sign-quotient orbicurve this may not
   be scheme-representable; representability cannot be assumed from a bare
   signature equality.

2. Finite-etale predicate comparison.
   The scheme category uses IsFiniteEtaleHom (Etale and IsFinite). The source
   category uses EtaleStackFiniteEtaleMorphism (representably finite etale).
   One must prove that representable stack morphisms induced by scheme
   finite-etale maps satisfy the stack predicate, and conversely that every
   source finite-etale cover in the represented case comes from such a scheme
   cover.

3. Categorical comparison of cover categories.
   Construct an equivalence (or at least a fully faithful/essentially
   surjective comparison preserving the finite-etale structure)
   FiniteEtaleCover S to OrbicurveFiniteEtaleCover X, compatible with the
   over-X maps and the coverMorphism realization field.

4. Fiber comparison.
   The source package uses baseScheme, basePoint, the fiber functor to
   FintypeCat, and GeometricFiber as a CostructuredArrow of stack
   functors. One must identify the scheme geometric fiber with this literal
   stack fiber naturally, and show the identification is natural in cover
   morphisms (the fiberIdentification_natural field).

5. Galois/quotient transport.
   Transport the scheme-side finite-group action colimits (or Galois quotient
   axiom) across the comparison, and preserve the GaloisCategory structure,
   the fiber functor, and the IsFundamentalGroup certificate. A bare
   HasColimitsOfShape statement is not enough unless the fiber/GaloisCategory
   data are transported with it.

6. Sign quotient caveat.
   SourceCompletionSignQuotient also asks for the sign quotient cF.
   The sign quotient orbicurve may be non-scheme-representable. Results for the
   once-punctured scheme curveScheme K cannot be reused for cF without an
   actual representability/orbifold-stack comparison.

## 4. Exact gap and minimal freezeable local target

Exact gap:
There is currently no proved comparison from the scheme finite-etale-cover
category (or its finite-group action colimit property) to
OrbicurveFiniteEtaleCover X, and no construction of the Galois quotient axiom
inside the actual orbicurve cover category. The source package
OrbicurveEtaleFundamentalGroup therefore cannot be fed from a scheme-side G2
theorem by a type cast or an import.

Minimal freezeable local target (statement only, no proof claim):

Target S1:
Given X : HyperbolicOrbicurve F with a scheme S : SchemeOverField F and an
actual identification of X.stack.fiber with
schemeRepresentableEtalePseudofunctor F S (including the orbifold structure),
construct a comparison functor
schemeFiniteEtaleToOrbicurve : FiniteEtaleCover S ⥤ OrbicurveFiniteEtaleCover X
and prove it is an equivalence of categories preserving the over-S/over-X
morphisms and the finite-etale predicate.

Target S2:
From GlobalQuotientCoconeResidual S (or the direct scheme-side theorem),
derive
forall (G) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X)
along the equivalence S1, and transport the fiber functor/geometric-fiber
identification.

Target S3 (source binding, separate from G2):
Identify the actual source scheme corresponding to SourceCompletionSignQuotient
/SourceOncePuncturedGeometry with the representable stack used in S1; do not
use a mere signature = sourceTypeOneOne equality as the curve/source binding.
For the sign quotient cF, freeze the representability/orbifold-stack statement
separately.

Recommended next executable step:
Freeze S1 first as a statement dependency with the actual scheme S and the
actual stack identification; do not start with the fixed test curve's extra
properties, and do not replace the source category by scheme
FiniteEtaleCover or by a hypothesis field.

## 5. 对 consumer 结构的进一步核对（2026-10-22 追加）

- `OrbicurveEtaleFundamentalGroup` 是一个 structure，当前源码检索未找到它的构造器；它不是只缺一个 G2 字段的“现成结构”。
- 它的 `galoisCategory : GaloisCategory (OrbicurveFiniteEtaleCover X)` 是一个完整结构，G2/HasColimitsOfShape 只是其中 `PreGaloisCategory` 的一个字段。
- 因此 L0.3 的 G2 结果只能作为构造该结构所需的一个组件；不能单独声称已经构造 `OrbicurveEtaleFundamentalGroup` 或已经接入 `SourceCompletionSignQuotient.xFGroups`。
- 实际 source consumer 还需要：完整 `PreGaloisCategory` 其余公理、fiber functor、geometric fiber identification、coverMorphism realizability、IsFundamentalGroup certificate，以及这些数据与实际 source curve 的 binding。
- 这些属于 L0.3 之外的 source 接入包，须另列，不得用 G2 结果替代。
