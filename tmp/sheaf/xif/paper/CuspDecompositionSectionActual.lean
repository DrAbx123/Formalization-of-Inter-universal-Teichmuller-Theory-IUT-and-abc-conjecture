import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# Cusp decomposition subgroup / profinite section

The public orbicurve foundation exposes the closed-subgroup and profinite exact
sequence constructions, but it does not provide a cusp-to-decomposition-subgroup
functor or a Galois-to-arithmetic section.  This file records the actual data
interfaces and the exact missing group-theoretic functor; it does not fabricate
a subgroup or a section.

Actual existing construction: from a supplied
`OrbicurveCuspidalDecompositionData` one obtains its actual closed subgroup,
its actual exact sequence, and its actual ambient embedding.  These are
projections of a real datum, not arbitrary choices.

Missing: a function which, for each `OrbicurveBoundaryCusp X`, produces the
arithmetic decomposition subgroup together with the surjectivity predicate,
and a section of the Galois projection to that subgroup.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace CuspDecompositionSectionActual

open LeanFormal.IUT
universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {galois : ProfiniteGrp.{u}}
variable (groups : OrbicurveFundamentalGroupData X galois)

/-- The actual closed arithmetic subgroup attached to a supplied cuspidal
decomposition datum. -/
noncomputable def actualCuspDecompositionSubgroup
    (D : OrbicurveCuspidalDecompositionData groups) :
    ClosedSubgroup groups.arithmetic.group :=
  D.decompositionSubgroup

/-- The actual exact sequence of the supplied cuspidal datum. -/
noncomputable def actualCuspDecompositionExactSequence
    (D : OrbicurveCuspidalDecompositionData groups) :
    ProfiniteFundamentalExactSequence
      (OrbicurveCuspidalDecompositionData.inertia D)
      (OrbicurveCuspidalDecompositionData.decomposition D) galois :=
  D.exactSequence

/-- A profinite section of the arithmetic projection. -/
structure ProfiniteArithmeticSection where
  sectionMap : galois →* groups.arithmetic.group
  right_inverse : ∀ g : galois, groups.projection (sectionMap g) = g

/-- The actual missing group-theoretic cusp functor: assign to every boundary
cusp its arithmetic decomposition subgroup and the required surjectivity of the
closed-subgroup projection. -/
structure CuspDecompositionFunctor where
  subgroupOfCusp : OrbicurveBoundaryCusp X → ClosedSubgroup groups.arithmetic.group
  subgroupProjection_surjective : ∀ cusp : OrbicurveBoundaryCusp X,
    Function.Surjective
      (profiniteClosedSubgroupRestriction
        (subgroupOfCusp cusp) groups.projection)

/-- The actual missing cusp-dependent profinite section data. -/
structure CuspProfiniteSectionFunctor where
  decomposition : CuspDecompositionFunctor groups
  sectionOfCusp : OrbicurveBoundaryCusp X → ProfiniteArithmeticSection groups

/-- Exact required object: a cusp decomposition functor together with the
cusp-dependent arithmetic section.  No inhabitant is asserted. -/
def CuspProfiniteSectionFunctorRequired : Prop :=
  Nonempty (CuspProfiniteSectionFunctor groups)

/-- From an actual cusp functor and section family, construct the actual
section datum at a given cusp.  This is a real map from the missing input, not
an arbitrary section. -/
noncomputable def actualCuspSection
    (F : CuspProfiniteSectionFunctor groups)
    (cusp : OrbicurveBoundaryCusp X) :
    ProfiniteArithmeticSection groups :=
  F.sectionOfCusp cusp

/-- The actual decomposition subgroup supplied by a cusp functor. -/
noncomputable def actualCuspFunctorSubgroup
    (F : CuspDecompositionFunctor groups)
    (cusp : OrbicurveBoundaryCusp X) :
    ClosedSubgroup groups.arithmetic.group :=
  F.subgroupOfCusp cusp

end CuspDecompositionSectionActual
end LeanFormal.IUT.XiFPaper
end
