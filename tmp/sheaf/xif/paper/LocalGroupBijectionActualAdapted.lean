import tmp.sheaf.xif.paper.ClauseEToD7LocalGroupActual

/-!
# Local group bijections: actual per-local-source image equivalence

Clause E supplies, at every selected finite or infinite place, a
ProfiniteFundamentalGroupInclusion whose arithmetic component is an open
embedding, hence injective but in general not surjective.

This file constructs the actual bijection from the source local group onto the
image of that embedding:

  profiniteImageEquiv : G ~= Set.range (e.hom)

and applies it to the clause-E finite/infinite local sources:

  finiteLocalGroupImageEquiv :
    L.xGroups.sequence.arithmetic.carrier
      ~= Set.range (L.local_group_inclusion.arithmetic.hom)
  infiniteLocalGroupImageEquiv : analogous.

The full ClauseEToD7LocalGroupBijection is still missing: it requires a global
canonical-place-indexed choice of these local carriers and identifications of
the modified carrier with the image subgroup at sectionMap x. This exact missing
object is recorded as MissingClauseEToD7LocalGroupBijection from the previous
file. No arbitrary global carrier or map is chosen; no toy/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace LocalGroupBijectionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.ClauseEToD7Actual
open LeanFormal.IUT.XiFPaper.ClauseEToD7LocalGroupActual

universe u

variable {l : PrimeGeFive}

/-- The actual image equivalence of an injective profinite open embedding. -/
noncomputable def profiniteImageEquiv
    {G H : ProfiniteGrp.{u}} (e : ProfiniteOpenEmbedding G H) :
    G ≃ Set.range e.hom :=
  Equiv.ofInjective e.hom (ProfiniteOpenEmbedding.injective e)

/-- The actual image equivalence for a finite clause-E local source. -/
noncomputable def finiteLocalGroupImageEquiv
    {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B}
    {E : SourceClauseD A S C B D}
    {w : NumberField.FinitePlace A.K}
    (L : SourceFiniteLocalSource A S C B D E w) :
    (L.xGroups.sequence.arithmetic : Type u) ≃
      Set.range (L.local_group_inclusion.arithmetic.hom) :=
  profiniteImageEquiv L.local_group_inclusion.arithmetic

/-- The actual image equivalence for an infinite clause-E local source. -/
noncomputable def infiniteLocalGroupImageEquiv
    {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B}
    {E : SourceClauseD A S C B D}
    {w : NumberField.InfinitePlace A.K}
    (L : SourceInfiniteLocalSource A S C B D E w) :
    (L.xGroups.sequence.arithmetic : Type u) ≃
      Set.range (L.local_group_inclusion.arithmetic.hom) :=
  profiniteImageEquiv L.local_group_inclusion.arithmetic

/-- The exact missing global ClauseEToD7LocalGroupBijection, for a completed
native source C. -/
def MissingGlobalLocalGroupBijection (C : SourceCompletion.{0} l) : Prop :=
  MissingClauseEToD7LocalGroupBijection C

/-- The global missing object is exactly the previously isolated pointwise
bijection. -/
theorem missingGlobalLocalGroupBijection_iff
    (C : SourceCompletion.{0} l) :
    MissingGlobalLocalGroupBijection C ↔
      MissingClauseEToD7LocalGroupBijection C :=
  Iff.rfl

/-- The per-local-source image bijections are actual; only their global
canonical-place assembly remains missing. -/
theorem localGroupImageBijections_actual
    {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B}
    {E : SourceClauseD A S C B D}
    {wFinite : NumberField.FinitePlace A.K}
    (Lf : SourceFiniteLocalSource A S C B D E wFinite) :
    Nonempty
      ((Lf.xGroups.sequence.arithmetic : Type u) ≃
        Set.range (Lf.local_group_inclusion.arithmetic.hom)) :=
  ⟨finiteLocalGroupImageEquiv Lf⟩

end LocalGroupBijectionActualAdapted
end LeanFormal.IUT.XiFPaper
end
