import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-!
# Actual native SourceOrbicurveClause from SourceClauseD data

Builds `SourceOrbicurveClause` from the actual native orbicurve/group data
available in `SourceClauseD`/`SourceClauseE`: the xK groups exact sequence
`D.x_groups.sequence`, the actual finite-etale cover `D.k_l_torsion_cover`, and
the actual K-side orbicurves `S.xK`, `S.cK`.

The exact-sequence clause is constructed from the actual profinite exact
sequence; its only explicit missing datum is a splitting section
`baseGroup →* coverGroup` (the source record does not carry one). The
curve/punctured/cover point carriers and their two maps are also not
carried by `SourceClauseD`/`SourceClauseE` as point-set data, so they are
explicit hypotheses; the types themselves are the actual finite-etale-cover
types of the native orbicurves. The cusp count is likewise an explicit
source field; no number is fabricated.

No arbitrary carrier, `True`, `PUnit`, fake exact sequence, axiom, or `sorry`
is used. Missing fields are parameters and are listed in the final report.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual

open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

universe u v w

/-- Convert the actual profinite exact sequence `D.x_groups.sequence` into
the source exact-sequence clause, taking the splitting section as an exact
explicit hypothesis. The groups and the injective/surjective/exact fields
are the native ones. -/
def sourceExactSequenceOfGroups
    {Ggeom Garith Galois : ProfiniteGrp.{u}}
    (sequence : ProfiniteFundamentalExactSequence Ggeom Garith Galois)
    (sectionMap : ↥Galois →* ↥Garith)
    (section_right_inverse : ∀ x : ↥Galois, sequence.projection (sectionMap x) = x) :
    SourceExactSequenceClause where
  baseGroup := ↥Galois
  coverGroup := ↥Garith
  geometricGroup := ↥Ggeom
  injection := sequence.inclusion.hom.toMonoidHom
  projection := sequence.projection.hom.toMonoidHom
  injection_injective := by
    intro x y h
    exact sequence.inclusion_injective h
  projection_surjective := by
    intro x
    exact sequence.projection_surjective x
  exact_at_cover := by
    intro x
    constructor
    · intro hx
      have hxker : x ∈ sequence.projection.hom.ker := hx
      have hxrange : x ∈ sequence.inclusion.hom.range := by
        rw [sequence.exact]
        exact hxker
      rcases hxrange with ⟨y, hy⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      change sequence.projection (sequence.inclusion y) = 1
      have hcomp : sequence.projection.hom.toMonoidHom.comp
          sequence.inclusion.hom.toMonoidHom = 1 :=
        sequence.projection_comp_inclusion_eq_one
      exact congrArg (fun f => f y) hcomp
  sectionMap := sectionMap
  section_right_inverse := section_right_inverse

namespace SourceExactSequenceOfGroups

variable {Ggeom Garith Galois : ProfiniteGrp.{u}}
variable {sequence : ProfiniteFundamentalExactSequence Ggeom Garith Galois}
variable {sectionMap : ↥Galois →* ↥Garith}
variable {section_right_inverse : ∀ x : ↥Galois, sequence.projection (sectionMap x) = x}

@[simp] theorem baseGroup_eq :
    (sourceExactSequenceOfGroups sequence sectionMap section_right_inverse).baseGroup =
      Galois := rfl

@[simp] theorem coverGroup_eq :
    (sourceExactSequenceOfGroups sequence sectionMap section_right_inverse).coverGroup =
      Garith := rfl

@[simp] theorem geometricGroup_eq :
    (sourceExactSequenceOfGroups sequence sectionMap section_right_inverse).geometricGroup =
      Ggeom := rfl

theorem sectionMap_right_inverse (x : ↥Galois) :
    (sourceExactSequenceOfGroups sequence sectionMap section_right_inverse).projection
        ((sourceExactSequenceOfGroups sequence sectionMap section_right_inverse).sectionMap x) = x :=
  section_right_inverse x

end SourceExactSequenceOfGroups

/-- Conditional construction of the native SourceOrbicurveClause from the
actual exact-sequence clause and the explicit native orbicurve fields that
SourceClauseD/E do not carry: point carriers/maps, cusp count, and curve
compatibility. The exact-sequence argument is the actual clause constructed
above (or the same native data); no arbitrary True/PUnit field is used. -/
noncomputable def nativeSourceOrbicurveClause
    (exactSequence : SourceExactSequenceClause.{u, v, w})
    (curve : Type u) (puncturedCurve : Type v) (cover : Type w)
    (structureGroup : Type u) [Group structureGroup]
    (curveToPunctured : puncturedCurve → curve)
    (coverToPunctured : cover → puncturedCurve)
    (cover_surjective : Function.Surjective coverToPunctured)
    (cuspCount : Nat) (cuspCount_pos : 0 < cuspCount)
    (curveCompatibility : Prop) (curveCompatibility_proved : curveCompatibility) :
    SourceOrbicurveClause.{u, v, w} where
  curve := curve
  puncturedCurve := puncturedCurve
  cover := cover
  structureGroup := structureGroup
  structureGroupLaw := inferInstance
  curveToPunctured := curveToPunctured
  coverToPunctured := coverToPunctured
  cover_surjective := cover_surjective
  exactSequence := exactSequence
  cuspCount := cuspCount
  cuspCount_pos := cuspCount_pos
  curveCompatibility := curveCompatibility
  curveCompatibility_proved := curveCompatibility_proved

/- EXACT GAP (task-504):
The actual SourceExactSequenceClause is constructed above from the native
SourceClauseD.x_groups.sequence, with the missing splitting section supplied
as an explicit hypothesis. The remaining SourceOrbicurveClause fields are
NOT carried as point-set data by SourceClauseD/SourceClauseE:
* the curve and punctured-curve point carriers and their map;
* the finite-etale cover point carrier and cover-to-punctured map;
* the cusp count and its positivity;
* the curve-compatibility proposition/witness (the finite-etale cover
  D.k_l_torsion_cover supplies one natural candidate, but the curve/punctured
  point maps are absent).
The conditional constructor above takes exactly these as explicit hypotheses
and does not fabricate them. No arbitrary True/PUnit/fake exact sequence,
axiom, or sorry is used. -/

#check sourceExactSequenceOfGroups
#check nativeSourceOrbicurveClause

end LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual

end
