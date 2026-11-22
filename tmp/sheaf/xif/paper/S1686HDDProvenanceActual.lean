import tmp.sheaf.xif.paper.S1669HDDOutputDependenceActual
import tmp.sheaf.xif.paper.S1638HDDRankTwoActual
import tmp.sheaf.xif.paper.S1630HDDOutputImageActual

/-! # S1686: HDD provenance red-team

S1669 proved that `S1630OutputDependentIntegralPoint` is fake-inhabitable by
casting the part (iii) label to a completion.  This file audits the dependent
S1513/S1551/S1630/S1638 types for the same junk source, constructs the junk
S1638 rank-two family explicitly, and records that a genuine source-provenance
map must come from the actual q-pilot/theta output-to-section data, which is
not formalized.  S1669's minimal nondegeneracy predicate is not used as a
complete provenance predicate. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1686HDDProvenanceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual
open LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual
open LeanFormal.IUT.XiFPaper.S1638HDDRankTwoActual
open LeanFormal.IUT.XiFPaper.S1669HDDOutputDependenceActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-- The junk source is an S1630 inhabitant, hence S1513/S1551 generators over
it are not source-provenanced. -/
theorem s1686S1630_fake_inhabited
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (hne : s.Nonempty) :
    Nonempty (S1630OutputDependentIntegralPoint (I := I) (s := s)) :=
  s1669S1630_fake_inhabited_of_det (I := I) (s := s) det hne

/-- The junk S1638 rank-two family: S1638's source/generator fields accept the
junk S1630 point family.  This is a negative control, not the paper object. -/
noncomputable def s1686JunkS1638Family
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (hne : s.Nonempty) : S1638HDDRankTwoFamily I s :=
  let P := s1669JunkS1630 (I := I) (s := s) det hne
  { source := P.toSource
    generator := s1551GeneratorFamilyOfPoints (D := P.toSource)
      (fun o v => ⟨P.point o, by rfl, P.integral o v, P.point_ne_zero o v⟩) }

/-- The actual SHE output type has a subsingleton honest part. -/
theorem s1686HonestOutput_subsingleton :
    Subsingleton (s1669HonestOutput I) :=
  s1669HonestOutput_subsingleton (I := I)

/-- Any honest-output section map is constant; actual output data alone cannot
provide an output-dependent genuine section. -/
theorem s1686HonestOutput_section_constant
    (f : s1669HonestOutput I → S1513DependentPoint s) :
    ∀ x y : s1669HonestOutput I, f x = f y := by
  letI := s1669HonestOutput_subsingleton (I := I)
  intro x y
  exact congrArg f (Subsingleton.elim x y)

/-- Exact provenance missing: an output-dependent section map on the honest
output part.  This is impossible, so a genuine paper provenance map cannot
factor through the actual output record alone. -/
def S1686HonestOutputProvenance (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  ∃ (f : s1669HonestOutput I → S1513DependentPoint s),
    ∃ x y : s1669HonestOutput I, f x ≠ f y

theorem s1686HonestOutputProvenance_false :
    ¬ S1686HonestOutputProvenance (I := I) (s := s) := by
  rintro ⟨f, x, y, hne⟩
  exact hne (s1686HonestOutput_section_constant (I := I) (s := s) f x y)

/-- S1669's junk and nondegeneracy are not source provenance: the provenance
object must be an actual q-pilot/theta output-to-section map, absent from the
current tree.  This names the exact missing interface. -/
def S1686PaperOutputToSectionMapMissing (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  ¬ S1686HonestOutputProvenance (I := I) (s := s)

theorem s1686PaperOutputToSectionMap_missing :
    S1686PaperOutputToSectionMapMissing (I := I) (s := s) :=
  s1686HonestOutputProvenance_false (I := I)

#check s1686S1630_fake_inhabited
#check s1686JunkS1638Family
#check s1686HonestOutput_section_constant
#check S1686HonestOutputProvenance
#check s1686PaperOutputToSectionMap_missing

end LeanFormal.IUT.XiFPaper.S1686HDDProvenanceActual
end
