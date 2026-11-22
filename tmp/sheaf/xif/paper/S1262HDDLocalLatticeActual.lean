import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual

-- S1262: actual HDD local lattice from actualSHEOutput/oneColumnStructure.
-- rank 1; lattice = span of the actual unit section in the completed local field.
-- No exact first-field placeholder, no arbitrary Set.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1262HDDLocalLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- The actual rank: the integral line bundle is rank one. -/
def s1262Rank : Nat := 1

/-- The actual local lattice at a place: the span, in the completed local
field, of the localization of the actual unit section. -/
noncomputable def s1262LocalLattice (I : Input Label Choice)
    (v : NumberField.FinitePlace ℚ) :
    Submodule ((oneColumnStructure).localRing v)
      (Fin (s1262Rank) → (oneColumnStructure).localField v) :=
  Submodule.span ((oneColumnStructure).localRing v)
    ({fun _ : Fin (s1262Rank) =>
      (oneColumnStructure).localizationInclusion v
        ((actualSHEOutput I).bundle.localization v
          (unitSection : (integralLineBundle).total))} :
      Set (Fin (s1262Rank) → (oneColumnStructure).localField v))

/-- The actual S1215 HDD local lattice. -/
noncomputable def s1262HDDLocalLattice :
    S1215HDDLocalLattice (I := I) where
  rank := s1262Rank
  lattice := fun _ v => (s1262LocalLattice I v :
    Set (Fin s1262Rank → (oneColumnStructure).localField v))

theorem s1262HDDLocalLattice_rank :
    (s1262HDDLocalLattice (I := I)).rank = 1 := rfl

theorem s1262HDDLocalLattice_lattice (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) :
    (s1262HDDLocalLattice (I := I)).lattice o v =
      (s1262LocalLattice I v :
        Set (Fin s1262Rank → (oneColumnStructure).localField v)) := rfl

#check s1262HDDLocalLattice
#check s1262HDDLocalLattice_rank
#check s1262HDDLocalLattice_lattice

end LeanFormal.IUT.XiFPaper.S1262HDDLocalLatticeActual

end