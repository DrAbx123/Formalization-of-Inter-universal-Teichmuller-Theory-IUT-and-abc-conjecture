import tmp.sheaf.xif.paper.S1286LocalizeHDDCompatActual

-- S1295: localizeSection and localize_hdd_compat for the S1262 lattice.
-- Actual compat uses the actual unit section (S1286).  The stronger
-- x-representation by span scalars is recorded exact: bundle.total has no
-- localRing-module structure, so span induction cannot produce it.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1295LocalizeSectionSpanActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1262HDDLocalLatticeActual
open LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual
open LeanFormal.IUT.XiFPaper.S1286LocalizeHDDCompatActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Actual localizeSection (constant on the span): the unit section. -/
noncomputable def s1295LocalizeSection
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : (s1262HDDLocalLattice (I := I)).lattice o v) :
    (actualSHEOutput I).bundle.total :=
  s1286LocalizeSection I v o x

/-- Actual localize_hdd_compat for the S1262 actual lattice. -/
theorem s1295LocalizeHDDCompat
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin (s1262HDDLocalLattice (I := I)).rank →
      (oneColumnStructure).localField v)
    (hx : x ∈ (s1262HDDLocalLattice (I := I)).lattice o v) :
    (s1275SHELocalization (I := I)).expression v o =
      (actualSHEOutput I).bundle.localization v
        (s1295LocalizeSection I v o ⟨x, hx⟩) :=
  s1286LocalizeHDDCompat I v o x hx

/-- Exact stronger condition: the section actually represents x under
localization.  This is not derivable from the span without a
localRing-module structure on bundle.total. -/
structure S1295LatticeSectionRepresentation
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) where
  localizeSection : ∀ (x : Fin (s1262HDDLocalLattice (I := I)).rank →
      (oneColumnStructure).localField v),
    x ∈ (s1262HDDLocalLattice (I := I)).lattice o v →
      (actualSHEOutput I).bundle.total
  represents : ∀ (x : Fin (s1262HDDLocalLattice (I := I)).rank →
      (oneColumnStructure).localField v)
    (hx : x ∈ (s1262HDDLocalLattice (I := I)).lattice o v),
    (oneColumnStructure).localizationInclusion v
      ((actualSHEOutput I).bundle.localization v (localizeSection x hx)) =
      x ⟨0, by
        rw [s1262HDDLocalLattice_rank (I := I)]
        norm_num⟩

#check s1295LocalizeSection
#check s1295LocalizeHDDCompat
#check S1295LatticeSectionRepresentation

end LeanFormal.IUT.XiFPaper.S1295LocalizeSectionSpanActual

end