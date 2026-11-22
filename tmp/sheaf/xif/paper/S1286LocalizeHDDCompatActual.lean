import tmp.sheaf.xif.paper.S1262HDDLocalLatticeActual
import tmp.sheaf.xif.paper.S1275SHEDDNonLatticeFieldsActual

-- S1286: actual localize_hdd_compat for the S1262 rank-one lattice and
-- the S1275 actual sheLocalization/readout.  localizeSection is the
-- actual unit section, hence the equality is rfl.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1286LocalizeHDDCompatActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1262HDDLocalLatticeActual
open LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Actual localizeSection: take the actual unit section for every lattice
element.  The S1262 lattice is the span of the localization of this very
section, so the localization equality is definitional. -/
noncomputable def s1286LocalizeSection
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (_x : (s1262HDDLocalLattice (I := I)).lattice o v) :
    (actualSHEOutput I).bundle.total :=
  unitSection

/-- Actual localize_hdd_compat for the S1262 actual lattice and S1275 actual
sheLocalization. -/
theorem s1286LocalizeHDDCompat
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin (s1262HDDLocalLattice (I := I)).rank →
      (oneColumnStructure).localField v)
    (hx : x ∈ (s1262HDDLocalLattice (I := I)).lattice o v) :
    (s1275SHELocalization (I := I)).expression v o =
      (actualSHEOutput I).bundle.localization v
        (s1286LocalizeSection (I := I) v o ⟨x, hx⟩) := rfl

theorem s1286LocalizeHDDCompat_unit
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin (s1262HDDLocalLattice (I := I)).rank →
      (oneColumnStructure).localField v)
    (hx : x ∈ (s1262HDDLocalLattice (I := I)).lattice o v) :
    (s1275SHELocalization (I := I)).expression v o =
      (actualSHEOutput I).bundle.localization v unitSection := rfl

#check s1286LocalizeSection
#check s1286LocalizeHDDCompat
#check s1286LocalizeHDDCompat_unit

end LeanFormal.IUT.XiFPaper.S1286LocalizeHDDCompatActual

end