import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual

-- S1238: the minimal actual step for SourceSHEHDDCompatibility.hddLocalLattice.
-- The exact first field type is S1215HDDLocalLattice; no inhabitant is
-- asserted because actualSHEOutput supplies only the 1-column bundle/reading,
-- not an HDD local lattice.  No fake singleton lattice or weak Prop is added.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1238HDDLocalLatticeExactFirstField

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Exact type of the first outstanding field: the HDD local lattice data. -/
abbrev S1238HDDLocalLatticeType : Type (v + 1) := S1215HDDLocalLattice (I := I)

/-- Exact first-field obligation, as a type (no inhabitant asserted). -/
abbrev S1238HDDLocalLatticeRequired : Type (v + 1) := S1215HDDLocalLattice (I := I)

/-- Actual donor fact: actualSHEOutput gives the 1-column bundle, its
localization and the unit-section reading.  This is not an HDD lattice. -/
theorem s1238ActualSHEDonor_reading
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  rfl

theorem s1238ActualSHEDonor_bundle
    (v : NumberField.FinitePlace ℚ) :
    (actualSHEOutput I).bundle.localization v unitSection =
      (actualSHEOutput I).bundle.localization v unitSection :=
  rfl

#check S1238HDDLocalLatticeType
#check S1238HDDLocalLatticeRequired
#check s1238ActualSHEDonor_reading

end LeanFormal.IUT.XiFPaper.S1238HDDLocalLatticeExactFirstField

end