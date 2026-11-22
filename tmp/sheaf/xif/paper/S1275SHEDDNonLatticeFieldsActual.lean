import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual

-- S1275: non-lattice fields of SourceSHEHDDCompatibility.
-- sheLocalization and readout_reference_compat are actual from SHEOutputActual.
-- localize_hdd_compat is kept exact, parameterized by an already-supplied HDD
-- lattice; no HDD lattice is constructed or modified here.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Actual sheLocalization: the actual localization expression of the actual
Theorem 3.11 output in the 1-column bundle. -/
noncomputable def s1275SHELocalization :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I) :=
  actualLocalizationExpression I

theorem s1275SHELocalization_output :
    (s1275SHELocalization (I := I)).output = theorem311Output I := rfl

theorem s1275SHELocalization_reading (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) :
    (s1275SHELocalization (I := I)).expression v o =
      (integralLineBundle).localization v unitSection := rfl

/-- Actual readout_reference_compat: the actual localization expression reads
exactly the actualSHEOutput reading map. -/
theorem s1275ReadoutReferenceCompat (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) :
    (s1275SHELocalization (I := I)).expression v o =
      (actualSHEOutput I).readingMap v o := rfl

/-- Exact localize_hdd_compat type: it consumes an already-supplied HDD
local lattice and section map; it does not construct either. -/
def S1275LocalizeHDDCompatExactType
    (L : S1215HDDLocalLattice (I := I))
    (E : SourceLocalizationExpression oneColumnStructure (Theorem311Output I))
    (localizeSection : ∀ (v : NumberField.FinitePlace ℚ)
      (o : Theorem311Output I), L.lattice o v →
        (actualSHEOutput I).bundle.total) : Prop :=
  ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin L.rank → (oneColumnStructure).localField v)
    (hx : x ∈ L.lattice o v),
    E.expression v o =
      (actualSHEOutput I).bundle.localization v
        (localizeSection v o ⟨x, hx⟩)

#check s1275SHELocalization
#check s1275SHELocalization_reading
#check s1275ReadoutReferenceCompat
#check S1275LocalizeHDDCompatExactType

end LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual

end