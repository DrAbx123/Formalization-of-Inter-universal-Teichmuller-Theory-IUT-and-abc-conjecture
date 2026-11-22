import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual

-- S1268: exact first field for `S1215HDDLocalLattice`, with the actual
-- localization obstruction recorded.
--
-- `actualSHEOutput` supplies the actual Theorem 3.11 output, the 1-column
-- bundle, its completed localization and the unit-section reading.  It does
-- not supply an HDD hull+det module, a rank for such a module, or a
-- lattice-to-bundle-total map.  Consequently no inhabitant of
-- `S1215HDDLocalLattice` is asserted here: a rank chosen from the SHE unit
-- section and a Set (Fin rank -> localField v) generated from that one section
-- would be SHE data, not HDD data.
--
-- In particular this file does not use Fin 0, Fin 1, an arbitrary Set, a weak
-- Prop, a Nonempty gate or Classical.choice to manufacture the first field.
-- The remaining exact obligation is the type `S1215HDDLocalLattice (I := I)`.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1268HDDLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Exact first field: the HDD local-lattice data required by S1215, with its
actual rank/lattice shape `output -> place -> Set (Fin rank -> localField v)`. -/
abbrev S1268HDDLocalLatticeExact : Type (v + 1) :=
  S1215HDDLocalLattice (I := I)

/-- Exact unresolved obligation: the same type, recorded without an inhabitant. -/
abbrev S1268HDDLocalLatticeRequired : Type (v + 1) :=
  S1215HDDLocalLattice (I := I)

/-- Actual SHE donor: at every place the reading is the completed-ring
localization of the unit integral section. -/
theorem s1268ActualReading_eq_unitSection
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  rfl

/-- The actual SHE reading is independent of the Theorem 3.11 output argument.
Thus the available SHE reading cannot distinguish the HDD data attached to two
different outputs. -/
theorem s1268ActualReading_output_independent
    (v : NumberField.FinitePlace ℚ) (o o' : Theorem311Output I) :
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).readingMap v o' :=
  rfl

/-- The expression of any actual S1215 compatibility record is the unit-section
localization, by `readout_reference_compat` and `indeterminacy_sync`.  This does
not depend on the HDD lattice or on its rank. -/
theorem s1268SHEExpression_eq_unitSection
    (C : SourceSHEHDDCompatibility (I := I) J)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection := by
  rw [C.readout_reference_compat v o, C.indeterminacy_sync v o]

/-- Obstruction: in any actual S1215 compatibility record, the HDD local section
attached to an HDD lattice element localizes to the unit section.  Hence
`localize_hdd_compat` does not transport the HDD lattice itself into the
1-column bundle total; it only reproduces the already-fixed unit reading.  This
is why a rank/lattice chosen from the SHE unit section cannot serve as the HDD
local lattice. -/
theorem s1268LocalizeSection_localizes_to_unitSection
    (C : SourceSHEHDDCompatibility (I := I) J)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin C.hddLocalLattice.rank → (oneColumnStructure).localField v)
    (hx : x ∈ C.hddLocalLattice.lattice o v) :
    (actualSHEOutput I).bundle.localization v
        (C.localizeSection v o ⟨x, hx⟩) =
      (actualSHEOutput I).bundle.localization v unitSection := by
  rw [← C.localize_hdd_compat v o x hx]
  exact s1268SHEExpression_eq_unitSection (I := I) (J := J) C v o

/-- Conditional form: if the actual completed localization is injective at the
place, the HDD local section is literally the unit integral section.  The
injectivity of the completed integral localization is an arithmetic donor fact
(characteristic zero), kept as an explicit hypothesis here. -/
theorem s1268LocalizeSection_eq_unitSection_of_injective
    (C : SourceSHEHDDCompatibility (I := I) J)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin C.hddLocalLattice.rank → (oneColumnStructure).localField v)
    (hx : x ∈ C.hddLocalLattice.lattice o v)
    (hinj : Function.Injective ((actualSHEOutput I).bundle.localization v)) :
    C.localizeSection v o ⟨x, hx⟩ = unitSection :=
  hinj (s1268LocalizeSection_localizes_to_unitSection (I := I) (J := J)
    C v o x hx)

#check S1268HDDLocalLatticeExact
#check S1268HDDLocalLatticeRequired
#check s1268ActualReading_eq_unitSection
#check s1268ActualReading_output_independent
#check s1268SHEExpression_eq_unitSection
#check s1268LocalizeSection_localizes_to_unitSection
#check s1268LocalizeSection_eq_unitSection_of_injective

end LeanFormal.IUT.XiFPaper.S1268HDDLatticeActual

end
