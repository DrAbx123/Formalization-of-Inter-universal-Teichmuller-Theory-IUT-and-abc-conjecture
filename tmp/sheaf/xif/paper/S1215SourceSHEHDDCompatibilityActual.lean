import tmp.sheaf.xif.paper.SHEOutputActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

-- S1215: exact target structure for the fourth joint, SourceSHEHDDCompatibility.
-- Fields are actual donor-backed data/equalities; no weak Prop, no inhabitant.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Exact HDD local lattice data: rank plus the actual local field family of
the 1-column structure. -/
structure S1215HDDLocalLattice where
  rank : Nat
  lattice : Theorem311Output I →
    (v : NumberField.FinitePlace ℚ) →
      Set (Fin rank → (oneColumnStructure).localField v)

/-- Exact fourth-joint target.  The actual SHEOutputActual donor supplies the
output, 1-column bundle, reading map and unit-section localization; the
actual SourceSharedBoundary donor supplies oneColumnScale for the log
shift field. -/
structure SourceSHEHDDCompatibility where
  hddLocalLattice : S1215HDDLocalLattice (I := I)
  sheLocalization :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I)
  localizeSection : ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
    hddLocalLattice.lattice o v → (actualSHEOutput I).bundle.total
  localize_hdd_compat : ∀ (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) (x : Fin hddLocalLattice.rank →
      (oneColumnStructure).localField v)
    (hx : x ∈ hddLocalLattice.lattice o v),
    sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v
        (localizeSection v o ⟨x, hx⟩)
  readout_reference_compat : ∀ (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I),
    sheLocalization.expression v o = (actualSHEOutput I).readingMap v o
  logShift_readout_compat : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log ((J.oneColumnScale m j)) =
      Real.log ((J.oneColumnScale m' j))
  indeterminacy_sync : ∀ (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I),
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection

/-- The log-shift field is not a new gap: it is the actual S1204 readout
shift theorem for the same SourceSharedBoundary donor. -/
theorem s1215LogShiftReadoutCompat_actual
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j) :=
  by simpa [oneColumnLogReadout] using oneColumnLogReadout_shift J m m' j

/-- The indeterminacy-sync field for the actual output is actual (rfl via the
1-column unit-section reading). -/
theorem s1215IndeterminacySync_actual
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  rfl

#check S1215HDDLocalLattice
#check SourceSHEHDDCompatibility
#check s1215LogShiftReadoutCompat_actual
#check s1215IndeterminacySync_actual

end LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

end