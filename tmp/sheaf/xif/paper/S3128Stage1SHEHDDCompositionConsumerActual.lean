import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDCompositionConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Composition consumer: SHE readout → SHE reading map → unit localization,
together with the actual log-shift and theta readout. -/
structure S3128Stage1SHEHDDCompositionData
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  readout_eq_reading :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).readingMap v o
  reading_eq_unit :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      (actualSHEOutput I).readingMap v o =
        (actualSHEOutput I).bundle.localization v unitSection
  readout_eq_unit :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  theta :
    ∀ (m : Int) (j : SignedLabel l.value),
      oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)

theorem S3128Stage1SHEHDDCompositionData_ofCompatibility
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDCompositionData (I := I) (J := J) C :=
  { readout_eq_reading := fun v o => C.readout_reference_compat v o
    reading_eq_unit := fun v o => C.indeterminacy_sync v o
    readout_eq_unit := fun v o => by
      rw [C.readout_reference_compat, C.indeterminacy_sync]
    logShift := fun m m' j =>
      s1215LogShiftReadoutCompat_actual (J := J) m m' j
    theta := fun m j => oneColumnLogReadout_theta J m j }

#check S3128Stage1SHEHDDCompositionData
#check S3128Stage1SHEHDDCompositionData_ofCompatibility
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDCompositionConsumerActual