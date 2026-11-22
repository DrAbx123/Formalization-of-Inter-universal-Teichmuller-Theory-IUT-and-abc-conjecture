import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDConsumerActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Consumer: an actual SHE/HDD fourth-joint compatibility yields that the
SHE readout equals the unit localization (readout_reference_compat +
indeterminacy_sync). -/
theorem S3128Stage1SHEHDD_readout_eq_unit
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection := by
  rw [C.readout_reference_compat, C.indeterminacy_sync]

/-- Consumer: the S1204 log-shift readout compatibility for the same source. -/
theorem S3128Stage1SHEHDD_logShift
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j) :=
  s1215LogShiftReadoutCompat_actual (I := I) (J := J) m m' j

#check S3128Stage1SHEHDD_readout_eq_unit
#check S3128Stage1SHEHDD_logShift
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDConsumerActualAdapted