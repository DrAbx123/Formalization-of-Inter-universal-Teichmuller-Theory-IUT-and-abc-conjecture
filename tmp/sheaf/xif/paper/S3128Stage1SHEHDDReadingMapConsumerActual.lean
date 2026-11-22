import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDReadingMapConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDReadingMap_readout
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).readingMap v o :=
  C.readout_reference_compat v o

theorem S3128Stage1SHEHDDReadingMap_chain
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).readingMap v o ∧
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection := by
  refine ⟨C.readout_reference_compat v o, ?_⟩
  exact C.indeterminacy_sync v o

#check S3128Stage1SHEHDDReadingMap_readout
#check S3128Stage1SHEHDDReadingMap_chain
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDReadingMapConsumerActual