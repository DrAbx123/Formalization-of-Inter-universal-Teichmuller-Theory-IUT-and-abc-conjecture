import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDLogShiftFieldConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDLogShiftField_holds
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) =
      Real.log (J.oneColumnScale m' j) :=
  C.logShift_readout_compat m m' j

theorem S3128Stage1SHEHDDLogShiftField_eq_source
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    C.logShift_readout_compat =
      (fun (m m' : Int) (j : SignedLabel l.value) =>
        s1215LogShiftReadoutCompat_actual (J := J) m m' j) := by
  funext m m' j
  exact Subsingleton.elim _ _

#check S3128Stage1SHEHDDLogShiftField_holds
#check S3128Stage1SHEHDDLogShiftField_eq_source
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDLogShiftFieldConsumerActual