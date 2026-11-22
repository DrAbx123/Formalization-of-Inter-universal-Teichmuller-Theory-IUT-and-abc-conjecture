import tmp.sheaf.xif.paper.S3128Stage1SHEHDDSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDSpecDownstreamActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHEHDDSpecDownstream_readout
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection :=
  (S3128Stage1SHEHDDSpec_ofCompatibility (I := I) (J := J) C).readout_eq_unit v o

theorem S3128Stage1SHEHDDSpecDownstream_localize_hdd
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
    (x : Fin C.hddLocalLattice.rank → (oneColumnStructure).localField v)
    (hx : x ∈ C.hddLocalLattice.lattice o v) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v
        (C.localizeSection v o ⟨x, hx⟩) :=
  (S3128Stage1SHEHDDSpec_ofCompatibility (I := I) (J := J) C).localize_hdd v o x hx

theorem S3128Stage1SHEHDDSpecDownstream_logShift
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) =
      Real.log (J.oneColumnScale m' j) :=
  (S3128Stage1SHEHDDSpec_ofCompatibility (I := I) (J := J) C).logShift m m' j

#check S3128Stage1SHEHDDSpecDownstream_readout
#check S3128Stage1SHEHDDSpecDownstream_localize_hdd
#check S3128Stage1SHEHDDSpecDownstream_logShift
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDSpecDownstreamActual