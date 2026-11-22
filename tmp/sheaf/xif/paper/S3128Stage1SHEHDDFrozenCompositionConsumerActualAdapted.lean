import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFrozenCompositionConsumerActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S3128Stage1SHEHDDFrozenComposition
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) : Prop where
  readout_eq_unit :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
  localize_hdd :
    ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I)
      (x : Fin C.hddLocalLattice.rank → (oneColumnStructure).localField v)
      (hx : x ∈ C.hddLocalLattice.lattice o v),
      C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v
          (C.localizeSection v o ⟨x, hx⟩)
  logShift :
    ∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  frozen : HullDeterminantLogVolumeFrozenSpec

theorem S3128Stage1SHEHDDFrozenComposition_ofCompatibility
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDFrozenComposition (I := I) (J := J) C :=
  { readout_eq_unit := fun v o => by
      rw [C.readout_reference_compat, C.indeterminacy_sync]
    localize_hdd := fun v o x hx => C.localize_hdd_compat v o x hx
    logShift := fun m m' j =>
      s1215LogShiftReadoutCompat_actual (J := J) m m' j
    frozen := s1385FrozenSpec_actual }

#check S3128Stage1SHEHDDFrozenComposition
#check S3128Stage1SHEHDDFrozenComposition_ofCompatibility
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDFrozenCompositionConsumerActualAdapted