import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDCompatibilityConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Upstream consumer of the SHE/HDD fourth-joint actual compatibility:
readout = unit localization, HDD localization compatibility, log-shift and
theta readout. Does not import U3. -/
structure S3128Stage1SHEHDDCompatibilityConsumerSpec
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
  theta :
    ∀ (m : Int) (j : SignedLabel l.value),
      oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)

theorem S3128Stage1SHEHDDCompatibilityConsumerSpec_ofCompatibility
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3128Stage1SHEHDDCompatibilityConsumerSpec (I := I) (J := J) C :=
  { readout_eq_unit := fun v o => by
      rw [C.readout_reference_compat, C.indeterminacy_sync]
    localize_hdd := fun v o x hx => C.localize_hdd_compat v o x hx
    logShift := fun m m' j =>
      s1215LogShiftReadoutCompat_actual (J := J) m m' j
    theta := fun m j => oneColumnLogReadout_theta J m j }

#check S3128Stage1SHEHDDCompatibilityConsumerSpec
#check S3128Stage1SHEHDDCompatibilityConsumerSpec_ofCompatibility
end LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDCompatibilityConsumerActual