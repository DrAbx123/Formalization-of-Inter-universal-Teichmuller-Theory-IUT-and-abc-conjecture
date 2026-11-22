import tmp.sheaf.xif.paper.S1385HDDHullDetActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132HDDHullDetReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.LocalFieldProductHull

universe u v ua uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-!
# Stage 1 fourth-joint actual hull readout

The Stage 1 fourth joint is `(hull+det) circ (SHE)` (IUT III, Theorem 3.11 and
Corollary 3.12 proof; formalization route note).  The hull side is read from the
actual HDD tensor-hull/det donors (S1300/S1356/S1385) and the SHE side from the
actual one-column theta readout (S1204); the determinant bookkeeping and the
SHE/HDD chain composition are the `shehdd` stream's S3134* files and are not
duplicated here.  No log-volume inequality is asserted.

* The S1215 HDD local lattice is, by construction of the actual HDD source, the
  actual product hull of the HDD allowed-image family transported by the
  source's uniform local-field identification.
* On each factor, under the actual nonarchimedean structure and the actual
  compactness of the allowed image, that hull is the actual integral span of the
  image (`s1300ActualIntegralSpan_eq_hull`); the compactness input is kept as an
  explicit hypothesis because the HDD source only supplies compactness of the
  closure of the image.
* The SHE one-column log readout is the logarithm of the actual source theta
  value at the shared boundary and is invariant under the vertical shift
  (S1204).
-/

/-- **HDD hull readout.**  The S1215 HDD local lattice at output `o` and finite
place `v` is exactly the actual product hull of the HDD allowed-image family
transported by the source's uniform local-field identification. -/
theorem hddLattice_eq_transportedHullReadout
    {I : Input Label Choice} (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
          fun i => D.localEquiv v i (x i)) ''
        (@LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)) :=
  D.toS1215_lattice_eq_hull o v

/-- **SHE one-column theta readout.**  The actual one-column log readout is the
logarithm of the actual source theta value at the shared boundary. -/
theorem oneColumnLogReadout_theta_readout
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (m : ℤ) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j) :=
  oneColumnLogReadout_theta J m j

/-- **SHE one-column vertical invariance readout.**  The actual one-column log
readout is invariant under the vertical shift. -/
theorem oneColumnLogReadout_vertical_readout
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (m : ℤ) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = oneColumnLogReadout J (m + 1) j :=
  oneColumnLogReadout_shift J m (m + 1) j

#check hddLattice_eq_transportedHullReadout
#check oneColumnLogReadout_theta_readout
#check oneColumnLogReadout_vertical_readout

end LeanFormal.IUT.XiFPaper.S3132HDDHullDetReadoutActual

end