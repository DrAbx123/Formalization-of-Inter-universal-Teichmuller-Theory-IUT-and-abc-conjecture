import tmp.sheaf.xif.paper.PaperThetaHullThenAverageActual
import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

/-! # INVALID SURROGATE: Paper label-hull log-volume versus q-pilot local scalar

STATUS: the per-label hull below is built on the constant-tuple possible image
`paperThetaPilotPointAt`, which places the same theta value in every F_l^x
component.  This is not the paper possible image (which uses the j-th
F_l^x component / F_l^x orbit).  `PaperLabelHullHaarComputed` is therefore NOT
paper-faithful; do not use this file to derive hull = q-pilot equality.
See PaperThetaHullEqQPilotAudit.md.

Original doc:

At the F_l^x label j = 1, the q-pilot local signed scalar with the
SourceVolumeIndex cardinality factor is

  qPilotLocalSignedScalar q
    = card(SourceVolumeIndex l) * log(paperThetaValue q 1).

The paper per-label hull log-volume is

  paperLabelHullLogVolume q 1
    = log(paperThetaPilotHaar (paperLabelHull q 1)).toReal.

The actual Haar log-volume is constructed but its numeric value is not
computed.  This file records the exact equality gap:

  PaperLabelHullHaarComputed q
    := (paperThetaPilotHaar (paperLabelHull q 1)).toReal
         = (paperThetaValue q 1) ^ card(SourceVolumeIndex l).

Conditional on that exact Haar computation, the j = 1 equality is proved.
Conditional on the per-label hull log-volumes being the same copy, the F_l^x
average is proved equal to the j = 1 local scalar.  No equality is asserted
unconditionally and no inequality is asserted.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaHullEqQPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaHullThenAverageActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (q : Real)

/-- The actual q-pilot local signed scalar at j = 1, with the same
SourceVolumeIndex cardinality factor. -/
noncomputable def qPilotLocalSignedScalar : Real :=
  (Fintype.card (SourceVolumeIndex l) : Real) *
    Real.log (paperThetaValue (l := l) q (1 : ProcessionLabel l))

/-- Exact Haar computation gap at j = 1. -/
def PaperLabelHullHaarComputed : Prop :=
  (paperThetaPilotHaar (l := l)
    (paperLabelHull (l := l) q (1 : ProcessionLabel l) :
      Set (PaperThetaPilotPoint (l := l)))).toReal =
    (paperThetaValue (l := l) q (1 : ProcessionLabel l)) ^
      Fintype.card (SourceVolumeIndex l)

/-- Conditional j = 1 equality: if the exact Haar value is computed, the
per-label hull log-volume equals the q-pilot local signed scalar. -/
theorem paperLabelHullLogVolume_one_eq_qPilotLocalSignedScalar
    (h : PaperLabelHullHaarComputed (l := l) q) :
    paperLabelHullLogVolume (l := l) q (1 : ProcessionLabel l) =
      qPilotLocalSignedScalar (l := l) q := by
  unfold paperLabelHullLogVolume qPilotLocalSignedScalar
  rw [h, Real.log_pow]

/-- Exact per-label hull-copy condition: all F_l^x labels have the same hull
log-volume as the j = 1 copy. -/
def PaperLabelHullCopiesSame : Prop :=
  forall j : ProcessionLabel l,
    paperLabelHullLogVolume (l := l) q j =
      paperLabelHullLogVolume (l := l) q (1 : ProcessionLabel l)

/-- Conditional F_l^x average equality: if all hull copies have the same
log-volume, the hull-then-average scalar equals the j = 1 local scalar. -/
theorem paperHullThenAverage_eq_one_of_copiesSame
    (hcopy : PaperLabelHullCopiesSame (l := l) q)
    (hcard : (Fintype.card (ProcessionLabel l) : Real) <> 0) :
    paperHullThenAverage (l := l) q =
      paperLabelHullLogVolume (l := l) q (1 : ProcessionLabel l) := by
  unfold paperHullThenAverage
  rw [Finset.sum_congr rfl (fun j _ => hcopy j)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hcard]

/-- Combined conditional statement: exact Haar computation plus identical hull
copies gives the F_l^x average equal to the q-pilot local signed scalar. -/
theorem paperHullThenAverage_eq_qPilotLocalSignedScalar
    (hhaar : PaperLabelHullHaarComputed (l := l) q)
    (hcopy : PaperLabelHullCopiesSame (l := l) q)
    (hcard : (Fintype.card (ProcessionLabel l) : Real) <> 0) :
    paperHullThenAverage (l := l) q =
      qPilotLocalSignedScalar (l := l) q := by
  rw [paperHullThenAverage_eq_one_of_copiesSame (l := l) q hcopy hcard,
    paperLabelHullLogVolume_one_eq_qPilotLocalSignedScalar (l := l) q hhaar]

/-- Exact unconditional gap: the only missing data for the j = 1 equality is
the actual Haar value computation. -/
def PaperThetaHullEqQPilotGap : Prop :=
  PaperLabelHullHaarComputed (l := l) q

end LeanFormal.IUT.XiFPaper.PaperThetaHullEqQPilotActual

end
