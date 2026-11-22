import tmp.sheaf.xif.paper.S3055PaperCor312Assembly
import tmp.sheaf.xif.paper.S2725GlobalThetaHullActual
import tmp.sheaf.xif.paper.GlobalHullPaperXiFActual
import tmp.sheaf.xif.paper.S1672GlobalThetaHullComparisonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3056XiFSignActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

/-- With signed scalars Q = -M and Theta = -H, the hxi inequality is exactly
H <= M, i.e. the global hull log-volume is at most the q-pilot magnitude. -/
theorem S3056_hxi_iff_hull_le_magnitude
    (H M : Real)
    (hH : S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        places tuple nu D = -H)
    (hQ : S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat = -M) :
    (S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat <=
      S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        places tuple nu D) ↔
    H <= M := by
  rw [hQ, hH]
  constructor <;> intro h <;> linarith

/-- Inclusion of the q-pilot image in the hull gives, contrapositively, that
hxi would force equality of the log-volumes, not a strict hull <= magnitude
from inclusion alone.  This records the sign direction without asserting any
missing global readout. -/
theorem S3056_hxi_forces_eq_of_inclusion
    (H M : Real)
    (hH : S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        places tuple nu D = -H)
    (hQ : S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat = -M)
    (hincl : M <= H) :
    (S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat <=
      S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        places tuple nu D) ->
    M = H := by
  intro h
  have hh : H <= M := (S3056_hxi_iff_hull_le_magnitude R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
    hcusCompat D places tuple nu H M hH hQ).mp h
  linarith

#check S3056_hxi_iff_hull_le_magnitude
#check S3056_hxi_forces_eq_of_inclusion

end LeanFormal.IUT.XiFPaper.S3056XiFSignActual
end