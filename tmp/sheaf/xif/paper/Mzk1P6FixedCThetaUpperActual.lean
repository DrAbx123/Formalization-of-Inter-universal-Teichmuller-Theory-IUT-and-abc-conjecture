/- Fixed actual P6 constants: CThetaPaper upper via Box(11) packet bound. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplaySourceConstantsActual
import tmp.sheaf.xif.paper.Mzk1P6PacketConsumerActual
import tmp.sheaf.xif.paper.Mzk1CThetaUpperActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6FixedCThetaUpperActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplaySourceConstantsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketConsumerActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Fixed actual P6 CThetaPaper (dmod, dFpd, fFpd, eStar, etaPrm, logQ from the
actual P6 source constants). -/
noncomputable def p6FixedCThetaPaper {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  let D := p6DisplaySourceDataConstants T b
  CThetaPaper D.l D.logQ (D.dmod : Real) D.dFpd D.fFpd D.eStar D.etaPrm

/-- Fixed actual qAbs = paperQAbsLog of the actual qHat normalized log. -/
noncomputable def p6FixedQAbs {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  let D := p6DisplaySourceDataConstants T b
  paperQAbsLog D.l D.logQ

/-- Box(11) bound for the packet hull. -/
theorem p6_box_bound
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu] :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤
      (-LocalFieldLogarithm.localNormOrder p D.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ D.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  p6_packetHull_bound_consumer places tuple D

/-- Fixed-actual CThetaPaper upper for the packet hull volume. -/
theorem p6_fixed_cThetaUpper
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu] :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤
      p6FixedCThetaPaper T b * p6FixedQAbs T b := by
  have hbox := p6_box_bound places tuple D
  have hC : p6FixedCThetaPaper T b * p6FixedQAbs T b =
      (-LocalFieldLogarithm.localNormOrder p D.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ D.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) := by
    rfl
  linarith

#check p6FixedCThetaPaper
#check p6FixedQAbs
#check p6_box_bound
#check p6_fixed_cThetaUpper

end LeanFormal.IUT.XiFPaper.Mzk1P6FixedCThetaUpperActual
end
