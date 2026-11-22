/- Fixed-actual CTheta comparison against the Box(11) packet bound. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplaySourceConstantsActual
import tmp.sheaf.xif.paper.Mzk1P6PacketConsumerActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaFixedBoundActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplaySourceConstantsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketConsumerActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

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

noncomputable def fixedCThetaPaper : Real :=
  let D := p6DisplaySourceDataConstants T b
  CThetaPaper D.l D.logQ (D.dmod : Real) D.dFpd D.fFpd D.eStar D.etaPrm

noncomputable def fixedQAbs : Real :=
  let D := p6DisplaySourceDataConstants T b
  paperQAbsLog D.l D.logQ

/-- Fixed-actual CTheta comparison with the Box(11) packet bound. -/
theorem fixed_CTheta_ge_box
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu] :
    (-LocalFieldLogarithm.localNormOrder p D.varpi +
        ∑ i, LocalFieldLogarithm.localNormOrder p
          (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
      ∑ i ∈ D.exceptional, (3 + Real.log
        (LocalFieldLogarithm.logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) ≤
    fixedCThetaPaper T b * fixedQAbs T b := by
  have hbox := p6_packetHull_bound_consumer places tuple D
  linarith

#check fixedCThetaPaper
#check fixedQAbs
#check fixed_CTheta_ge_box

end LeanFormal.IUT.XiFPaper.Mzk1CThetaFixedBoundActual
end
