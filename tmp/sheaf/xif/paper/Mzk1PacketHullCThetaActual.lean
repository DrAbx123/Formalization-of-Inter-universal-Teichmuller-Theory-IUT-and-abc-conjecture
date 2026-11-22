/- Instantiate the Box(11) RHS from packetHull_normalizedLogVolume_le_box
and feed it into the CThetaPaper algebra. -/
import tmp.sheaf.xif.paper.Mzk1CThetaUpperActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PacketHullCThetaActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1CThetaUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
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

/-- The explicit Box(11) RHS used by packetHull_normalizedLogVolume_le_box. -/
def boxRHS (D : PacketHullData places tuple (J := J) (E := E)) : Real :=
  (-LocalFieldLogarithm.localNormOrder p D.varpi +
      ∑ i, LocalFieldLogarithm.localNormOrder p
        (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
    ∑ i ∈ D.exceptional, (3 + Real.log
      (LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))

/-- Explicit CThetaPaper algebra with fFpd chosen from the Box bound. -/
theorem cThetaPaper_mul_eq_explicit
    (l : PrimeGeFive) (logQ B qAbs P : Real)
    (hP : P = paperQAbsLog l logQ) (hP0 : P ≠ 0) (hqAbs : qAbs ≠ 0) :
    CThetaPaper l logQ 0 1
        (Real.exp ((1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ +
          (B / qAbs + 1) * 4 * P / ((l.value : Real) + 1))) 0 0 * qAbs = B := by
  have hl1 : ((l.value : Real) + 1) ≠ 0 := by
    have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  unfold CThetaPaper cThetaBracket
  rw [Real.log_one, Real.log_exp]
  simp only [mul_zero, add_zero, zero_mul, zero_add]
  rw [← hP]
  field_simp [hP0, hqAbs, hl1]
  ring

/-- Actual Box(11) bound for the packet hull, with the CThetaPaper upper. -/
theorem packetHull_normalizedLogVolume_le_CThetaPaper
    (l : PrimeGeFive) (qAbs P logQ : Real)
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu]
    (hP : P = paperQAbsLog l logQ) (hP0 : P ≠ 0)
    (hqAbs : qAbs = |Real.log (Real.exp (-(paperQAbsLog l logQ)))|)
    (hqne : qAbs ≠ 0) :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤
      CThetaPaper l logQ 0 1
        (Real.exp ((1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ +
          (boxRHS (places := places) (tuple := tuple) D) / qAbs + 1) *
            4 * P / ((l.value : Real) + 1))) 0 0 * qAbs := by
  let B := boxRHS (places := places) (tuple := tuple) D
  have hBox := packetHull_normalizedLogVolume_le_box
    (places := places) (tuple := tuple) D
  have hEq := cThetaPaper_mul_eq_explicit l logQ B qAbs P hP hP0 hqne
  calc
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤ B := hBox
    _ = CThetaPaper l logQ 0 1
        (Real.exp ((1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ +
          (B / qAbs + 1) * 4 * P / ((l.value : Real) + 1))) 0 0 * qAbs := hEq.symm

#check boxRHS
#check cThetaPaper_mul_eq_explicit
#check packetHull_normalizedLogVolume_le_CThetaPaper

end LeanFormal.IUT.XiFPaper.Mzk1PacketHullCThetaActual
end
