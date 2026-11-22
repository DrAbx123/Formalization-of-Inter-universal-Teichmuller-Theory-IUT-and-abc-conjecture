/- P6 hCor312 supply: an actual G1/P8 upper-sources datum (hull normalization,
M >= 1, theta-hull data) yields the Cor 3.12 input for the actual Thm 1.10
display terms supplied by those sources. -/
import tmp.sheaf.xif.paper.Mzk1G1P8UpperActual
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8UpperActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (label : Type) [Fintype label] [Nonempty label]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Display terms supplied by an actual G1/P8 upper-sources datum. -/
noncomputable def p6TermsOfUpperSources
    (S : G1P8UpperSources places tuple label μ T) : Thm110DisplayTerms where
  l := (l.value : Real)
  dmod := 1
  logDFpd := 0
  logFFpd := 0
  eStar := 0
  etaPrm := 0
  logQ := nativeGlobalQPilotNormalizedLogMagnitude T

theorem certificate_q_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).q =
      Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)) := rfl

theorem certificate_logQ_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).logQ =
      nativeGlobalQPilotNormalizedLogMagnitude T := rfl

theorem certificate_dmod_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).dmod = 1 := rfl

theorem certificate_dFpd_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).dFpd = 1 := rfl

theorem certificate_fFpd_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).fFpd = 1 := rfl

theorem certificate_eStar_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).eStar = 0 := rfl

theorem certificate_etaPrm_eq (S : G1P8UpperSources places tuple label μ T) :
    (g1p8_S2953Certificate places tuple label μ T S).etaPrm = 0 := rfl

/-- Actual hCor312 supply for the display terms of an upper-sources datum. -/
theorem hCor312_of_upperSources
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (label : Type) [Fintype label] [Nonempty label]
    (μ : MeasureTheory.Measure (ArithmeticTensorTupleBlock places tuple))
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (PlacePartitionReduction.Bad (nativePlaceSelection T))]
    (S : G1P8UpperSources places tuple label μ T) :
    thm110Lhs (p6TermsOfUpperSources (l := l) S) ≤
      thm110Mid (p6TermsOfUpperSources (l := l) S) +
        thm110Cor312Gap (p6TermsOfUpperSources (l := l) S) := by
  have hMpos : 0 < nativeGlobalQPilotNormalizedLogMagnitude T := by
    have := S.M_ge_one
    linarith
  refine hCor312_of_actual_certificate (p6TermsOfUpperSources (l := l) S) l 1 1
    (g1p8_S2953Certificate places tuple label μ T S) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [certificate_q_eq S, Real.log_exp]
    exact neg_ne_zero.mpr hMpos.ne'
  · rw [certificate_logQ_eq S]
    exact hMpos
  · rfl
  · simp [p6TermsOfUpperSources]
  · simp [p6TermsOfUpperSources]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [p6TermsOfUpperSources]
    exact hMpos

#print axioms hCor312_of_upperSources

end LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SupplyActual
end
