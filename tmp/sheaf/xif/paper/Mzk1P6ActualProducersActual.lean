/- P6 actual producers: P14, qHat, packet volume, Thm110DisplayTerms constructor
and the display consumer chain.  All are actual proofs/d constructions from the
tree; no interface-only placeholders. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14P14iiActualActual
import tmp.sheaf.xif.paper.Mzk1P2QHatNormCoherenceProofActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticPacketVolume
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14ActualHBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14P14iiActualActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceProofActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u v

/-- P6 actual P14 producer (Prop 1.4(ii)): the actual log-volume ratio formula. -/
theorem p6_P14Producer
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]
    (hp : (1 : ℝ) < (p : ℝ)) (d e f m s : ℕ)
    (he : 1 ≤ e) (hf : 1 ≤ f) (hd : d = e * f)
    (μL μO μΛ : ℝ) (hμL : 0 < μL) (hμO : 0 < μO)
    (hexp : actualGammaH (K := K) (p := p) + f + m = s * d)
    (hμΛ : μΛ = (p : ℝ) ^ actualGammaH (K := K) (p := p) * μO)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ) :
    (Real.log μL - Real.log μO) / (d : ℝ) =
      -(((f + m : ℝ) / (e * f : ℝ)) * Real.log (p : ℝ)) :=
  p14ii_logVolume_actual (K := K) (p := p) hp d e f m s he hf hd
    μL μO μΛ hμL hμO hexp hμΛ hL

/-- P6 actual qHat norm coherence producer. -/
theorem p6_actualQHatNorm
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    ‖c0QHat T b‖ = qVFamNormalizedNorm T b :=
  qHatNormCoherence_proved (T := T) (b := b)

/-- P6 actual packet-volume producer (nonnegativity). -/
theorem p6_packetVolume_nonneg (K : Type u) [Field K] [NumberField K]
    (p : Nat) [Fact p.Prime] (ι : Type v) [Finite ι] :
    0 ≤ fullPrimeArithmeticHullPacketLogVolume K p ι :=
  fullPrimeArithmeticHullPacketLogVolume_nonneg K p ι

/-- P6 actual Thm 1.10 display-terms constructor. -/
def p6_displayTermsOf
    (l dmod logDFpd logFFpd eStar etaPrm logQ : ℝ) : Thm110DisplayTerms where
  l := l
  dmod := dmod
  logDFpd := logDFpd
  logFFpd := logFFpd
  eStar := eStar
  etaPrm := etaPrm
  logQ := logQ

/-- P6 actual display consumer chain: the Thm 1.10 slack inequality. -/
theorem p6_thm110_slack (T : Thm110DisplayTerms) (hl : 7 ≤ T.l)
    (hd : 1 ≤ T.dmod) (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T :=
  thm110_slack_of_hCor312 T hl hd hS hE hCor312

#print axioms p6_P14Producer
#print axioms p6_actualQHatNorm
#print axioms p6_packetVolume_nonneg
#print axioms p6_thm110_slack

end LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual
end
