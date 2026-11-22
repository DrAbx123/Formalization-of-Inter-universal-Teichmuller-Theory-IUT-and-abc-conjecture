/- U-C K-side theta wiring: C2ThetaInput with kurt's K-side theta object
(ksThetaHullLogRoot) and the paper outer weight normDegreeWeight (f/[K:Q]).

Paper: IUT IV L977-1000 (normalized E-degree), L1045-1102 (fiber-normalized
letters), outer sum over v_Q accumulates the denominator to [F:Q].  Lead ruling
2026-11-17: outer weight = normDegreeWeight; gamma (nativeBadLocalWeight) is
SUPERSEDED for the C4/U-L main chain.

Inputs: kurt's Mzk1URThetaKSideActual (20:16:53) provides
ksThetaHullLogRoot_le_ucWeightedHpkt with weight normDegreeWeight.
hThetaLower is still a parameter (kurt's P5 lower bound is next); it is NOT
closed here and is documented as such.
-/
import tmp.sheaf.xif.paper.Mzk1UCHthetaWiringActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULStepVIIIActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCHthetaWiringKSideActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- paper-faithful M_paper := qPilotMagnitudePaper_v2/(2*l.value) (david 21:55:33).
The old qPilotMagnitudePaper (single F-lift order x K-lift weight) is LEGACY. -/
noncomputable def MpaperV2 : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]

/-- K-side C2 theta input: theta is kurt's K-side theta object
(ksThetaHullLogRoot), the upper bound uses the paper outer weight
normDegreeWeight, and the lower bound is the P5 bound in K-side form. -/
structure C2ThetaInputK (packetV : Bad (nativePlaceSelection T) → ℝ) where
  /-- the real read-off used in the sandwich -/
  theta : ℝ
  hThetaEq : theta = ksThetaHullLogRoot (l := l) T
  /-- P5 lower bound in K-side form (kurt's next step; parameter here) -/
  hThetaLower : -MpaperV2 (l := l) T ≤ theta
  /-- nz htheta with the paper outer weight normDegreeWeight -/
  hThetaUpper : ksThetaHullLogRoot (l := l) T
    ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (normDegreeWeight T) packetV

/-- construct the K-side C2 theta input from per-b hull bounds (upper bound
from kurt's ksThetaHullLogRoot_le_ucWeightedHpkt) plus the P5 lower bound. -/
noncomputable def c2ThetaInputK_of_hperB (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, ksThetaHullLog (l := l) T b ≤ packetV b)
    (hLower : -MpaperV2 (l := l) T ≤ ksThetaHullLogRoot (l := l) T) :
    C2ThetaInputK (l := l) T packetV where
  theta := ksThetaHullLogRoot (l := l) T
  hThetaEq := rfl
  hThetaLower := hLower
  hThetaUpper := ksThetaHullLogRoot_le_ucWeightedHpkt (l := l) T packetV hperB


/-- U-C C4 with the K-side theta object and the paper outer weight normDegreeWeight
(f/[K:Q]).  Same sandwich as uc_c4_paperConstants_of_p6, with M := M_paper :=
qPilotMagnitudePaper/(2*l.value) (paper |log q| = (1/2l) log(q), IUT IV L1359-1364)
and theta := ksThetaHullLogRoot, so the theta object and the outer weight are both
K-side (Lead ruling 2026-11-17; paper L977-1000, L1045-1102). -/
theorem uc_c4_of_hthetaKSide {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T),
      MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    [∀ b : Bad (nativePlaceSelection T),
      BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hC : C2ThetaInputK (l := l) T V)
    (hVB : ∀ b, V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T), normDegreeWeight T i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
          ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar + 2 * Real.log (l.value : ℝ) + 56
            - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
            + (20 / 3) *
              LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - MpaperV2 (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) := by
  have hP5 : -MpaperV2 (l := l) T ≤ ksThetaHullLogRoot (l := l) T := by
    simpa [hC.hThetaEq] using hC.hThetaLower
  have hw : ∀ b : Bad (nativePlaceSelection T), 0 ≤ normDegreeWeight T b :=
    fun b => LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.normDegreeWeight_nonneg
      (l := l) T b
  exact LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual.uc_c4_of_paperConstants
    (normDegreeWeight T) V B hw hVB hη0 hπ he (l.value : ℝ) eta_prm S_ar Q
    (MpaperV2 (l := l) T) d_mod (ksThetaHullLogRoot (l := l) T)
    hl heta hP5 hC.hThetaUpper hstepVIII

end LeanFormal.IUT.XiFPaper.Mzk1UCHthetaWiringKSideActual
end