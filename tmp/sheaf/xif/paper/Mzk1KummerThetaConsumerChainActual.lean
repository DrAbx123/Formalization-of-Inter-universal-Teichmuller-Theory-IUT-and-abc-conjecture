import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPacketInterfaceActual
import tmp.sheaf.xif.paper.Mzk1AbsoluteKummerTrioActual

/-!
# Mzk1KummerThetaConsumerChainActual — consumer theorems over the Kummer/theta interface
assets (IKT/TRIB/TPI, all EXIT0). Composed projections only; no new axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerThetaConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerTrioActual

/-- Consumer: the absolute Kummer quotient map is injective (via IKT re-export). -/
theorem consumer_kummer_quotient_injective {K : Type} [Field K] [CharZero K] {n : ℕ}
    [NeZero n] (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Function.Injective (AbsoluteKummerQuotient.absoluteKummerMapQuotient hμ) :=
  kummerQuotient_injective hμ

/-- Consumer: the theta quotient interface has surjective theta-to-elliptic map. -/
theorem consumer_theta_surjective (G : Type) [Group G] :
    Function.Surjective (thetaQuotientInterface G).thetaToElliptic :=
  (thetaQuotientInterface G).thetaToElliptic_surjective

/-- Consumer: the theta-pilot tensor generator lies in the IQ packet (TPI re-export). -/
theorem consumer_thetaPilot_generator_mem (D : SourceLogShellDatum) (j : ℕ)
    (f : (i : Capsule j) → D.K) (hf : ∀ i, f i ∈ D.logShell) :
    sourceLogShellTensorGenerator D j f ∈ sourceThetaPilotIQPacket D j :=
  tensorGenerator_mem_iqPacket D j f hf

/-- Consumer bundle: Kummer layer + theta quotient interface, inhabited. -/
structure KummerThetaConsumer (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type) [Group G] where
  kummerLayer : KummerLayerInterface K n hμ
  thetaQuotient : ThetaQuotientInterface G

/-- The consumer bundle is inhabited. -/
def kummerThetaConsumer (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type) [Group G] : KummerThetaConsumer K n hμ G where
  kummerLayer := kummerLayerInterface K n hμ
  thetaQuotient := thetaQuotientInterface G

/-- Consumer bundle nonempty. -/
theorem kummerThetaConsumer_nonempty (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type) [Group G] : Nonempty (KummerThetaConsumer K n hμ G) :=
  ⟨kummerThetaConsumer K n hμ G⟩

#check consumer_kummer_quotient_injective
#check consumer_theta_surjective
#check consumer_thetaPilot_generator_mem
#check kummerThetaConsumer_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1KummerThetaConsumerChainActual
end
