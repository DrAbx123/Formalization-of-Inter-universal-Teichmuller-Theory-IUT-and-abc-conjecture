import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPacketInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPreciseInterfaceActualAdapted
import tmp.sheaf.xif.paper.Mzk1AbsoluteKummerTrioActual

/-!
# Mzk1ThetaPilotKummerLinkActualAdapted (adapted copy, A475 reuse) — theta-pilot / absolute-Kummer link interface (iuti-ii)

STEP 0 prior-art: Mzk1KummerThetaInterfaceActual (Kummer/theta interface),
Mzk1ThetaPilotPacketInterfaceActual (theta-pilot packet re-exports),
Mzk1ThetaPilotPreciseInterfaceActualAdapted (X-mu precision interface),
Mzk1AbsoluteKummerTrioActual (absolute Kummer trio) -> REUSE.
This file bundles the theta-pilot precision data with the absolute Kummer layer in one typed
link interface and records the rows; the deep source-to-arithmetic comparison stays NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotKummerLinkActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPreciseInterfaceActualAdapted
open LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerTrioActual

/-- The theta-pilot / absolute-Kummer link interface at (K,n,hμ,G): the Kummer layer, the
theta quotient interface, the theta-pilot packet rows and the X-mu precision rows. -/
structure ThetaPilotKummerLink (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] where
  kummerLayer : KummerLayerInterface K n hμ
  thetaQuotient : ThetaQuotientInterface G
  packetRows : List (String × String × String)
  preciseRows : List (String × String × String)

/-- The link interface is inhabited by the tree assets for every datum. -/
noncomputable def thetaPilotKummerLink (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] : ThetaPilotKummerLink K n hμ G where
  kummerLayer := kummerLayerInterface K n hμ
  thetaQuotient := thetaQuotientInterface G
  packetRows := thetaPilotPacketRows
  preciseRows := thetaPilotPreciseRows

/-- The link interface is nonempty. -/
theorem thetaPilotKummerLink_nonempty (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] : Nonempty (ThetaPilotKummerLink K n hμ G) :=
  ⟨thetaPilotKummerLink K n hμ G⟩

/-- Link rows: (paper object, formal asset, status). -/
def thetaPilotKummerLinkRows : List (String × String × String) :=
  [ ("absolute Kummer layer", "KummerLayerInterface / absoluteKummerTrio", "TREE PROOF + interface"),
    ("theta quotient interface", "ThetaQuotientInterface", "TREE ASSET + interface"),
    ("theta-pilot packet rows", "thetaPilotPacketRows", "TREE PROOFS (re-exported)"),
    ("X-mu precision rows", "thetaPilotPreciseRows", "TREE ASSETS (re-exported)"),
    ("source-to-arithmetic comparison (paper)", "not asserted", "NAMED") ]

/-- The link row record has five rows. -/
theorem thetaPilotKummerLinkRows_length : thetaPilotKummerLinkRows.length = 5 := rfl

#check ThetaPilotKummerLink
#check thetaPilotKummerLink
#check thetaPilotKummerLink_nonempty
#check thetaPilotKummerLinkRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotKummerLinkActualAdapted
end
