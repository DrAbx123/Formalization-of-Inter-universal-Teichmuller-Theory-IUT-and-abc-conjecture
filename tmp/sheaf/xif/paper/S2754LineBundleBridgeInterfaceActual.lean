import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.S2743ConditionalHweightvolActual
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2754LineBundleBridgeInterfaceActual

variable {l : PrimeGeFive}

/-- New bridge carrier: the actual arithmetic line bundle. -/
abbrev S2754Carrier (l : PrimeGeFive) : Type :=
  SourceLineBundle (A := S2735Arithmetic l)

/-- qPilot line-bundle log volume as bridge region volume. -/
noncomputable def S2754RegionLogVolume (l : PrimeGeFive)
    (J : Nat -> Nat -> Nat -> Ideal (SourceOK (A := S2735Arithmetic l)))
    (a b c : Nat) : Real :=
  S2736QPilotLineBundleLogVolume (l := l) (J a b c)

/-- New bridge interface on the line-bundle carrier.  The hweightvol field is
the conditional S2736 statement; the height comparison is an explicit Prop gap
(no proof is stored), so the structure is not asserted nonempty. -/
structure S2754LineBundleBridgeInterface where
  J : Nat -> Nat -> Nat -> Ideal (SourceOK (A := S2735Arithmetic l))
  unitVol : Real
  hweightvol : S2736QPilotLineBundleHweightvol (l := l) J unitVol
  height_le_normalizedRegionVolume : Prop

theorem S2754_hweightvol (B : S2754LineBundleBridgeInterface (l := l)) :
    S2736QPilotLineBundleHweightvol (l := l) B.J B.unitVol :=
  B.hweightvol

theorem S2754_regionLogVolume_eq (B : S2754LineBundleBridgeInterface (l := l))
    (a b c : Nat) :
    S2754RegionLogVolume (l := l) B.J a b c =
      S2736QPilotLineBundleLogVolume (l := l) (B.J a b c) := rfl

end LeanFormal.IUT.XiFPaper.S2754LineBundleBridgeInterfaceActual
end
