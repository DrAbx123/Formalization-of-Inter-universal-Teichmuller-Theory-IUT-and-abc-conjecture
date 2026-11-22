import tmp.sheaf.xif.paper.Mzk1HodgeTheaterInterfaceActual
import tmp.sheaf.xif.paper.Mzk1FrobenioidInterfaceActual
import tmp.sheaf.xif.paper.Mzk1KummerInterfaceActual
import tmp.sheaf.xif.paper.Mzk1InitialThetaInterfaceActual
import tmp.sheaf.xif.paper.Mzk1K1K2InterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1PreObjectInterfacesBundleActualAdapted (adapted copy, A475 reuse) — pre-object interface bundle (reuse)

Reuses the EXIT0 interface files for the Hodge theater, Frobenioid carrier,
Kummer map data, initial theta data and K1/K2 data, bundling them with
projections.  These are interfaces only; no paper object is constructed.
No closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PreObjectInterfacesBundleActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1HodgeTheaterInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1FrobenioidInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1InitialThetaInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1K1K2InterfaceActual

universe u v w

/-- Bundle of the five pre-object interfaces. -/
structure PreObjectInterfacesBundle (Source Target Carrier S T Index Carrier2 Packet : Type*)
    where
  hodge : HodgeTheaterData Source Target
  frob : FrobenioidCarrier Carrier
  kummer : KummerMapData S T
  initialTheta : InitialThetaData Index Carrier2
  k1k2 : K1K2Data Packet

theorem preBundle_hodge_link {Source Target Carrier S T Index Carrier2 Packet : Type*}
    (B : PreObjectInterfacesBundle Source Target Carrier S T Index Carrier2 Packet) :
    B.hodge.link B.hodge.src = B.hodge.link B.hodge.src :=
  rfl

theorem preBundle_frob_logMap {Source Target Carrier S T Index Carrier2 Packet : Type*}
    (B : PreObjectInterfacesBundle Source Target Carrier S T Index Carrier2 Packet)
    (x : Carrier) : B.frob.logMap x = B.frob.logMap x :=
  rfl

theorem preBundle_kummer_section {Source Target Carrier S T Index Carrier2 Packet : Type*}
    (B : PreObjectInterfacesBundle Source Target Carrier S T Index Carrier2 Packet)
    (x : S) : B.kummer.section_ (B.kummer.kummer x) = x :=
  B.kummer.section_kummer x

theorem preBundle_initialTheta_mem {Source Target Carrier S T Index Carrier2 Packet : Type*}
    (B : PreObjectInterfacesBundle Source Target Carrier S T Index Carrier2 Packet) :
    B.initialTheta.family B.initialTheta.distinguished =
      B.initialTheta.family B.initialTheta.distinguished :=
  B.initialTheta.distinguished_mem

def preObjectInterfacesRows : List (String × String × String) :=
  [ ("bundle", "PreObjectInterfacesBundle", "DEF (reuses EXIT0 interfaces)"),
    ("projections", "preBundle_hodge_link/frob_logMap/kummer_section/initialTheta_mem", "PROVED/re-export"),
    ("scope", "interfaces only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem preObjectInterfacesRows_length : preObjectInterfacesRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PreObjectInterfacesBundleActualAdapted

end
