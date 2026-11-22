import tmp.sheaf.xif.paper.S1961LocalGlobalBridgeActual

open LeanFormal.IUT.XiFPaper.S1961LocalGlobalBridgeActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

#check @bridgePacket
#check @bridgePacket_eq_paperGlobalLogShellPacket
#check @s1961_finiteLogShell_eq_bridge
#check @s1961_paperFullLogKummerUQ_finiteLogShell_eq_bridge
#check @s1961_paperFullLogKummerUQ_finiteLogShell_eq_span_actualLogShell

example (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).finiteLogShell = bridgePacket :=
  s1961_paperFullLogKummerUQ_finiteLogShell_eq_bridge D

example (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).finiteLogShell =
      Submodule.span ℚ (Set.pi Set.univ (fun v => realBridgeImage v)) :=
  s1961_paperFullLogKummerUQ_finiteLogShell_eq_span_actualLogShell D
