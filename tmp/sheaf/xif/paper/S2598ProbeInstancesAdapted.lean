import tmp.sheaf.xif.paper.S2597RootSetEquivActual
import tmp.sheaf.xif.paper.S2595LResidueEquivActual
import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
#synth IsIntegralClosure T S S1720Field
#synth IsIntegralClosure T S S2057FiveDivisionField
#synth Algebra S T
#synth IsScalarTower S S1720Field S2057FiveDivisionField
#synth IsFractionRing S S1720Field
#synth FaithfulSMul S S2057FiveDivisionField