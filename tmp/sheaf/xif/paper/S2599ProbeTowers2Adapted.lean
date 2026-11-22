import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
#synth IsScalarTower C OL L
#synth IsScalarTower C S T
#synth IsScalarTower C OL T
#synth IsScalarTower C S S1720Field
#synth IsScalarTower S T L
#synth FaithfulSMul C OL
#synth IsIntegralClosure OL C L
#synth IsFractionRing OL L
#synth IsLocalization (Submonoid.powers (Cden : C)) S
