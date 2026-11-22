import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.L
abbrev Fb : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
#synth Algebra Cb Lb
#synth Algebra Sb Lb
#synth IsScalarTower Cb Sb Lb
#synth IsScalarTower Cb Fb Lb
#synth Algebra Fb Lb
