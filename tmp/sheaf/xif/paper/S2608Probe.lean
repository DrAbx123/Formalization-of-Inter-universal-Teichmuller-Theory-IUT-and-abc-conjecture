import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
abbrev T' : Type := Localization (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers S2057FiveDivisionField) (Submonoid.powers (c : ℤ)))
#synth Algebra C (NumberField.RingOfIntegers S2057FiveDivisionField)
#synth Algebra (NumberField.RingOfIntegers S2057FiveDivisionField) T'
#synth IsLocalization (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers S2057FiveDivisionField) (Submonoid.powers c)) T'
