import tmp.sheaf.xif.paper.S2007F613FbarActual
import tmp.sheaf.xif.paper.S2596GaloisFixesCActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
noncomputable section
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2007F613FbarActual
namespace LeanFormal.IUT.XiFPaper.S2596bConcreteFixesCActual
#synth Field S1720Field
#synth Field S2057FiveDivisionField
local instance : NumberField S2057FiveDivisionField :=
  NumberField.of_module_finite (K := S1720Field) (L := S2057FiveDivisionField)
#synth NumberField S2057FiveDivisionField
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) (RingOfIntegers S2057FiveDivisionField) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
#synth IsGalois S1720Field S2057FiveDivisionField
theorem galois_fixes_algebraMap_C_Fp
    (sigma : Gal(S2057FiveDivisionField/S1720Field))
    (c : RingOfIntegers S1720Field) :
    sigma • algebraMap (RingOfIntegers S1720Field)
        (RingOfIntegers S2057FiveDivisionField) c =
      algebraMap (RingOfIntegers S1720Field)
        (RingOfIntegers S2057FiveDivisionField) c :=
  LeanFormal.IUT.XiFPaper.S2596GaloisFixesCActual.galois_fixes_algebraMap_C
    (K := S1720Field) (L := S2057FiveDivisionField) sigma c
#print axioms galois_fixes_algebraMap_C_Fp
end LeanFormal.IUT.XiFPaper.S2596bConcreteFixesCActual
end
