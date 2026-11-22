import tmp.sheaf.xif.paper.S2610TTPrimeActual
import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596zTPrimeBatch1Actual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
noncomputable instance instAlgTL' : Algebra S2610TTPrimeActual.T' S2057FiveDivisionField :=
  (S2599TInstancesActual.liftTL.comp S2610TTPrimeActual.eTT'.symm.toRingHom).toAlgebra
lemma hCS :
    Algebra.algebraMapSubmonoid S2565ConcreteIntegralClosureCActual.C
        (Submonoid.powers (S2565ConcreteIntegralClosureCActual.c : ℤ)) =
      Submonoid.powers
        (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rfl
noncomputable instance instIsLocS :
    IsLocalization
      (Submonoid.powers
        (S2562HZcMonicCActual.Cden : S2565ConcreteIntegralClosureCActual.C))
      S2565ConcreteIntegralClosureCActual.S := by
  rw [← hCS]
  infer_instance
#print axioms hCS
end LeanFormal.IUT.XiFPaper.S2596zTPrimeBatch1Actual
end
