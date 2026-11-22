import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596uHMTActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
lemma hMT' :
    Algebra.algebraMapSubmonoid S2599TInstancesActual.OL
        (Submonoid.powers (Cden : S2565ConcreteIntegralClosureCActual.C)) =
      Submonoid.powers
        (algebraMap S2565ConcreteIntegralClosureCActual.C S2599TInstancesActual.OL
          (Cden : S2565ConcreteIntegralClosureCActual.C)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y (Cden : S2565ConcreteIntegralClosureCActual.C)).mp hy
    exact ⟨n, by rw [map_pow]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(Cden : S2565ConcreteIntegralClosureCActual.C) ^ n, ⟨n, rfl⟩, by rw [map_pow]⟩
#print axioms hMT'
end LeanFormal.IUT.XiFPaper.S2596uHMTActual
end
