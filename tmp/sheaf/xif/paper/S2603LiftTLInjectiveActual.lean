import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2600TIntegralClosureActual
import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2603LiftTLInjectiveActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

lemma powers_r_nonZeroDivisors :
    Submonoid.powers (algebraMap C OL (Cden : C)) ≤ nonZeroDivisors OL :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (by simpa using Cden_OL_ne_zero)

lemma algebraMap_OL_T_injective :
    Function.Injective (algebraMap OL T) :=
  IsLocalization.injective T (M := Submonoid.powers (algebraMap C OL (Cden : C))) powers_r_nonZeroDivisors

lemma gOL_injective : Function.Injective gOL :=
  IsIntegralClosure.algebraMap_injective (A := OL) (R := ℤ) (B := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.L)

lemma liftTL_injective : Function.Injective liftTL := by
  change Function.Injective (IsLocalization.lift (fun y => gOL_unit y.1 y.2))
  rw [IsLocalization.lift_injective_iff (fun y => gOL_unit y.1 y.2)]
  intro x y
  constructor
  · intro h
    have hxy : x = y := algebraMap_OL_T_injective h
    rw [hxy]
  · intro h
    have hxy : x = y := gOL_injective h
    rw [hxy]

end LeanFormal.IUT.XiFPaper.S2603LiftTLInjectiveActual
end