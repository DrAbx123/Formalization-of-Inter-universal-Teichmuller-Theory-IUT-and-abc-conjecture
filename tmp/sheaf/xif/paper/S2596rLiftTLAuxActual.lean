import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2596cDenomClearActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596rLiftTLAuxActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2596cDenomClearActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
lemma aOL_unit :
    ∀ y : Submonoid.powers S2596cDenomClearActual.aOL,
      IsUnit (algebraMap S2594LP0PActual.OL S2057FiveDivisionField (y : S2594LP0PActual.OL)) := by
  intro y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : S2594LP0PActual.OL) S2596cDenomClearActual.aOL).mp y.2
  rw [← hn, map_pow]
  exact IsUnit.pow n (by
    have hne : algebraMap S2594LP0PActual.OL S2057FiveDivisionField
        S2596cDenomClearActual.aOL ≠ 0 := by
      intro h
      apply S2599TInstancesActual.Cden_OL_ne_zero
      exact IsFractionRing.injective S2594LP0PActual.OL S2057FiveDivisionField (by
        simpa [S2596cDenomClearActual.aOL] using h)
    exact isUnit_iff_ne_zero.mpr hne)
noncomputable def liftTL' :
    S2594LP0PActual.T →+* S2057FiveDivisionField :=
  IsLocalization.lift
    (M := Submonoid.powers S2596cDenomClearActual.aOL)
    (g := algebraMap S2594LP0PActual.OL S2057FiveDivisionField)
    aOL_unit
lemma liftTL'_comp :
    liftTL'.comp (algebraMap S2594LP0PActual.OL S2594LP0PActual.T) =
      algebraMap S2594LP0PActual.OL S2057FiveDivisionField :=
  IsLocalization.lift_comp aOL_unit
lemma liftTL_comp :
    S2599TInstancesActual.liftTL.comp
        (algebraMap S2594LP0PActual.OL S2594LP0PActual.T) =
      algebraMap S2594LP0PActual.OL S2057FiveDivisionField :=
  IsLocalization.lift_comp (fun y : Submonoid.powers S2596cDenomClearActual.aOL =>
    S2599TInstancesActual.gOL_unit y y.2)
#print axioms aOL_unit
#print axioms liftTL'_comp
#print axioms liftTL_comp
lemma liftTL'_eq : liftTL' = S2599TInstancesActual.liftTL := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers S2596cDenomClearActual.aOL)
  rw [liftTL'_comp, liftTL_comp]
local instance : IsScalarTower S2594LP0PActual.OL S2594LP0PActual.T S2057FiveDivisionField := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change algebraMap S2594LP0PActual.OL S2057FiveDivisionField x =
    S2599TInstancesActual.liftTL (algebraMap S2594LP0PActual.OL S2594LP0PActual.T x)
  rw [← liftTL'_eq]
  exact (RingHom.congr_fun liftTL'_comp x).symm
#print axioms liftTL'_eq
end LeanFormal.IUT.XiFPaper.S2596rLiftTLAuxActual
end

