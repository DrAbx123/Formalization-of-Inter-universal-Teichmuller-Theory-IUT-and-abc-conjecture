import tmp.sheaf.xif.paper.S2595LResidueEquivActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2599TInstancesActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

abbrev L : Type := S2057FiveDivisionField
abbrev OL : Type := NumberField.RingOfIntegers L

/-- T = O_L[1/Cden]. -/
abbrev T : Type := Localization.Away (algebraMap C OL (Cden : C))

/-- The ring hom C -> T via O_L. -/
noncomputable def gCT : C →+* T := (algebraMap OL T).comp (algebraMap C OL)

lemma gCT_unit : ∀ y ∈ Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)),
    IsUnit (gCT y) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff z (c : ℤ)).mp hz
  rw [← hn]
  unfold gCT
  rw [map_pow, map_pow]
  have hc : (algebraMap ℤ C) c = (Cden : C) := rfl
  rw [hc]
  exact IsUnit.pow n (IsLocalization.map_units T
    ⟨algebraMap C OL (Cden : C), (Submonoid.mem_powers_iff _ _).mpr ⟨1, by rw [pow_one]⟩⟩)

/-- S -> T, by localizing C -> T. -/
noncomputable def liftST : S →+* T :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)))
    (g := gCT) (fun y => gCT_unit y.1 y.2)

noncomputable instance : Algebra S T := liftST.toAlgebra


/-- The ring hom O_L -> L. -/
noncomputable def gOL : OL →+* L := algebraMap OL L

lemma Cden_OL_ne_zero : algebraMap C OL (Cden : C) ≠ 0 := by
  intro h
  have hcomp : algebraMap C L (Cden : C) = 0 := by
    rw [IsScalarTower.algebraMap_apply C OL L, h, map_zero]
  have hinj : Function.Injective (algebraMap C L) := FaithfulSMul.algebraMap_injective C L
  exact (by
    have hc : (Cden : C) = 0 := hinj (by simpa using hcomp)
    exact Cden_ne_zero (by exact_mod_cast hc)) 

lemma gOL_unit : ∀ y ∈ Submonoid.powers (algebraMap C OL (Cden : C)),
    IsUnit (gOL y) := by
  intro y hy
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y (algebraMap C OL (Cden : C))).mp hy
  rw [← hn]
  unfold gOL
  rw [map_pow]
  apply IsUnit.pow
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact Cden_OL_ne_zero (by
    have hinj : Function.Injective (algebraMap OL L) :=
      IsIntegralClosure.algebraMap_injective OL ℤ L
    exact hinj (by simpa using h))

/-- T -> L, by localizing O_L -> L. -/
noncomputable def liftTL : T →+* L :=
  IsLocalization.lift (M := Submonoid.powers (algebraMap C OL (Cden : C)))
    (g := gOL) (fun y => gOL_unit y.1 y.2)

noncomputable instance : Algebra T L := liftTL.toAlgebra


end LeanFormal.IUT.XiFPaper.S2599TInstancesActual
end