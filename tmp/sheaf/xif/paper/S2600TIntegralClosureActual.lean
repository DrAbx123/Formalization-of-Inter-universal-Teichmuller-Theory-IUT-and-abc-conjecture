import tmp.sheaf.xif.paper.S2599TInstancesActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual

/-- The localization submonoids agree. -/
lemma N_eq_powers :
    Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)) =
      Submonoid.powers (Cden : C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y (c : ℤ)).mp hy
    rw [← hn, map_pow]
    exact (Submonoid.mem_powers_iff _ _).mpr ⟨n, by
      rw [show algebraMap ℤ C c = (Cden : C) from rfl]⟩
  · rintro ⟨n, hn⟩
    refine ⟨(c : ℤ) ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩, ?_⟩
    rw [map_pow, show algebraMap ℤ C c = (Cden : C) from rfl]
    exact hn



lemma isScalarTower_CST : IsScalarTower C S T := by
  letI : Algebra C T := gCT.toAlgebra
  letI : SMul C T := Algebra.toSMul
  change @IsScalarTower C S T (Algebra.toSMul : SMul C S) (Algebra.toSMul : SMul S T) (gCT.toAlgebra.toSMul : SMul C T)
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change gCT x = algebraMap S T (algebraMap C S x)
  rw [show algebraMap S T (algebraMap C S x) = liftST (algebraMap C S x) from rfl]
  exact (IsLocalization.lift_eq (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (c : ℤ)))
    (g := gCT) (fun y => gCT_unit y.1 y.2) x).symm


end LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual
end