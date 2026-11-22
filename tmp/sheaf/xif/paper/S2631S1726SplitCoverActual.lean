import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Pi

noncomputable section
set_option maxHeartbeats 4000000

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

namespace LeanFormal.IUT.XiFPaper.S2631S1726SplitCoverActual

abbrev S1726SplitAlgebra : Type :=
  TensorProduct S1726K S1726CoordinateRing S1726FiniteEtaleAlgebra

abbrev S1726SplitScheme : Scheme :=
  Spec (CommRingCat.of S1726SplitAlgebra)

abbrev S1726SplitOver : SchemeOverField S1726K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726SplitAlgebra)))

noncomputable def S1726SplitMap : S1726SplitOver ⟶ S1726AffineOver :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (algebraMap S1726CoordinateRing S1726SplitAlgebra)))
    (by
      change Spec.map (CommRingCat.ofHom (algebraMap S1726CoordinateRing S1726SplitAlgebra)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing)) =
        Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726SplitAlgebra))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])


instance : Algebra.Etale S1726K S1726FiniteEtaleAlgebra := by
  let e : S1726FiniteEtaleAlgebra ≃ₐ[S1726K] (Fin 2 → S1726K) :=
  { toFun := fun p i => if i = 0 then p.1 else p.2
    invFun := fun f => (f 0, f 1)
    left_inv := by intro p; ext <;> simp
    right_inv := by intro f; funext i; fin_cases i <;> simp
    map_mul' := by intro x y; ext i <;> fin_cases i <;> simp
    map_add' := by intro x y; ext i <;> fin_cases i <;> simp
    commutes' := by intro r; ext i <;> fin_cases i <;> simp }
  exact Algebra.Etale.of_equiv e.symm

instance : Module.Finite S1726K S1726FiniteEtaleAlgebra := inferInstance

instance : Algebra.Etale S1726CoordinateRing S1726SplitAlgebra :=
  Algebra.Etale.baseChange
    (R := S1726K) (A := S1726FiniteEtaleAlgebra)
    (B := S1726CoordinateRing)

instance : Module.Finite S1726CoordinateRing S1726SplitAlgebra := inferInstance

theorem S1726SplitMap_isFinite :
    AlgebraicGeometry.IsFinite S1726SplitMap.left := by
  change AlgebraicGeometry.IsFinite
    (Spec.map (CommRingCat.ofHom
      (algebraMap S1726CoordinateRing S1726SplitAlgebra)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap (A := S1726CoordinateRing)
    (B := S1726SplitAlgebra).mpr inferInstance

theorem S1726SplitMap_etale :
    AlgebraicGeometry.Etale S1726SplitMap.left := by
  change AlgebraicGeometry.Etale
    (Spec.map (CommRingCat.ofHom
      (algebraMap S1726CoordinateRing S1726SplitAlgebra)))
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)
    (Q := RingHom.Etale)]
  exact RingHom.etale_algebraMap (R := S1726CoordinateRing)
    (S := S1726SplitAlgebra).mpr inferInstance

#check S1726SplitMap_isFinite
#check S1726SplitMap_etale
#print axioms S1726SplitMap_isFinite
#print axioms S1726SplitMap_etale

#check S1726SplitAlgebra
#check S1726SplitScheme
#check S1726SplitOver
#check S1726SplitMap

end LeanFormal.IUT.XiFPaper.S2631S1726SplitCoverActual
end
