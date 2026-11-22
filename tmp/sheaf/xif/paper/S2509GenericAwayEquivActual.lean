import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Lemmas

noncomputable section
set_option maxHeartbeats 2000000

open MvPolynomial

namespace S2509GenericAwayEquiv

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K0 : Type) [Field K0]

abbrev A : Type := MvPolynomial (Fin 2) K0
abbrev AwayRing : Type := HomogeneousLocalization.Away
  (MvPolynomial.homogeneousSubmodule (Fin 2) K0) (MvPolynomial.X 1)
abbrev Poly1 : Type := MvPolynomial (Fin 1) K0

noncomputable def phi : A K0 →+* Poly1 K0 :=
  MvPolynomial.eval₂Hom (algebraMap K0 (Poly1 K0))
    (fun i : Fin 2 => if i = 1 then 1 else MvPolynomial.X 0)

theorem phi_X1 : phi K0 (MvPolynomial.X 1) = 1 := by
  simp [phi]

#check phi
#check phi_X1
#check AwayRing
#check HomogeneousLocalization.Away.mk
#check HomogeneousLocalization.fromZeroRingHom

noncomputable def fRing : AwayRing K0 →+* Poly1 K0 :=
  (Localization.awayLift (phi K0) (MvPolynomial.X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [phi_X1 K0]; simp⟩)).comp
    (algebraMap (AwayRing K0) (Localization.Away (MvPolynomial.X 1)))

#check fRing

noncomputable def cAway (a : K0) : AwayRing K0 :=
  HomogeneousLocalization.Away.mk
    (MvPolynomial.homogeneousSubmodule (Fin 2) K0)
    (d := 1) (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X _ _) 0
    (MvPolynomial.C a) (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa using MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K0) a)

noncomputable def constAway : K0 →+* AwayRing K0 where
  toFun := cAway K0
  map_one' := by
    ext
    simp [cAway, HomogeneousLocalization.Away.val_mk]
  map_mul' a b := by
    ext
    simp [cAway, HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  map_zero' := by
    ext
    simp [cAway, HomogeneousLocalization.Away.val_mk, Localization.mk_zero]
  map_add' a b := by
    ext
    simp [cAway, HomogeneousLocalization.Away.val_mk, Localization.add_mk_self]

#check constAway

#check cAway

noncomputable def x01 : AwayRing K0 :=
  HomogeneousLocalization.Away.mk
    (MvPolynomial.homogeneousSubmodule (Fin 2) K0)
    (d := 1) (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X _ _) 1
    (MvPolynomial.X 0) (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa using MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K0) 0)

noncomputable def gRing : Poly1 K0 →+* AwayRing K0 :=
  MvPolynomial.eval₂Hom (constAway K0) (fun _ : Fin 1 => x01 K0)

theorem fRing_comp_gRing :
    (fRing K0).comp (gRing K0) = RingHom.id (Poly1 K0) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have h := Localization.awayLift_mk (phi K0) (MvPolynomial.X 1)
      (MvPolynomial.C a) 1 (by rw [phi_X1 K0]; simp) 0
    simpa [fRing, gRing, constAway, cAway, phi,
      HomogeneousLocalization.Away.val_mk] using h
  · intro i
    fin_cases i
    have h := Localization.awayLift_mk (phi K0) (MvPolynomial.X 1)
      (MvPolynomial.X 0) 1 (by rw [phi_X1 K0]; simp) 1
    simpa [fRing, gRing, x01, phi,
      HomogeneousLocalization.Away.val_mk] using h

#check x01
#check gRing

end S2509GenericAwayEquiv
end
