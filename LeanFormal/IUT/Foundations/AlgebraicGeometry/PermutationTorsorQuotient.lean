import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace PermutationTorsorQuotient

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  {ι : Type u} [MulAction G ι]

instance functionMulSemiringAction : MulSemiringAction G (ι → R) where
  smul g f := fun i => f (g⁻¹ • i)
  one_smul f := by funext i; change f ((1 : G)⁻¹ • i) = f i; simp
  mul_smul g h f := by funext i; change f ((g * h)⁻¹ • i) = f (h⁻¹ • (g⁻¹ • i)); rw [mul_inv_rev, mul_smul]
  smul_zero g := by funext i; rfl
  smul_add g f h := by funext i; rfl
  smul_one g := by funext i; rfl
  smul_mul g f h := by funext i; rfl

instance functionSMulCommClass : SMulCommClass G R (ι → R) where
  smul_comm g r f := by funext i; rfl

theorem mem_fixedPoints_iff_constant
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) (f : ι → R) :
    f ∈ FixedPoints.subalgebra R (ι → R) G ↔ ∀ i j : ι, f i = f j := by
  constructor
  · intro hf i j
    obtain ⟨g, hg⟩ := htrans i j
    have h := congrFun (hf g) j
    have hg' : g⁻¹ • j = i := by rw [← hg, inv_smul_smul]
    change f (g⁻¹ • j) = f j at h
    rw [hg'] at h
    exact h
  · intro hc g
    funext i
    exact hc (g⁻¹ • i) i

noncomputable def fixedPointsEquivBase [Nonempty ι]
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) :
    FixedPoints.subalgebra R (ι → R) G ≃ₐ[R] R where
  toFun f := f.val (Classical.arbitrary ι)
  invFun r := ⟨fun _ => r, by
    intro g
    funext i
    rfl⟩
  left_inv f := by
    ext i
    have hc := (mem_fixedPoints_iff_constant htrans f.val).mp f.2 i (Classical.arbitrary ι)
    simpa using hc.symm
  right_inv r := rfl
  map_add' f g := rfl
  map_mul' f g := rfl
  commutes' r := rfl

theorem fixedPoints_etale [Nonempty ι]
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) :
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) := by
  exact Algebra.Etale.of_equiv (fixedPointsEquivBase htrans).symm

theorem fixedPoints_moduleFinite [Nonempty ι]
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) :
    Module.Finite R (FixedPoints.subalgebra R (ι → R) G) :=
  Module.Finite.equiv (fixedPointsEquivBase htrans).toLinearEquiv.symm

theorem fixedPoints_finiteEtale [Nonempty ι]
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) :
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (ι → R) G) :=
  ⟨fixedPoints_etale htrans, fixedPoints_moduleFinite htrans⟩

section FreeTorsor

theorem regular_action_transitive (i j : G) : ∃ g : G, g • i = j := by
  refine ⟨j * i⁻¹, ?_⟩
  simp [mul_assoc]

noncomputable def regular_fixedPoints_equiv :
    FixedPoints.subalgebra R (G → R) G ≃ₐ[R] R :=
  fixedPointsEquivBase (R := R) (G := G) (ι := G) regular_action_transitive

theorem regular_fixedPoints_etale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) :=
  fixedPoints_etale (R := R) (G := G) (ι := G) regular_action_transitive

theorem regular_fixedPoints_moduleFinite :
    Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  fixedPoints_moduleFinite (R := R) (G := G) (ι := G) regular_action_transitive

end FreeTorsor

section OrbitProduct

theorem fixedPoints_invariance_orbit_quotient
    (gq : MulAction.orbitRel.Quotient G ι → R) :
    (fun i => gq (Quotient.mk (MulAction.orbitRel G ι) i)) ∈
      FixedPoints.subalgebra R (ι → R) G := by
  intro g
  funext i
  change gq (Quotient.mk (MulAction.orbitRel G ι) (g⁻¹ • i)) =
    gq (Quotient.mk (MulAction.orbitRel G ι) i)
  congr 1
  apply Quotient.sound
  exact ⟨g⁻¹, rfl⟩

noncomputable def fixedPointsEquivOrbitFunctions :
    FixedPoints.subalgebra R (ι → R) G ≃ₐ[R]
      (MulAction.orbitRel.Quotient G ι → R) where
  toFun f := Quotient.lift (fun i => f.val i) (by
    intro i j h
    rcases h with ⟨g, hg⟩
    have hfix := congrFun (f.2 g) i
    change f.val (g⁻¹ • i) = f.val i at hfix
    have hgj : g⁻¹ • i = j := by rw [← hg, inv_smul_smul]
    rw [hgj] at hfix
    exact hfix.symm)
  invFun gq := ⟨fun i => gq (Quotient.mk (MulAction.orbitRel G ι) i), fixedPoints_invariance_orbit_quotient gq⟩
  left_inv f := by
    ext i
    rfl
  right_inv gq := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  map_add' f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  map_mul' f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  commutes' r := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl

theorem fixedPoints_etale_orbits [Fintype ι] :
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) := by
  exact Algebra.Etale.of_equiv (fixedPointsEquivOrbitFunctions).symm

theorem fixedPoints_moduleFinite_orbits [Fintype ι] :
    Module.Finite R (FixedPoints.subalgebra R (ι → R) G) :=
  Module.Finite.equiv (fixedPointsEquivOrbitFunctions).toLinearEquiv.symm

theorem fixedPoints_finiteEtale_orbits [Fintype ι] :
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (ι → R) G) :=
  ⟨fixedPoints_etale_orbits, fixedPoints_moduleFinite_orbits⟩

end OrbitProduct


section QuotientChart

open AlgebraicGeometry CategoryTheory

/-- The affine quotient chart `Spec (A^G) → Spec R` for the permutation cover. -/
def finiteEtaleQuotientChart :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap R (FixedPoints.subalgebra R (ι → R) G))))

end QuotientChart


section FiniteEtaleCoverChart

open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable [Fintype ι]

theorem finiteEtaleQuotientChart_etale :
    Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R (ι → R) G)))) := by
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr (fixedPoints_etale_orbits (R := R) (G := G) (ι := ι)))

theorem finiteEtaleQuotientChart_finite :
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R (ι → R) G)))) := by
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (R := CommRingCat.of R) (S := CommRingCat.of (FixedPoints.subalgebra R (ι → R) G))
    (f := CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R (ι → R) G)))).mpr
    (RingHom.finite_algebraMap.mpr (fixedPoints_moduleFinite_orbits (R := R) (G := G) (ι := ι)))

noncomputable def finiteEtaleQuotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R (ι → R) G))))
    finiteEtaleQuotientChart_etale finiteEtaleQuotientChart_finite

end FiniteEtaleCoverChart

end

end PermutationTorsorQuotient
