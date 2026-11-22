import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Corner fixed points and product interface for M2/M3

Given a corner ring `R` and a coordinate permutation action of a finite group `G`
on `ι → R` (provided by kummer's `σ_g`/`hrow`/`hcol` block), the fixed-point
algebra is the algebra of functions on the orbit quotient.  The second part
packages the product of finitely many finite etale corners, the M3 consumer.
-/
namespace ABCBridge.SplitCaseCornerFixedPoints

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]
  {ι : Type u} [Fintype ι]

/-- Corner fixed points of a coordinate permutation action are functions on the
orbit quotient. -/
noncomputable def cornerFixedPointsEquivOrbitFunctions
    (ρ : G →* Equiv.Perm ι) :
    letI : MulAction G ι := MulAction.compHom ι ρ
    FixedPoints.subalgebra R (ι → R) G ≃ₐ[R]
      (MulAction.orbitRel.Quotient G ι → R) := by
  letI : MulAction G ι := MulAction.compHom ι ρ
  exact PermutationTorsorQuotient.fixedPointsEquivOrbitFunctions
    (R := R) (G := G) (ι := ι)

/-- Corner fixed points are finite etale over the corner ring. -/
theorem cornerFixedPoints_finiteEtale (ρ : G →* Equiv.Perm ι) :
    letI : MulAction G ι := MulAction.compHom ι ρ
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (ι → R) G) := by
  letI : MulAction G ι := MulAction.compHom ι ρ
  exact PermutationTorsorQuotient.fixedPoints_finiteEtale_orbits
    (R := R) (G := G) (ι := ι)

/-- M3 product consumer: a finite product of finite etale `S`-algebras is finite
etale over `S`. -/
theorem pi_finiteEtale {S : Type u} [CommRing S] {κ : Type u} [Fintype κ]
    (T : κ → Type u) [∀ k, CommRing (T k)] [∀ k, Algebra S (T k)]
    [∀ k, Algebra.Etale S (T k)] [∀ k, Module.Finite S (T k)] :
    Algebra.Etale S (∀ k, T k) ∧ Module.Finite S (∀ k, T k) :=
  ⟨inferInstance, inferInstance⟩



/-- Universe-local function action on `Fin n → R` induced by a permutation hom.
Used because production `functionMulSemiringAction` unifies the index universe
with `R`. -/
noncomputable def finFunctionMulSemiringAction {n : ℕ}
    (ρ : G →* Equiv.Perm (Fin n)) : MulSemiringAction G (Fin n → R) where
  smul g f := fun i => f ((ρ g)⁻¹ i)
  one_smul f := by
    funext i
    change f ((ρ 1)⁻¹ i) = f i
    rw [map_one]
    rfl
  mul_smul g h f := by
    funext i
    change f ((ρ (g * h))⁻¹ i) = f ((ρ h)⁻¹ ((ρ g)⁻¹ i))
    rw [map_mul, mul_inv_rev]
    rfl
  smul_zero g := by funext i; rfl
  smul_add g f h := by funext i; rfl
  smul_one g := by funext i; rfl
  smul_mul g f h := by funext i; rfl

noncomputable def finFunctionSMulCommClass {n : ℕ}
    (ρ : G →* Equiv.Perm (Fin n)) :
    letI : MulSemiringAction G (Fin n → R) :=
      finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
    SMulCommClass G R (Fin n → R) := by
  letI : MulSemiringAction G (Fin n → R) :=
    finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
  exact ⟨fun g r f => by funext i; rfl⟩

section FinSpecialized

variable {n : ℕ}

noncomputable def cornerFixedPointsEquivFin (ρ : G →* Equiv.Perm (Fin n)) :
    letI : MulAction G (Fin n) := MulAction.compHom (Fin n) ρ
    letI : MulSemiringAction G (Fin n → R) :=
      finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
    letI : SMulCommClass G R (Fin n → R) :=
      finFunctionSMulCommClass (R := R) (G := G) (ρ := ρ)
    FixedPoints.subalgebra R (Fin n → R) G ≃ₐ[R]
      (MulAction.orbitRel.Quotient G (Fin n) → R) := by
  letI : MulAction G (Fin n) := MulAction.compHom (Fin n) ρ
  letI : MulSemiringAction G (Fin n → R) :=
    finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
  letI : SMulCommClass G R (Fin n → R) :=
    finFunctionSMulCommClass (R := R) (G := G) (ρ := ρ)
  refine
    { toFun := fun f => Quotient.lift (fun i => f.val i) ?_
      invFun := fun gq => ⟨fun i => gq (Quotient.mk (MulAction.orbitRel G (Fin n)) i), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_
      commutes' := ?_ }
  · intro i j h
    rcases h with ⟨g, hg⟩
    have hfix : f.val ((ρ g)⁻¹ i) = f.val i := congrFun (f.2 g) i
    have hgj : (ρ g)⁻¹ i = j := by
      have hg' : (ρ g) j = i := hg
      calc (ρ g)⁻¹ i = (ρ g)⁻¹ (ρ g j) := by rw [hg']
        _ = j := by simp
    rw [hgj] at hfix
    exact hfix.symm
  · intro g
    funext i
    change gq (Quotient.mk (MulAction.orbitRel G (Fin n)) ((ρ g)⁻¹ i)) =
      gq (Quotient.mk (MulAction.orbitRel G (Fin n)) i)
    congr 1
    apply Quotient.sound
    exact ⟨g⁻¹, by
      change (ρ g⁻¹) i = (ρ g)⁻¹ i
      rw [map_inv]⟩
  · intro f
    ext i
    rfl
  · intro gq
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  · intro f g
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  · intro f g
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  · intro r
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl

theorem cornerFixedPoints_finiteEtaleFin (ρ : G →* Equiv.Perm (Fin n)) :
    letI : MulAction G (Fin n) := MulAction.compHom (Fin n) ρ
    letI : MulSemiringAction G (Fin n → R) :=
      finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
    letI : SMulCommClass G R (Fin n → R) :=
      finFunctionSMulCommClass (R := R) (G := G) (ρ := ρ)
    Algebra.Etale R (FixedPoints.subalgebra R (Fin n → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (Fin n → R) G) := by
  letI : MulAction G (Fin n) := MulAction.compHom (Fin n) ρ
  letI : MulSemiringAction G (Fin n → R) :=
    finFunctionMulSemiringAction (R := R) (G := G) (ρ := ρ)
  letI : SMulCommClass G R (Fin n → R) :=
    finFunctionSMulCommClass (R := R) (G := G) (ρ := ρ)
  exact ⟨Algebra.Etale.of_equiv (cornerFixedPointsEquivFin (R := R) (G := G) ρ).symm,
    Module.Finite.equiv (cornerFixedPointsEquivFin (R := R) (G := G) ρ).toLinearEquiv.symm⟩

end FinSpecialized

section Family

universe v

variable {κ : Type v} [Fintype κ] (Rc : κ → Type u)
  [∀ A, CommRing (Rc A)] (ρ : ∀ A, G →* Equiv.Perm (Fin n))

/-- Per-atom corner fixed-point equivalence, with the exact local instances used
by the global atom assembly. -/
noncomputable def cornerFixedPointsEquivAt (A : κ) :
    letI : MulAction G (Fin n) := MulAction.compHom (Fin n) (ρ A)
    letI : MulSemiringAction G (Fin n → Rc A) :=
      finFunctionMulSemiringAction (R := Rc A) (G := G) (ρ := ρ A)
    letI : SMulCommClass G (Rc A) (Fin n → Rc A) :=
      finFunctionSMulCommClass (R := Rc A) (G := G) (ρ := ρ A)
    FixedPoints.subalgebra (Rc A) (Fin n → Rc A) G ≃ₐ[Rc A]
      (MulAction.orbitRel.Quotient G (Fin n) → Rc A) :=
  cornerFixedPointsEquivFin (R := Rc A) (G := G) (ρ := ρ A)

/-- Per-atom finite etaleness of the corner fixed-point algebra. -/
theorem cornerFixedPoints_finiteEtaleAt (A : κ) :
    letI : MulAction G (Fin n) := MulAction.compHom (Fin n) (ρ A)
    letI : MulSemiringAction G (Fin n → Rc A) :=
      finFunctionMulSemiringAction (R := Rc A) (G := G) (ρ := ρ A)
    letI : SMulCommClass G (Rc A) (Fin n → Rc A) :=
      finFunctionSMulCommClass (R := Rc A) (G := G) (ρ := ρ A)
    Algebra.Etale (Rc A) (FixedPoints.subalgebra (Rc A) (Fin n → Rc A) G) ∧
      Module.Finite (Rc A) (FixedPoints.subalgebra (Rc A) (Fin n → Rc A) G) :=
  cornerFixedPoints_finiteEtaleFin (R := Rc A) (G := G) (ρ := ρ A)

end Family

end ABCBridge.SplitCaseCornerFixedPoints