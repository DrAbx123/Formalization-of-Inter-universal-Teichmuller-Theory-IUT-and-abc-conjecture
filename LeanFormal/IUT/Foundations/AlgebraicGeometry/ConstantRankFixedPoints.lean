import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsDescent
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2GlobalAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseFixedPointsTransport
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Tactic

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.defProp false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints

noncomputable section

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

/-! ## Split case: M2 transported across an arbitrary split algebra equivalence -/

/-- Conjugate a `G`-action across an `S`-algebra equivalence `e : B ≃ₐ[S] Fin n → S`. -/
@[reducible] noncomputable def splitConjAction {S G : Type u} [CommRing S] [Group G]
    {B : Type u} [CommRing B] [Algebra S B] [MulSemiringAction G B] [SMulCommClass G S B]
    {n : ℕ} (e : B ≃ₐ[S] (Fin n → S)) : MulSemiringAction G (Fin n → S) where
  smul g x := e (g • e.symm x)
  one_smul x := by
    change e ((1 : G) • e.symm x) = x
    rw [one_smul, AlgEquiv.apply_symm_apply]
  mul_smul g h x := by
    change e ((g * h) • e.symm x) = e (g • e.symm (e (h • e.symm x)))
    rw [mul_smul, AlgEquiv.symm_apply_apply]
  smul_zero g := by
    change e (g • e.symm (0 : Fin n → S)) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add g x y := by
    change e (g • e.symm (x + y)) = e (g • e.symm x) + e (g • e.symm y)
    rw [map_add, smul_add, map_add]
  smul_one g := by
    change e (g • e.symm (1 : Fin n → S)) = 1
    rw [map_one, smul_one, map_one]
  smul_mul g x y := by
    change e (g • e.symm (x * y)) = e (g • e.symm x) * e (g • e.symm y)
    rw [map_mul, smul_mul', map_mul]

/-- The conjugated action commutes with the `S`-scalars. -/
@[reducible] noncomputable def splitConjSMulComm {S G : Type u} [CommRing S] [Group G]
    {B : Type u} [CommRing B] [Algebra S B] [MulSemiringAction G B] [SMulCommClass G S B]
    {n : ℕ} (e : B ≃ₐ[S] (Fin n → S)) :
    letI : MulSemiringAction G (Fin n → S) := splitConjAction (S := S) (G := G) e
    SMulCommClass G S (Fin n → S) := by
  letI : MulSemiringAction G (Fin n → S) := splitConjAction (S := S) (G := G) e
  refine ⟨fun g s x => ?_⟩
  change e (g • e.symm (s • x)) = s • e (g • e.symm x)
  rw [map_smul (e.symm) s x, smul_comm g s (e.symm x), map_smul e s (g • e.symm x)]

/-- M2 final transported to any finite split `S`-algebra `B`: the fixed-point
subalgebra is finite etale over `S`. -/
theorem splitFixedPoints_finiteEtale {S : Type u} [CommRing S]
    {B : Type u} [CommRing B] [Algebra S B] [Algebra.Etale S B] [Module.Finite S B]
    [MulSemiringAction G B] [SMulCommClass G S B]
    (hsplit : Algebra.IsFiniteSplit S B) :
    Algebra.Etale S (FixedPoints.subalgebra S B G) ∧
      Module.Finite S (FixedPoints.subalgebra S B G) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun S B
  haveI : Fintype G := Fintype.ofFinite G
  haveI : DecidableEq G := Classical.decEq G
  letI : MulSemiringAction G (Fin n → S) := splitConjAction (S := S) (G := G) e
  letI : SMulCommClass G S (Fin n → S) := splitConjSMulComm (S := S) (G := G) e
  have hM2 := M2FinalAssembly.m2_final (S := S) (G := G) (n := n)
  letI : Algebra.Etale S (FixedPoints.subalgebra S (Fin n → S) G) := hM2.1
  letI : Module.Finite S (FixedPoints.subalgebra S (Fin n → S) G) := hM2.2
  have he : ∀ (g : G) (b : B), e (g • b) = g • e b := by
    intro g b
    change e (g • b) = e (g • e.symm (e b))
    rw [AlgEquiv.symm_apply_apply]
  have hfix := ABCBridge.SplitCaseFixedPointsTransport.fixedPointsAlgEquivOfEquiv
    (S := S) (A := B) (B := Fin n → S) (G := G) e he
  exact ⟨Algebra.Etale.of_equiv hfix.symm,
    Module.Finite.equiv hfix.symm.toLinearEquiv⟩

/-! ## Constant-rank splitting cover and M3 descent -/

/-- Constant-rank finite etale `A/R` admits a finite faithfully flat etale cover
`T` such that `T ⊗[R] A` is split (Mathlib Lenstra 5.10). -/
theorem exists_splitCover_of_constantRank (n : ℕ)
    (hn : Module.rankAtStalk (R := R) A = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T) (_ : Algebra.Etale R T),
      Algebra.IsFiniteSplit T (T ⊗[R] A) :=
  Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := R) (S := A) hn

/-- Core M3 descent consumer: a faithfully flat `T/R` and a `T`-etale `T'`
identified with `T ⊗[R] A^G` give finite etale `A^G/R`. -/
theorem fixedPointSubalgebra_finiteEtale_of_splitDescent
    (T T' : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [CommRing T'] [Algebra R T'] [Algebra T T'] [IsScalarTower R T T']
    [Algebra.Etale T T']
    (e : T ⊗[R] fixedPointSubalgebra R A G ≃ₐ[T] T') :
    Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) := by
  have het : Algebra.Etale R (fixedPointSubalgebra R A G) :=
    ABCBridge.InvariantsDescent.etale_fixedPointSubalgebra_of_baseChange_fixedPoints
      R A G T T' e
  exact ⟨het, fixedPoints_moduleFinite_of_etale R A G het⟩

/-- M3 assembly: constant-rank finite etale `A/R`, Mathlib's splitting cover,
M1's actual flat-base-change AlgEquiv, and the transported production M2 theorem
imply `A^G` is finite etale over `R`, with no `|G|`-invertibility. -/
theorem fixedPointSubalgebra_finiteEtale_of_constantRank
    (n : ℕ) (hn : Module.rankAtStalk (R := R) A = n) :
    Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) := by
  obtain ⟨T, hTcomm, hTalg, hTff, hTfin, hTet, hTsplit⟩ :=
    exists_splitCover_of_constantRank (R := R) (A := A) n hn
  letI := hTcomm
  letI := hTalg
  letI := hTff
  letI := hTfin
  letI := hTet
  haveI : Fintype G := Fintype.ofFinite G
  haveI : DecidableEq G := Classical.decEq G
  haveI : Module.Flat R T := Algebra.Smooth.flat R T
  have hT2 := splitFixedPoints_finiteEtale (S := T) (G := G)
    (B := T ⊗[R] A) hTsplit
  letI : Algebra.Etale T (FixedPoints.subalgebra T (T ⊗[R] A) G) := hT2.1
  exact fixedPointSubalgebra_finiteEtale_of_splitDescent (R := R) (A := A) (G := G)
    T (FixedPoints.subalgebra T (T ⊗[R] A) G)
    (M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G) (T := T))


/-- L0 source-range corollary: over a local base ring every finite flat module is
free, so the finite etale algebra has a constant rank and the constant-rank M3
assembly applies without an explicit rank hypothesis. -/
theorem fixedPointSubalgebra_finiteEtale_of_local
    [IsLocalRing R] :
    Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) := by
  haveI : Module.Flat R A := Algebra.Smooth.flat R A
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  refine fixedPointSubalgebra_finiteEtale_of_constantRank (R := R) (A := A) (G := G)
    (Module.finrank R A) ?_
  rw [Module.rankAtStalk_eq_finrank_of_free]

end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints