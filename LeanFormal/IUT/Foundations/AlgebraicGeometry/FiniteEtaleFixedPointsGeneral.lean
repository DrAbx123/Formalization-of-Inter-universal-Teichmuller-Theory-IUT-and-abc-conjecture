import LeanFormal.IUT.Foundations.AlgebraicGeometry.RankDecompositionFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory


set_option maxRecDepth 10000
noncomputable section

namespace FiniteEtaleFixedPointsGeneral

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- Finitely presented flat is projective. -/
local instance moduleProjective : Module.Projective R A := by
  haveI : Module.Flat R A := inferInstance
  haveI : Module.FinitePresentation R A :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := R) (S := A)).mpr inferInstance
  exact Module.Flat.projective_of_finitePresentation

local notation "B" => LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra R A G

/-- The rank-n idempotent. -/
abbrev eRank (n : ℕ) : R :=
  RankDecompositionFixedPoints.rankComponentIdempotent (R := R) (A := A) n

/-- The rank labels cover all primes. -/
lemma rank_span_top : Ideal.span (Set.range (eRank (R := R) (A := A))) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  apply top_unique
  intro p hp
  rw [TopologicalSpace.Opens.mem_iSup]
  refine ⟨Module.rankAtStalk (R := R) A p, ?_⟩
  have h : p ∈ (PrimeSpectrum.basicOpen
      (RankDecompositionFixedPoints.rankComponentIdempotent (R := R) (A := A)
        (Module.rankAtStalk (R := R) A p)) : Set (PrimeSpectrum R)) := by
    rw [RankDecompositionFixedPoints.rankComponent_basicOpen]
    rfl
  simpa [eRank] using h

/-- Localized component ring. -/
abbrev RN (n : ℕ) : Type u := Localization.Away (eRank (R := R) (A := A) n)

/-- Localized component algebra. -/
abbrev AN (n : ℕ) : Type u := TensorProduct R (RN (R := R) (A := A) n) A

/-- Localized fixed-point algebra. -/
abbrev CN (n : ℕ) : Type u := TensorProduct R (RN (R := R) (A := A) n) B

local instance (n : ℕ) : Module.Flat R (RN (R := R) (A := A) n) := inferInstance

/-- Base change of A is finite etale. -/
local instance anFinite (n : ℕ) : Module.Finite (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) := by
  unfold AN; infer_instance

local instance anEtale (n : ℕ) : Algebra.Etale (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) := by
  unfold AN; infer_instance

local instance anAction (n : ℕ) : MulSemiringAction G (AN (R := R) (A := A) n) := by
  unfold AN; infer_instance

local instance anSMulComm (n : ℕ) : SMulCommClass G (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) := by
  unfold AN
  exact LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints.tensorSMulCommClass (R := R) (A := A) (G := G) (T := RN (R := R) (A := A) n)

/-- The localized algebra has constant rank n. -/
lemma anRank (n : ℕ) :
    Module.rankAtStalk (R := RN (R := R) (A := A) n) (AN (R := R) (A := A) n) = n := by
  funext p
  exact RankDecompositionFixedPoints.rankAtStalk_baseChange_component (R := R) (A := A) n p

/-- Constant-rank theorem on the localized component. -/
lemma anFixedFiniteEtale (n : ℕ) :
    Algebra.Etale (RN (R := R) (A := A) n)
        (LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra
          (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) G) ∧
      Module.Finite (RN (R := R) (A := A) n)
        (LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra
          (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) G) :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_constantRank
    (R := RN (R := R) (A := A) n) (A := AN (R := R) (A := A) n) (G := G)
    n (anRank (R := R) (A := A) n)

/-- M1 identifies the localized fixed points with C_n. -/
noncomputable def cnEquivFixed (n : ℕ) :
    CN (R := R) (A := A) (G := G) n ≃ₐ[RN (R := R) (A := A) n]
      LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra
        (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) G :=
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := RN (R := R) (A := A) n)

lemma cnEtale (n : ℕ) : Algebra.Etale (RN (R := R) (A := A) n) (CN (R := R) (A := A) (G := G) n) := by
  haveI : Algebra.Etale (RN (R := R) (A := A) n)
      (LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra
        (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) G) :=
    (anFixedFiniteEtale (R := R) (A := A) (G := G) n).1
  exact Algebra.Etale.of_equiv
    (A := LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPointSubalgebra
      (RN (R := R) (A := A) n) (AN (R := R) (A := A) n) G)
    (cnEquivFixed (R := R) (A := A) (G := G) n).symm

local instance cnAlgebraB (n : ℕ) : Algebra B (CN (R := R) (A := A) (G := G) n) := by
  unfold CN
  exact Algebra.TensorProduct.rightAlgebra

local instance cnLocalization (n : ℕ) :
    IsLocalization.Away (algebraMap R B (eRank (R := R) (A := A) n))
      (CN (R := R) (A := A) (G := G) n) := by
  unfold CN; exact IsLocalization.Away.tensorRight (R := R) (S := B) (eRank (R := R) (A := A) n) (RN (R := R) (A := A) n)

/-- The localization-span compatibility square. -/
lemma localizationSquare (n : ℕ) :
    (algebraMap (RN (R := R) (A := A) n) (CN (R := R) (A := A) (G := G) n)).comp
        (algebraMap R (RN (R := R) (A := A) n)) =
      (algebraMap B (CN (R := R) (A := A) (G := G) n)).comp (algebraMap R B) := by
  ext r
  change (algebraMap R (RN (R := R) (A := A) n)) r ⊗ₜ[R] (1 : B) =
    (1 : RN (R := R) (A := A) n) ⊗ₜ[R] (algebraMap R B) r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rw [TensorProduct.smul_tmul]

/-- Ring-level etale of the localized map. -/
lemma fEtale (n : ℕ) :
    RingHom.Etale (algebraMap (RN (R := R) (A := A) n)
      (CN (R := R) (A := A) (G := G) n)) :=
  RingHom.etale_algebraMap.mpr (cnEtale (R := R) (A := A) (G := G) n)

/-- General fixed-point theorem. -/
theorem fixedPointSubalgebra_finiteEtale :
    Algebra.Etale R B ∧ Module.Finite R B := by
  have hEtaleRing : RingHom.Etale (algebraMap R B) := by
    refine RingHom.OfLocalizationSpan.ofIsLocalization
      RingHom.Etale.ofLocalizationSpan RingHom.Etale.respectsIso
      (algebraMap R B) (Set.range (eRank (R := R) (A := A)))
      (rank_span_top (R := R) (A := A)) ?_
    intro r
    obtain ⟨n, hn⟩ := Set.mem_range.mp r.2
    refine ⟨RN (R := R) (A := A) n, CN (R := R) (A := A) (G := G) n,
      inferInstance, inferInstance, inferInstance, inferInstance,
      ?_, ?_, algebraMap (RN (R := R) (A := A) n) (CN (R := R) (A := A) (G := G) n), ?_, ?_⟩
    · simpa [← hn] using (inferInstance : IsLocalization.Away
        (eRank (R := R) (A := A) n) (RN (R := R) (A := A) n))
    · simpa [hn] using (cnLocalization (R := R) (A := A) (G := G) n)
    · simpa [hn] using (localizationSquare (R := R) (A := A) (G := G) n)
    · simpa [hn] using fEtale (R := R) (A := A) (G := G) n
  have hEtale : Algebra.Etale R B := RingHom.etale_algebraMap.mp hEtaleRing
  exact ⟨hEtale,
    LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.fixedPoints_moduleFinite_of_etale
      R A G hEtale⟩

end FiniteEtaleFixedPointsGeneral
