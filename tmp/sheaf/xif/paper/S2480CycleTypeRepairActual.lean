/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

/-!
# S2480: repair of the actual range cycle-type target

## The target

  S2480Target := S2203RangeCycleTypeRequired S1982Basis
    = HasCycleType102
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

with the actual punctured elliptic curve E' = S1720Curve over the actual number
field F' = S1720Field, the actual rank-two basis S1982Basis of E'[5], and
HasCycleType102 (S2009) meaning that some element of the range acts on the
twelve pairs {+-v}, v in F_5^2 \ {0}, with permutation cycle type (10, 2).

## What this file does

This is the clean repair of the failed S2461CycleTypeFinalActual attempt.  It
does NOT prove the target and does NOT consume any stale olean of S2446, S2460
or S2461.  It rebuilds the reductions from the actual modules S2009, S2056,
S2132, S2167, S2172, S2180, S2186, S2203, S2217, S2126, S2055 and S1894.

Proved here (all kernel checked; no proof holes, extra postulates, vacuous gates or unchecked decision procedures):

1. The target is definitionally the displayed range statement, and equivalent
   to the cycle-type hypothesis at any rank-two basis.  The range at two
   bases is conjugate (S1894) and the pair cycle type is a class function on
   GL_2(F_5).
2. The target is equivalent to the existence of an element sigma of the
   absolute Galois group of F' whose mod-5 matrix has pair cycle type (10, 2)
   (S2480Target_iff_exists_sigma).
3. The matrix pair action of sigma is the actual Galois action of sigma on
   the twelve pairs {+-P} of nonzero 5-torsion points of E'
   (S2480PairAction_apply), and the pair permutation is canonically
   conjugate to the permutation of the twelve roots of the actual odd
   5-division polynomial psi_5 (S2480RootPairEquiv_permCongr,
   S2480PairMatrix_cycleType).
4. Consequently the target is exactly the existence of an F'-automorphism of
   the algebraic closure whose permutation of the twelve psi_5-roots has
   cycle type (10, 2) (S2480Target_iff_rootCycle).  This is the arithmetic
   form in which the Dedekind--Frobenius theorem of S2167/S2217 supplies its
   output.  Equivalently, the orbit-size multiset of that permutation is
   {10, 2} (S2480Target_iff_orbitSize), which is the vocabulary of the
   corrected Dedekind--Frobenius statement of S2217.
5. The target forces 10 | #range and 5 | #range and excludes the proper
   subgroup orders 96 and 48 of the Dickson list.
6. Together with pair transitivity of the actual range, the first missing
   statement gives the S1987 D5 large-image target (S2203).
7. The S2057 mod-29 factorization interface is uninhabitable
   (S2132Mod29FactorizationData_empty); this is why the honest first missing
   is stated on the actual division polynomial and not as a field of that
   structure.  The actual finite certificate is the corrected product of
   S2132 with the S2126 degree-ten irreducibility; the only unproved finite
   micro-input in the corrected certificate is the quadratic irreducibility
   S2167QuadraticIrreducible.

## Exact first missing

S2480FirstMissing below: there is an F'-automorphism of the algebraic closure
whose permutation of the twelve actual roots of psi_5 has cycle type (10, 2).
It is provably equivalent to S2480Target (S2480FirstMissing_iff_target).  No
inhabitant is asserted.  The conceptual arithmetic source is the
Dedekind--Frobenius orbit-size theorem S2217Missing (S2167 records the literal
statement, which S2217 refutes and corrects); the concrete S2132 statement
S2132FrobInducesPairCycleType is its splitting-field form.  The transport from
the S2057 splitting field to the absolute closure and the Dedekind--Frobenius
comparison are not formalized in this tree, so neither is claimed here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

open Matrix
open Polynomial
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual

/-! ## 1. The exact target and its basis-independence -/

/-- The actual range cycle-type target at the selected basis S1982Basis. -/
def S2480Target : Prop := S2203RangeCycleTypeRequired S1982Basis

/-- The target unfolded. -/
theorem S2480Target_iff_range :
    S2480Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The same target at the definitionally equal prime label S1982Five. -/
theorem S2480Target_iff_range1982 :
    S2480Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis).range :=
  Iff.rfl

/-- Conjugation in GL_2(F_5) preserves the pair cycle type. -/
theorem S2480cycleType_pairPermHom_conj (c g : GL2) :
    (pairPermHom (c * g * c⁻¹)).cycleType = (pairPermHom g).cycleType := by
  rw [map_mul, map_mul, map_inv]
  exact Equiv.Perm.cycleType_conj

/-- Cycle type (10, 2) is invariant under conjugating the subgroup. -/
theorem S2480HasCycleType102_map_conj (c : GL2) (H : Subgroup GL2) :
    HasCycleType102 (Subgroup.map (MulAut.conj c).toMonoidHom H) ↔
      HasCycleType102 H := by
  constructor
  · rintro ⟨h, hh, hc⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨g, hg, hgk⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgk
    refine ⟨g, hg, ?_⟩
    rw [← S2480cycleType_pairPermHom_conj c g]
    exact hgk ▸ hc
  · rintro ⟨g, hg, hc⟩
    refine ⟨c * g * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨g, hg, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [S2480cycleType_pairPermHom_conj]
      exact hc

/-- The cycle-type hypothesis is independent of the rank-two basis. -/
theorem S2480RangeCycleType_congr (b b' : S1725TorsionBasis S1987Five) :
    HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b').range := by
  rw [S1894MatrixRep_range_conj S1987Five b b']
  exact (S2480HasCycleType102_map_conj
    (S1894BasisChangeGL S1987Five b b')
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range).symm

/-- The target is the cycle-type hypothesis at any chosen basis. -/
theorem S2480Target_iff_basis (b : S1725TorsionBasis S1987Five) :
    S2480Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2480Target_iff_range.trans (S2480RangeCycleType_congr S1982Basis b)

/-- The basis-free universal form of the target. -/
theorem S2480Target_iff_forall_basis :
    S2480Target ↔ ∀ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h b
    exact (S2480Target_iff_basis b).mp h
  · intro h
    exact (S2480Target_iff_basis S1982Basis).mpr (h S1982Basis)

/-- The existential-basis form of the target. -/
theorem S2480Target_iff_exists_basis :
    S2480Target ↔ ∃ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h
    exact ⟨S1982Basis, (S2480Target_iff_basis S1982Basis).mp h⟩
  · rintro ⟨b, hb⟩
    exact (S2480Target_iff_basis b).mpr hb

/-- The target as the existence of a Galois element whose matrix has pair
cycle type (10, 2). -/
theorem S2480Target_iff_exists_sigma :
    S2480Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) := by
  rw [S2480Target_iff_range]
  change (∃ h : GL (Fin 2) (ZMod S1987Five.value),
      h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ∧
        (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)) ↔ _
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, hc⟩

/-! ## 2. The actual Galois action on the twelve pairs -/

/-- The permutation of the twelve roots of psi_5 induced by an absolute Galois
element. -/
noncomputable def S2480RootPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Root where
  toFun := S2056RootMap σ
  invFun := S2056RootMap σ.symm
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)

@[simp] theorem S2480RootPerm_apply (σ : S1725AbsoluteGalois) (x : S2056Root) :
    S2480RootPerm σ x = S2056RootMap σ x := rfl

/-- The actual Galois action on the affine 5-torsion, as a homomorphism. -/
noncomputable def S2480PointMapTorsion (σ : S1725AbsoluteGalois) :
    S2056Torsion →+ S2056Torsion where
  toFun P := ⟨S2056PointMap σ (P : S2056W.Point), by
    have h := S2056PointMap_torsion σ P.2
    simpa using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

@[simp] theorem S2480PointMapTorsion_coe (σ : S1725AbsoluteGalois)
    (P : S2056Torsion) :
    (S2480PointMapTorsion σ P : S2056W.Point) =
      S2056PointMap σ (P : S2056W.Point) := rfl

/-- The projective/affine comparison intertwines the actual Galois action. -/
theorem S2480AffineTorsionEquiv_galois (σ : S1725AbsoluteGalois)
    (P : S1720Curve.LTorsion S1982Five) :
    (S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five σ P) :
        S2056W.Point) =
      S2056PointMap σ (S2172AffineTorsionEquiv P : S2056W.Point) := by
  change S1906ProjAffineEquiv (S1720Curve.galoisActionOnPoint σ
      (P : WeierstrassCurve.Projective.Point S2056W)) =
    WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) σ.toAlgHom
      (S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W))
  unfold PuncturedEllipticCurve.galoisActionOnPoint S1906ProjAffineEquiv
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply]

/-- The matrix representation acts on the affine torsion through the actual
Galois action. -/
theorem S2480MatrixRep_affine (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v) :
        S2056W.Point) =
      S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := by
  have h := S1894MatrixRep_acts S1982Five S1982Basis σ v
  calc
    (S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v) :
          S2056W.Point)
        = (S2172AffineTorsionEquiv
            (S1982Basis ((Matrix.GeneralLinearGroup.toLin
              (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v)) :
              S2056W.Point) := rfl
    _ = (S2172AffineTorsionEquiv
          (S1720Curve.galoisActionOnLTorsionLinearEquiv S1982Five σ
            (S1982Basis v)) : S2056W.Point) := by rw [h]
    _ = (S2172AffineTorsionEquiv
          (S1720Curve.galoisActionOnLTorsion S1982Five σ (S1982Basis v)) :
            S2056W.Point) := by
          rw [PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply]
    _ = S2056PointMap σ (S2172AffineTorsionEquiv (S1982Basis v) : S2056W.Point) :=
          S2480AffineTorsionEquiv_galois σ _
    _ = S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := rfl

/-- The module-action form on points. -/
theorem S2480MatrixRep_smul_point (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) :
          S2056W.Point) =
      S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := by
  rw [← S2480MatrixRep_affine σ v]
  congr 1

/-- The module-action form in the actual affine torsion group. -/
theorem S2480MatrixRep_smul_torsion (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) =
      S2480PointMapTorsion σ (S2172AffineBasis v) := by
  apply Subtype.ext
  exact S2480MatrixRep_smul_point σ v

/-- Negation on nonzero 5-torsion is involutive. -/
theorem S2480_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The standard pair of a nonzero 5-torsion point. -/
noncomputable def S2480PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
  ⟨{P, -P}, Finset.card_pair (S2056_ne_neg P), by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (S2480_neg_neg P)⟩

/-- Pair sets of the same nonzero point are equal. -/
theorem S2480PairOf_eq_of_eq_or_neg {P Q : S2056NonzeroTorsion}
    (h : Q = P ∨ Q = -P) : S2480PairOf P = S2480PairOf Q := by
  apply Subtype.ext
  rcases h with rfl | rfl
  · rfl
  · show ({P, -P} : Finset S2056NonzeroTorsion) = {-P, -(-P)}
    rw [S2480_neg_neg P]
    exact Finset.pair_comm P (-P)

/-- The Galois action on a pair is the pair of the Galois action. -/
theorem S2480PairMap_pairOf (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    S2056PairMap σ (S2480PairOf P) = S2480PairOf (S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  ext Q
  simp only [S2480PairOf, S2056PairMap, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image]
  constructor
  · rintro ⟨R, hR, rfl⟩
    rcases hR with rfl | rfl
    · exact Or.inl rfl
    · rw [S2056NonzeroTorsionMap_neg]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨P, Or.inl rfl, rfl⟩
    · exact ⟨-P, Or.inr rfl, S2056NonzeroTorsionMap_neg σ P⟩

/-- The affine basis image of a nonzero coordinate vector is nonzero. -/
theorem S2480E_ne_zero (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    (S2172AffineBasis v : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : S2172AffineBasis v = 0 := Subtype.ext h
  exact hv (S2172AffineBasis.injective (by rw [h0, map_zero]))

/-- The S2180 pair map is the standard pair of the affine basis image. -/
theorem S2480S2180PairMap_eq_pairOf (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis x =
      S2480PairOf ⟨S2172AffineBasis x.1,
        S2480E_ne_zero x.1 (isRep_ne_zero x.1 x.2)⟩ := by
  apply Subtype.ext
  apply Finset.ext
  intro Q
  simp [S2180PairMap, S2480PairOf]

/-- Coercion of the custom negation on nonzero torsion. -/
theorem S2480NonzeroTorsion_neg_coe (P : S2056NonzeroTorsion) :
    ((-P : S2056NonzeroTorsion) : S2056Torsion) = -P.1 := by
  apply Subtype.ext
  rfl

/-- Coercion of the Galois action on nonzero torsion. -/
theorem S2480NonzeroTorsionMap_coe (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    ((S2056NonzeroTorsionMap σ P : S2056NonzeroTorsion) : S2056Torsion) =
      S2480PointMapTorsion σ P.1 := by
  apply Subtype.ext
  rfl

/-- The actual matrix action agrees with the actual Galois action on pairs. -/
theorem S2480PairAction_apply (σ : S1725AbsoluteGalois) (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis
        (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) x) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis x) := by
  let g := S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ
  let v : Fin 2 → ZMod S1982Five.value := x.1
  let w : Fin 2 → ZMod S1982Five.value := g • v
  have hw : S2172AffineBasis (normalize w) =
        S2480PointMapTorsion σ (S2172AffineBasis v) ∨
      S2172AffineBasis (normalize w) =
        -S2480PointMapTorsion σ (S2172AffineBasis v) := by
    rcases normalize_eq_or_neg w with h | h
    · left
      rw [h, S2480MatrixRep_smul_torsion]
    · right
      rw [h]
      calc
        S2172AffineBasis (-w) = -S2172AffineBasis w := map_neg _ _
        _ = -S2480PointMapTorsion σ (S2172AffineBasis v) := by
          rw [S2480MatrixRep_smul_torsion]
  rw [S2480S2180PairMap_eq_pairOf, S2480S2180PairMap_eq_pairOf,
    S2480PairMap_pairOf]
  refine S2480PairOf_eq_of_eq_or_neg ?_
  rcases hw with h | h
  · left
    exact Subtype.ext h.symm
  · right
    apply Subtype.ext
    rw [S2480NonzeroTorsionMap_coe, S2480NonzeroTorsion_neg_coe]
    have h' := congrArg (fun z : S2056Torsion => -z) h
    have h'' : -(S2172AffineBasis (normalize w)) =
        S2480PointMapTorsion σ (S2172AffineBasis x.1) := by
      simpa using h'
    exact h''.symm

/-- The canonical pair equivalence from the twelve S2009 pairs to the actual
pairs {+-P}. -/
noncomputable def S2480PairEquiv : S2009Pairs ≃ S2056Pair :=
  Equiv.ofBijective (S2180PairMap S2172AffineBasis)
    (S2186PairMap_bijective S2172AffineBasis)

@[simp] theorem S2480PairEquiv_apply (x : S2009Pairs) :
    S2480PairEquiv x = S2180PairMap S2172AffineBasis x := rfl

/-- **The matrix pair permutation and the Galois root permutation of the same
sigma are conjugate, hence have the same cycle type.** -/
theorem S2480RootPairEquiv_permCongr (σ : S1725AbsoluteGalois) :
    S2056RootPairEquiv.permCongr (S2480RootPerm σ) =
      S2480PairEquiv.permCongr
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)) := by
  ext y
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, S2480RootPerm_apply,
    S2056RootPairEquiv_equivariant, Equiv.apply_symm_apply]
  have h : S2480PairEquiv
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)
          (S2480PairEquiv.symm y)) =
      S2056PairMap σ (S2480PairEquiv (S2480PairEquiv.symm y)) := by
    change S2180PairMap S2172AffineBasis
        (pairAct
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)
          (S2480PairEquiv.symm y)) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis (S2480PairEquiv.symm y))
    exact S2480PairAction_apply σ _
  rw [h, Equiv.apply_symm_apply]

/-- **The cycle type of the matrix action of sigma on the twelve pairs is the
cycle type of the action of sigma on the twelve roots of psi_5.** -/
theorem S2480PairMatrix_cycleType (σ : S1725AbsoluteGalois) :
    (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
      (S2480RootPerm σ).cycleType := by
  rw [← S2132cycleType_permCongr (e := S2480PairEquiv)
    (σ := pairPermHom
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ))]
  rw [← S2480RootPairEquiv_permCongr σ]
  rw [S2132cycleType_permCongr]

/-! ## 3. The target as an arithmetic root-cycle statement -/

/-- The exact arithmetic form of the target: there is an F'-automorphism of
the algebraic closure whose permutation of the twelve actual roots of psi_5 has
cycle type (10, 2). -/
def S2480RootCycleTypeRequired : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    (S2480RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)

/-- The target is equivalent to the arithmetic root-cycle statement. -/
theorem S2480Target_iff_rootCycle :
    S2480Target ↔ S2480RootCycleTypeRequired := by
  rw [S2480Target_iff_exists_sigma]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    rw [S2480PairMatrix_cycleType σ] at hσ
    exact hσ
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    rw [S2480PairMatrix_cycleType σ]
    exact hσ

/-- The corrected Dedekind--Frobenius orbit-size form (S2217 vocabulary): the
orbit-size multiset of the root permutation is {10, 2}. -/
def S2480OrbitSizeRequired : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2480RootPerm σ) = ({10, 2} : Multiset ℕ)

/-- The orbit-size form is equivalent to the root-cycle form.  This is the
concrete form in which the corrected Dedekind--Frobenius theorem of S2217
states its conclusion when the factor degrees are 2 and 10. -/
theorem S2480RootCycleTypeRequired_iff_orbitSize :
    S2480RootCycleTypeRequired ↔ S2480OrbitSizeRequired := by
  have hinst : (Classical.decEq S2056Root) =
      (fun a b => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hcard : Fintype.card S2056Root = 12 := by
      rw [← Nat.card_eq_fintype_card, S2056Root_card]
    have hfix : Fintype.card (Function.fixedPoints (S2480RootPerm σ)) = 0 := by
      rw [Equiv.Perm.card_fixedPoints, hcard, hσ]
      norm_num
    unfold LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset
    rw [hinst, hσ, hfix, Multiset.replicate_zero, add_zero]
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hσ' := hσ
    unfold LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset at hσ'
    rw [hinst] at hσ'
    have hfix : Fintype.card (Function.fixedPoints (S2480RootPerm σ)) = 0 := by
      by_contra h
      have hmem : (1 : ℕ) ∈ (S2480RootPerm σ).cycleType +
          Multiset.replicate (Fintype.card (Function.fixedPoints (S2480RootPerm σ))) 1 :=
        Multiset.mem_add.mpr (Or.inr (Multiset.mem_replicate.mpr ⟨h, rfl⟩))
      rw [hσ'] at hmem
      norm_num at hmem
    rw [hfix, Multiset.replicate_zero, add_zero] at hσ'
    exact hσ'

/-- The target is equivalent to the orbit-size form. -/
theorem S2480Target_iff_orbitSize :
    S2480Target ↔ S2480OrbitSizeRequired :=
  S2480Target_iff_rootCycle.trans S2480RootCycleTypeRequired_iff_orbitSize

/-! ## 4. The exact first missing -/

/-- **The exact first missing**: an F'-automorphism of the algebraic closure
whose permutation of the twelve actual roots of psi_5 has cycle type (10, 2).
Equivalent to the target; no inhabitant is asserted. -/
def S2480FirstMissing : Prop := S2480RootCycleTypeRequired

/-- The exact first missing is equivalent to the target. -/
theorem S2480FirstMissing_iff_target : S2480FirstMissing ↔ S2480Target :=
  S2480Target_iff_rootCycle.symm

/-- The first missing gives the target. -/
theorem S2480Target_of_firstMissing (h : S2480FirstMissing) : S2480Target :=
  S2480FirstMissing_iff_target.mp h

/-- Together with pair transitivity of the actual range, the first missing
gives the S1987 D5 large-image target (S2203). -/
theorem S2480D5LargeImageFive_of_firstMissing_and_pair
    (h : S2480FirstMissing)
    (hpair : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis
    (S2480Target_of_firstMissing h) hpair

/-! ## 5. Consumers of the target -/

/-- The target forces 10 to divide the order of the actual mod-5 image. -/
theorem S2480TenDvd_range (h : S2480Target) :
    10 ∣ Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range := by
  obtain ⟨h, hh, hc⟩ := S2480Target_iff_range.mp h
  exact ten_dvd_natCard_of_mem_cycleType102 hh hc

/-- The target forces 5 to divide the order of the actual mod-5 image. -/
theorem S2480FiveDvd_range (h : S2480Target) :
    5 ∣ Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  dvd_trans (by norm_num : 5 ∣ 10) (S2480TenDvd_range h)

/-- The target excludes the two proper subgroup orders 96 and 48 of the
Dickson list. -/
theorem S2480Range_card_ne_96_and_ne_48 (h : S2480Target) :
    Nat.card
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ≠ 96 ∧
      Nat.card
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ≠ 48 := by
  constructor
  · intro h96
    exact no_cycleType102_of_natCard_96 _ h96 (S2480Target_iff_range.mp h)
  · intro h48
    exact no_cycleType102_of_natCard_48 _ h48 (S2480Target_iff_range.mp h)

/-! ## 6. The actual S2132/S2167/S2217/S2126/S2055 inputs -/

/-- The honest Frobenius cycle-type statement of S2132, in its splitting-field
form. -/
def S2480S2132SplittingFieldCycle : Prop :=
  LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132FrobInducesPairCycleType

/-- The S2132 honest statement is definitionally the S2132 statement. -/
theorem S2480S2132SplittingFieldCycle_iff :
    S2480S2132SplittingFieldCycle ↔
      LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132FrobInducesPairCycleType :=
  Iff.rfl

/-- The general Dedekind--Frobenius orbit-size theorem of S2217. -/
def S2480DedekindFrobeniusMissing : Prop :=
  LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.S2217Missing

/-- The S2217 missing theorem is definitionally the S2217 statement. -/
theorem S2480DedekindFrobeniusMissing_iff :
    S2480DedekindFrobeniusMissing ↔
      LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.S2217Missing :=
  Iff.rfl

/-- The corrected mod-29 product certificate of S2132 (actual). -/
theorem S2480Mod29ProductActual :
    LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132F2Z.map
        (Int.castRingHom (ZMod 29)) *
      LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132F10Z.map
        (Int.castRingHom (ZMod 29)) =
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
      (Int.castRingHom (ZMod 29)) :=
  LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132CorrectedProduct

/-- The S2126 degree-ten factor is irreducible (actual, kernel checked). -/
theorem S2480Mod29TenIrreducibleActual :
    Irreducible LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10 :=
  LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10_irreducible

/-- The only unproved finite micro-input of the corrected mod-29 certificate. -/
def S2480Mod29QuadraticMissing : Prop :=
  LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.S2167QuadraticIrreducible

/-- The S2057 mod-29 factorization datum is uninhabitable, because no
integer-coefficient polynomial models the rational psi_5 (S2132). -/
theorem S2480S2057FactorizationData_uninhabitable :
    ¬ Nonempty LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Mod29FactorizationData :=
  LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132Mod29FactorizationData_empty

/-- No integer-coefficient polynomial models the actual rational psi_5. -/
theorem S2480NoIntegerModel :
    ¬ ∃ P : ℤ[X],
      P.map (Int.castRingHom ℚ) =
        LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5Q :=
  LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132NoIntegerModel

/-- The Dickson large-image input of S2055, re-exported for the consumer. -/
theorem S2480LargeImage_of_dickson (H : Subgroup GL2) (hdet : DetSurjectiveOn H)
    (htrans : PairTransitive H) (h102 : HasCycleType102 H) : H = ⊤ :=
  LeanFormal.IUT.XiFPaper.S2055DicksonClassActual.S2055LargeImage_of_dickson
    H hdet htrans h102

/-! ## 7. Axiom footprint -/

#print axioms S2480Target_iff_range
#print axioms S2480cycleType_pairPermHom_conj
#print axioms S2480HasCycleType102_map_conj
#print axioms S2480RangeCycleType_congr
#print axioms S2480Target_iff_basis
#print axioms S2480Target_iff_forall_basis
#print axioms S2480Target_iff_exists_basis
#print axioms S2480Target_iff_exists_sigma
#print axioms S2480RootPerm
#print axioms S2480PointMapTorsion
#print axioms S2480AffineTorsionEquiv_galois
#print axioms S2480MatrixRep_affine
#print axioms S2480MatrixRep_smul_point
#print axioms S2480MatrixRep_smul_torsion
#print axioms S2480PairOf
#print axioms S2480PairOf_eq_of_eq_or_neg
#print axioms S2480PairMap_pairOf
#print axioms S2480S2180PairMap_eq_pairOf
#print axioms S2480PairAction_apply
#print axioms S2480PairEquiv
#print axioms S2480PairEquiv_apply
#print axioms S2480RootPairEquiv_permCongr
#print axioms S2480PairMatrix_cycleType
#print axioms S2480Target_iff_rootCycle
#print axioms S2480RootCycleTypeRequired_iff_orbitSize
#print axioms S2480Target_iff_orbitSize
#print axioms S2480FirstMissing_iff_target
#print axioms S2480Target_of_firstMissing
#print axioms S2480D5LargeImageFive_of_firstMissing_and_pair
#print axioms S2480TenDvd_range
#print axioms S2480FiveDvd_range
#print axioms S2480Range_card_ne_96_and_ne_48
#print axioms S2480S2132SplittingFieldCycle_iff
#print axioms S2480DedekindFrobeniusMissing_iff
#print axioms S2480Mod29ProductActual
#print axioms S2480Mod29TenIrreducibleActual
#print axioms S2480S2057FactorizationData_uninhabitable
#print axioms S2480NoIntegerModel
#print axioms S2480LargeImage_of_dickson

end LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

end
