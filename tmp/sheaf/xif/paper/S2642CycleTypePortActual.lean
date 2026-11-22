/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual

/-!
# S2461: the actual range cycle-type target and its exact first missing

## The target

  S2461Target := S2203RangeCycleTypeRequired S1982Basis
    = HasCycleType102
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

with

* E' = S1720Curve the actual punctured elliptic curve over the actual number
  field F' = S1720Field (S1720);
* S1982Basis the actual rank-two ZMod-5-basis of E'[5] (S1982);
* galoisLTorsionMatrixRepresentation 5 S1982Basis the actual mod-5 matrix
  representation of Gal(closure F' / F') in that basis (EllipticTorsion);
* HasCycleType102 H (S2009): some h in H acts on the twelve pairs {+-v} of
  nonzero vectors of F_5^2 with permutation cycle type (10, 2).

## Status

The target is NOT proved here, and no inhabitant is produced.  No sorry, no
admit, no axiom, no opaque declaration, no True/PUnit gate, no native_decide,
no conditional object announced as actual.

## Proved reductions (all kernel checked)

1. The pair cycle type of a matrix is a class function on GL_2(F_5)
   (S2461cycleType_pairPermHom_conj, S2461HasCycleType102_map_conj).
2. Hence the target is independent of the rank-two basis
   (S2461RangeCycleType_congr, S2461Target_iff_basis) and equals the
   universal- and existential-basis forms (S2461Target_iff_forall_basis,
   S2461Target_iff_exists_basis).
3. The target is the existence of an absolute Galois element whose mod-5
   matrix has pair cycle type (10, 2) (S2461Target_iff_exists_sigma).
4. The matrix formulation is transported to the actual twelve pairs {+-P} of
   nonzero 5-torsion points of E'.  Along the basis-compatible bijection
   S2180PairMap S2172AffineBasis : S2009Pairs ~= S2056Pair (S2186), the pair
   action of the matrix of sigma is the actual Galois action S2056PairMap sigma
   on those pairs (S2461PairAction_comm), hence the two permutations have the
   same cycle type (S2461PairMatrix_cycleType).
5. The pairs are the twelve actual roots of psi_5.  Along the canonical
   x-coordinate bijection S2056RootPairEquiv (S2056, Galois equivariant), the
   action on pairs is the action on the roots of the actual odd 5-division
   polynomial psi_5, hence the pair permutation and the root permutation have
   the same cycle type (S2461PairPerm_cycleType_eq_rootPerm).
6. Combining 3-5: the target is exactly the existence of an F'-automorphism of
   the algebraic closure acting on the twelve roots of psi_5 with cycle type
   (10, 2) (S2461Target_iff_exists_rootCycle).

## Exact first missing

S2461FirstMissing below is the root-permutation statement of item 6, provably
equivalent to the target.  This is the form in which the Dedekind--Frobenius
theorem delivers its output: the arithmetic Frobenius at a prime above 29 has
root cycle type (10, 2) because psi_5 has an irreducible quadratic and an
irreducible degree-ten factor modulo 29.  The formal bridge from the residual
factorization to the cycle type is analysed in S2132, S2167, S2217 and is not
available in this tree; no inhabitant of S2461FirstMissing is asserted here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2642CycleTypePortActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual

/-! ## 1. The exact target -/

/-- The actual range cycle-type target at the selected rank-two basis:
the mod-5 image of Gal(closure F' / F') contains an element whose action on the
twelve pairs {+-v} has cycle type (10, 2). -/
def S2461Target : Prop := S2203RangeCycleTypeRequired S1982Basis

/-- The target unfolded. -/
theorem S2461Target_iff_range :
    S2461Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The target with the prime label read as the definitionally equal S1982Five. -/
theorem S2461Target_iff_range1982 :
    S2461Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis).range :=
  Iff.rfl

/-! ## 2. Conjugation invariance of the pair cycle type -/

/-- Conjugation in GL_2(F_5) preserves the pair cycle type. -/
theorem S2461cycleType_pairPermHom_conj (c g : GL2) :
    (pairPermHom (c * g * c⁻¹)).cycleType = (pairPermHom g).cycleType := by
  rw [map_mul, map_mul, map_inv]
  exact Equiv.Perm.cycleType_conj

/-- Cycle type (10, 2) is invariant under conjugating the subgroup. -/
theorem S2461HasCycleType102_map_conj (c : GL2) (H : Subgroup GL2) :
    HasCycleType102 (Subgroup.map (MulAut.conj c).toMonoidHom H) ↔
      HasCycleType102 H := by
  constructor
  · rintro ⟨h, hh, hc⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨g, hg, hgk⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgk
    refine ⟨g, hg, ?_⟩
    rw [← S2461cycleType_pairPermHom_conj c g]
    exact hgk ▸ hc
  · rintro ⟨g, hg, hc⟩
    refine ⟨c * g * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨g, hg, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [S2461cycleType_pairPermHom_conj]
      exact hc

/-! ## 3. Independence of the rank-two basis -/

/-- The cycle-type hypothesis does not depend on the rank-two basis.  The
ranges at two bases are conjugate (S1894), and the pair cycle type is a class
function on GL_2(F_5). -/
theorem S2461RangeCycleType_congr (b b' : S1725TorsionBasis S1987Five) :
    HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b').range := by
  rw [S1894MatrixRep_range_conj S1987Five b b']
  exact (S2461HasCycleType102_map_conj
    (S1894BasisChangeGL S1987Five b b')
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range).symm

/-- The target is the cycle-type hypothesis at any chosen rank-two basis. -/
theorem S2461Target_iff_basis (b : S1725TorsionBasis S1987Five) :
    S2461Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2461Target_iff_range.trans (S2461RangeCycleType_congr S1982Basis b)

/-- The target is the basis-free (universal) form of the cycle-type hypothesis. -/
theorem S2461Target_iff_forall_basis :
    S2461Target ↔ ∀ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h b
    exact (S2461Target_iff_basis b).mp h
  · intro h
    exact (S2461Target_iff_basis S1982Basis).mpr (h S1982Basis)

/-- The target is the existential-basis form of the cycle-type hypothesis. -/
theorem S2461Target_iff_exists_basis :
    S2461Target ↔ ∃ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h
    exact ⟨S1982Basis, (S2461Target_iff_basis S1982Basis).mp h⟩
  · rintro ⟨b, hb⟩
    exact (S2461Target_iff_basis b).mpr hb

/-- The target is the existence of a Galois element whose mod-5 matrix has pair
cycle type (10, 2). -/
theorem S2461Target_iff_exists_sigma :
    S2461Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) := by
  rw [S2461Target_iff_range]
  change (∃ h : GL (Fin 2) (ZMod S1987Five.value),
      h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ∧
        (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)) ↔ _
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, hc⟩

/-! ## 4. Consumers of the target -/

/-- The target gives the S1987 D5 large-image target together with the twelve
pair transitivity of the actual range (S2132/S2203). -/
theorem S2461D5LargeImageFive_of_target_and_transitive
    (h102 : S2461Target)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis h102 htrans

/-- The target forces 10 to divide the order of the actual mod-5 image. -/
theorem S2461TenDvd_range (h : S2461Target) :
    10 ∣ Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range := by
  obtain ⟨h, hh, hc⟩ := S2461Target_iff_range.mp h
  exact ten_dvd_natCard_of_mem_cycleType102 hh hc

/-- The target forces 5 to divide the order of the actual mod-5 image. -/
theorem S2461FiveDvd_range (h : S2461Target) :
    5 ∣ Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  dvd_trans (by norm_num : 5 ∣ 10) (S2461TenDvd_range h)

/-- The target excludes the two proper subgroup orders of the Dickson list. -/
theorem S2461Range_card_ne_96_and_ne_48 (h : S2461Target) :
    Nat.card
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ≠ 96 ∧
      Nat.card
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ≠ 48 := by
  constructor
  · intro h96
    exact no_cycleType102_of_natCard_96 _ h96 (S2461Target_iff_range.mp h)
  · intro h48
    exact no_cycleType102_of_natCard_48 _ h48 (S2461Target_iff_range.mp h)

/-! ## 5. The actual twelve pairs {+-P} of nonzero 5-torsion points -/

/-- The pair {P, -P} attached to a nonzero 5-torsion point. -/
noncomputable def S2461PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
  ⟨{P, -P}, Finset.card_pair (S2056_ne_neg P), by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · refine Or.inl ?_
      apply Subtype.ext
      apply Subtype.ext
      exact neg_neg _⟩

/-- The negation on the nonzero 5-torsion is involutive. -/
theorem S2461_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The pair attached to a point equals the pair attached to its negative. -/
theorem S2461PairOf_neg (P : S2056NonzeroTorsion) :
    S2461PairOf (-P) = S2461PairOf P := by
  apply Subtype.ext
  show (insert (-P) (Finset.singleton (-(-P)))) =
    insert P (Finset.singleton (-P))
  rw [S2461_neg_neg]
  exact Finset.pair_comm (-P) P

/-- The pair of a point only depends on the pair, not on the chosen sign. -/
theorem S2461PairOf_congr {P Q : S2056NonzeroTorsion} (h : Q = P ∨ Q = -P) :
    S2461PairOf Q = S2461PairOf P := by
  rcases h with rfl | rfl
  · rfl
  · exact S2461PairOf_neg P

/-- A nonzero coordinate vector stays nonzero in the affine 5-torsion. -/
theorem S2461E_ne_zero (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    ((e v : S2056Torsion) : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : e v = 0 := Subtype.ext h
  exact hv (e.injective (by rw [h0, map_zero]))

/-- The basis-compatible pair map is the pair-of map. -/
theorem S2461S2180PairMap_eq
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) (x : S2009Pairs) :
    S2180PairMap e x = S2461PairOf ⟨e x.1, S2461E_ne_zero e x.1 (isRep_ne_zero x.1 x.2)⟩ :=
  rfl

/-- The Galois action on the actual pairs sends the pair of P to the pair of
sigma P. -/
theorem S2461PairMap_pairOf (σ : S1725AbsoluteGalois) (P : S2056NonzeroTorsion) :
    S2056PairMap σ (S2461PairOf P) =
      S2461PairOf (S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  change (Finset.image (S2056NonzeroTorsionMap σ) (insert P (Finset.singleton (-P))))
    = insert (S2056NonzeroTorsionMap σ P)
        (Finset.singleton (-(S2056NonzeroTorsionMap σ P)))
  rw [Finset.image_insert, Finset.image_singleton, S2056NonzeroTorsionMap_neg]

/-- The Galois action on pairs is injective. -/
theorem S2461PairMap_injective (σ : S1725AbsoluteGalois) :
    Function.Injective (S2056PairMap σ) := by
  intro S T hST
  have hf : Function.Injective (S2056NonzeroTorsionMap σ) := S2056NonzeroTorsionMap_injective σ
  have himg : S.1.image (S2056NonzeroTorsionMap σ) = T.1.image (S2056NonzeroTorsionMap σ) :=
    congrArg Subtype.val hST
  apply Subtype.ext
  exact (Finset.image_inj hf).mp himg

/-- The Galois action on the twelve actual pairs as a permutation. -/
noncomputable def S2461PairPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Pair :=
  Equiv.ofBijective (S2056PairMap σ)
    (Finite.injective_iff_bijective.mp (S2461PairMap_injective σ))

/-- The Galois action on the twelve roots of psi_5 as a permutation. -/
noncomputable def S2461RootPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Root :=
  Equiv.ofBijective (S2056RootMap σ)
    (Finite.injective_iff_bijective.mp (by
      intro x y h
      apply Subtype.ext
      exact σ.injective (congrArg Subtype.val h)))

/-! ## 6. The matrix pair action is the actual Galois action on the pairs -/

/-- The projective/affine comparison intertwines the Galois action with the
affine point map. -/
theorem S2461AffineTorsionEquiv_galois (σ : S1725AbsoluteGalois)
    (P : S1720Curve.LTorsion S1982Five) :
    ((S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five σ P) :
        S2056Torsion) : S2056W.Point) =
      S2056PointMap σ ((S2172AffineTorsionEquiv P : S2056Torsion) : S2056W.Point) := by
  change S1906ProjAffineEquiv (S1720Curve.galoisActionOnPoint σ
      (P : WeierstrassCurve.Projective.Point S2056W)) =
    WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) σ.toAlgHom
      (S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W))
  unfold PuncturedEllipticCurve.galoisActionOnPoint S1906ProjAffineEquiv
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
    AddEquiv.apply_symm_apply]

/-- The matrix representation acts on the projective torsion through the actual
Galois action. -/
theorem S2461MatrixRep_galois (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    S1982Basis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v) =
      S1720Curve.galoisActionOnLTorsion S1982Five σ (S1982Basis v) := by
  have h := S1894MatrixRep_acts (l := S1982Five) (b := S1982Basis) (sigma := σ) v
  simpa [PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply] using h

/-- The module action of a general linear matrix is its linear equivalence. -/
theorem S2461Basis_toLin (g : GL2) (v : Fin 2 → ZMod S1982Five.value) :
    (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv v = g • v := by
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, ← Matrix.smul_eq_mulVec]
  rfl

/-- The affine basis transports the matrix action to the actual point map. -/
theorem S2461AffineBasis_galois (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    ((S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v) :
        S2056Torsion) : S2056W.Point) =
      S2056PointMap σ ((S2172AffineBasis v : S2056Torsion) : S2056W.Point) := by
  have h1 : S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v) =
      S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five σ (S1982Basis v)) := by
    show S2172AffineTorsionEquiv (S1982Basis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv v)) =
      S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five σ (S1982Basis v))
    rw [S2461MatrixRep_galois]
  rw [h1]
  show ((S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five σ (S1982Basis v)) :
      S2056Torsion) : S2056W.Point) =
    S2056PointMap σ
      ((S2172AffineTorsionEquiv (S1982Basis v) : S2056Torsion) : S2056W.Point)
  exact S2461AffineTorsionEquiv_galois σ (S1982Basis v)

/-- **The pair action of the mod-5 matrix of sigma is the actual Galois action
on the twelve pairs {+-P} of nonzero 5-torsion points of E'.** -/
theorem S2461PairAction_comm (σ : S1725AbsoluteGalois) (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis
        (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) x) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis x) := by
  have hv : x.1 ≠ 0 := isRep_ne_zero x.1 x.2
  have hAx : ((S2172AffineBasis x.1 : S2056Torsion) : S2056W.Point) ≠ 0 :=
    S2461E_ne_zero S2172AffineBasis x.1 hv
  have hgv : (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1 ≠ 0 := by
    rw [← S2461Basis_toLin]
    intro h0
    exact hv ((Matrix.GeneralLinearGroup.toLin
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv.injective
        (by rw [h0, map_zero]))
  have hAgx : ((S2172AffineBasis
      ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) :
        S2056Torsion) : S2056W.Point) ≠ 0 :=
    S2461E_ne_zero S2172AffineBasis _ hgv
  have hAn : ((S2172AffineBasis (normalize
      ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1)) :
        S2056Torsion) : S2056W.Point) ≠ 0 := by
    rcases normalize_eq_or_neg
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) with h | h
    · rw [h]; exact hAgx
    · rw [h, map_neg]
      exact neg_ne_zero.mpr hAgx
  have hpt : S2056PointMap σ ((S2172AffineBasis x.1 : S2056Torsion) : S2056W.Point)
      = ((S2172AffineBasis
          ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) :
            S2056Torsion) : S2056W.Point) := by
    rw [← S2461AffineBasis_galois σ x.1, S2461Basis_toLin]
  have hMap : S2056NonzeroTorsionMap σ (⟨S2172AffineBasis x.1, hAx⟩ : S2056NonzeroTorsion)
      = ⟨S2172AffineBasis
          ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1), hAgx⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpt
  rw [S2461S2180PairMap_eq, S2461PairMap_pairOf, S2461S2180PairMap_eq, hMap]
  refine S2461PairOf_congr ?_
  rcases normalize_eq_or_neg
      ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) with h | h
  · left
    apply Subtype.ext
    apply Subtype.ext
    rw [h]
  · right
    apply Subtype.ext
    apply Subtype.ext
    rw [h, map_neg]
    rfl

/-! ## 7. The cycle type on the pairs and on the roots of psi_5 -/

/-- The basis-compatible bijection between the twelve S2009 pairs and the
twelve actual pairs. -/
noncomputable def S2461PairEquiv : S2009Pairs ≃ S2056Pair :=
  Equiv.ofBijective (S2180PairMap S2172AffineBasis)
    (S2186PairMap_bijective S2172AffineBasis)

/-- Relabelling along an equivalence preserves the cycle type. -/
theorem S2461cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have hperm : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype (h := trivial), Equiv.permCongr_apply]
    rfl
  rw [hperm]
  exact Equiv.Perm.cycleType_extendDomain _

/-- **The pair cycle type of the mod-5 matrix of sigma equals the cycle type of
the actual Galois permutation of the twelve pairs {+-P}.** -/
theorem S2461PairMatrix_cycleType (σ : S1725AbsoluteGalois) :
    (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
      (S2461PairPerm σ).cycleType := by
  have hconj : S2461PairEquiv.permCongr
      (pairPermHom (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ))
        = S2461PairPerm σ := by
    ext x
    have happ : S2461PairEquiv (S2461PairEquiv.symm x) = x := Equiv.apply_symm_apply _ x
    change S2180PairMap S2172AffineBasis
      (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)
        (S2461PairEquiv.symm x)) = S2056PairMap σ x
    rw [S2461PairAction_comm]
    change S2056PairMap σ (S2461PairEquiv (S2461PairEquiv.symm x)) = S2056PairMap σ x
    rw [happ]
  rw [← hconj, S2461cycleType_permCongr]

/-- The pair cycle type equals the cycle type of the permutation of the twelve
actual roots of psi_5. -/
theorem S2461PairPerm_cycleType_eq_rootPerm (σ : S1725AbsoluteGalois) :
    (S2461PairPerm σ).cycleType = (S2461RootPerm σ).cycleType := by
  have hconj : S2056RootPairEquiv.permCongr (S2461RootPerm σ) = S2461PairPerm σ := by
    ext x
    have happ : S2056RootPairEquiv (S2056RootPairEquiv.symm x) = x :=
      Equiv.apply_symm_apply _ x
    change S2056RootPairEquiv (S2056RootMap σ (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [S2056RootPairEquiv_equivariant]
    change S2056PairMap σ (S2056RootPairEquiv (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [happ]
  rw [← hconj, S2461cycleType_permCongr]

/-! ## 8. The cycle-type statement in pair and root form -/

/-- The target in pair form: some F'-automorphism of the algebraic closure acts
on the twelve actual pairs {+-P} with cycle type (10, 2). -/
theorem S2461Target_iff_exists_pairCycle :
    S2461Target ↔ ∃ σ : S1725AbsoluteGalois,
      (S2461PairPerm σ).cycleType = ({10, 2} : Multiset ℕ) := by
  rw [S2461Target_iff_exists_sigma]
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨σ, (S2461PairMatrix_cycleType σ).symm.trans h⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, (S2461PairMatrix_cycleType σ).trans h⟩

/-- The target in root form: some F'-automorphism of the algebraic closure acts
on the twelve roots of the actual odd 5-division polynomial psi_5 with cycle
type (10, 2). -/
theorem S2461Target_iff_exists_rootCycle :
    S2461Target ↔ ∃ σ : S1725AbsoluteGalois,
      (S2461RootPerm σ).cycleType = ({10, 2} : Multiset ℕ) := by
  rw [S2461Target_iff_exists_pairCycle]
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨σ, (S2461PairPerm_cycleType_eq_rootPerm σ).symm.trans h⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, (S2461PairPerm_cycleType_eq_rootPerm σ).trans h⟩

/-! ## 9. The exact first missing -/

/-- **The exact first missing statement**: there is an F'-automorphism of the
algebraic closure of F' whose permutation of the twelve roots of psi_5 has
cycle type (10, 2).  By S2461Target_iff_exists_rootCycle this is equivalent to
the actual range cycle-type target.  No inhabitant is asserted. -/
def S2461FirstMissing : Prop :=
  ∃ σ : S1725AbsoluteGalois, (S2461RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)

/-- The exact first missing statement is literally the target. -/
theorem S2461FirstMissing_iff_target : S2461FirstMissing ↔ S2461Target :=
  (S2461Target_iff_exists_rootCycle).symm

/-- The exact first missing gives the target. -/
theorem S2461Target_of_firstMissing (h : S2461FirstMissing) : S2461Target :=
  S2461Target_iff_exists_rootCycle.mpr h

/-- Together with pair transitivity of the actual range, the first missing
statement gives the S1987 D5 target. -/
theorem S2461D5LargeImageFive_of_firstMissing
    (h : S2461FirstMissing)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range) :
    S1987D5LargeImageFive :=
  S2461D5LargeImageFive_of_target_and_transitive
    (S2461Target_of_firstMissing h) htrans

/-! ## 10. Axiom footprint -/

#print axioms S2461Target_iff_range
#print axioms S2461cycleType_pairPermHom_conj
#print axioms S2461HasCycleType102_map_conj
#print axioms S2461RangeCycleType_congr
#print axioms S2461Target_iff_basis
#print axioms S2461Target_iff_forall_basis
#print axioms S2461Target_iff_exists_basis
#print axioms S2461Target_iff_exists_sigma
#print axioms S2461TenDvd_range
#print axioms S2461FiveDvd_range
#print axioms S2461Range_card_ne_96_and_ne_48
#print axioms S2461PairOf
#print axioms S2461PairOf_neg
#print axioms S2461PairOf_congr
#print axioms S2461PairMap_pairOf
#print axioms S2461PairMap_injective
#print axioms S2461PairPerm
#print axioms S2461RootPerm
#print axioms S2461AffineTorsionEquiv_galois
#print axioms S2461MatrixRep_galois
#print axioms S2461Basis_toLin
#print axioms S2461AffineBasis_galois
#print axioms S2461PairAction_comm
#print axioms S2461PairEquiv
#print axioms S2461cycleType_permCongr
#print axioms S2461PairMatrix_cycleType
#print axioms S2461PairPerm_cycleType_eq_rootPerm
#print axioms S2461Target_iff_exists_pairCycle
#print axioms S2461Target_iff_exists_rootCycle
#print axioms S2461FirstMissing_iff_target

end LeanFormal.IUT.XiFPaper.S2642CycleTypePortActual

end
