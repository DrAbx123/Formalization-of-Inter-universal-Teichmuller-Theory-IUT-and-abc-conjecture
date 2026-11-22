/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

/-!
# S2501: the actual matrix-pair / affine-pair / root equivariance

## The object

S2480's minimal missing statement is

  S2480FirstMissing := S2480RootCycleTypeRequired
    = there is sigma in Gal(K/F') with
        (S2480RootPerm sigma).cycleType = (10, 2),

where K = AlgebraicClosure F' and S2480RootPerm is the action of sigma on the
twelve roots of psi_5 over K (S2056).  The equivalent matrix form uses the
actual mod-5 matrix representation rho_{5, S1982Basis} of E'/F' in the
rank-two basis S1982Basis of E'[5] (S1894), acting on the twelve pairs
{+-v} of F_5^2  {0} through pairPermHom (S2009); the equivalence is
S2480PairMatrix_cycleType (or the independent S2501PairMatrix_cycleType
below).  The S2132 honest target (S2132FrobInducesPairCycleType) instead
speaks about an F'-automorphism of the psi_5 splitting field
S2057FiveDivisionField and its permutation of the twelve roots of psi_5.

This file proves the finite/equivariance half of the comparison:

* the actual Galois action of sigma : Gal(K/F') on the affine 5-torsion
  E'(K)[5] (built from S2056PointMap) is the projective Galois action
  transported through the actual projective/affine equivalence
  S1906ProjAffineEquiv (S1906), so it is the honest affine action;
* on the affine torsion, the actual action equals the matrix action of
  rho_{5, S1982Basis} sigma transported through the actual affine lift
  S2172AffineBasis of the S1982 basis;
* consequently the permutation of the twelve affine pairs {+-P} induced by
  sigma is the matrix pair action of rho_{5, S1982Basis} sigma, conjugated
  by the basis-compatible pair bijection of S2180/S2186.  In particular the
  two permutations have the same cycle type;
* composing with the S2056 root-to-pair equivariance, the cycle type of the
  matrix pair action of sigma is the cycle type of the action of sigma on
  the twelve psi_5 roots over K;
* therefore S2480FirstMissing is equivalent to the existence of
  sigma : Gal(K/F') whose matrix pair permutation at S1982Basis has cycle
  type (10, 2), and the S2132 pair/root cycle-type data gets a literal
  matrix-range reading via S2229/S2243.

## Exact missing

The only remaining step from the S2132 target to S2480FirstMissing is the
transport from automorphisms of the splitting field
S2057FiveDivisionField to automorphisms of the algebraic closure K, with
the identification of the two twelve-element root sets.  This is recorded as
S2501RootCycleTransferRequired below; its consequence
S2501S2132ToFirstMissingRequired (S2132FrobInducesPairCycleType implies
S2480FirstMissing) is the exact implication still missing.  Neither is
inhabited here.

Every declaration below is an ordinary definition or theorem: no proof
placeholder and no unchecked decision oracle is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

/-! ## 1. The actual affine Galois action on the 5-torsion

S2056PointMap sigma is the affine point map of sigma on W = E'_K (S2056).
Restricting it to the 5-torsion gives the actual affine action used below;
S1906ProjAffineEquiv (the projective/affine additive equivalence) is shown to
intertwine it with the projective Galois action of
PuncturedEllipticCurve.galoisActionOnPoint. -/

/-- The actual Galois action of an absolute Galois element on the affine
5-torsion E'(K)[5], as an additive endomorphism. -/
noncomputable def S2501AffineTorsionGalois (sigma : S1725AbsoluteGalois) :
    S2056Torsion →+ S2056Torsion where
  toFun P := ⟨S2056PointMap sigma (P : S2056W.Point), by
    have h := S2056PointMap_torsion sigma P.2
    simpa using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

@[simp] theorem S2501AffineTorsionGalois_coe (sigma : S1725AbsoluteGalois)
    (P : S2056Torsion) :
    (S2501AffineTorsionGalois sigma P : S2056W.Point) =
      S2056PointMap sigma (P : S2056W.Point) := rfl

/-- The affine/projective comparison intertwines the actual Galois action:
the affine point map of sigma is the conjugate of the projective Galois
action of sigma by the projective/affine additive equivalence. -/
theorem S2501AffineTorsionEquiv_galois (sigma : S1725AbsoluteGalois)
    (P : S1720Curve.LTorsion S1982Five) :
    (S2172AffineTorsionEquiv (S1720Curve.galoisActionOnLTorsion S1982Five sigma P) :
        S2056W.Point) =
      S2056PointMap sigma (S2172AffineTorsionEquiv P : S2056W.Point) := by
  change S1906ProjAffineEquiv (S1720Curve.galoisActionOnPoint sigma
      (P : WeierstrassCurve.Projective.Point S2056W)) =
    WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) sigma.toAlgHom
      (S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W))
  unfold PuncturedEllipticCurve.galoisActionOnPoint S1906ProjAffineEquiv
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply]

/-- The matrix representation acts on the affine torsion through the actual
Galois action (S1894 plus the projective/affine comparison above). -/
theorem S2501MatrixRep_affine (sigma : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).toLinearEquiv
          v) : S2056W.Point) =
      S2056PointMap sigma (S2172AffineBasis v : S2056W.Point) := by
  have h := S1894MatrixRep_acts S1982Five S1982Basis sigma v
  calc
    (S2172AffineBasis ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).toLinearEquiv
          v) : S2056W.Point)
        = (S2172AffineTorsionEquiv (S1982Basis ((Matrix.GeneralLinearGroup.toLin
            (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).toLinearEquiv
              v)) : S2056W.Point) := rfl
    _ = (S2172AffineTorsionEquiv
          (S1720Curve.galoisActionOnLTorsionLinearEquiv S1982Five sigma (S1982Basis v)) :
            S2056W.Point) := by rw [h]
    _ = (S2172AffineTorsionEquiv
          (S1720Curve.galoisActionOnLTorsion S1982Five sigma (S1982Basis v)) :
            S2056W.Point) := by
          rw [PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply]
    _ = S2056PointMap sigma (S2172AffineTorsionEquiv (S1982Basis v) : S2056W.Point) :=
          S2501AffineTorsionEquiv_galois sigma _
    _ = S2056PointMap sigma (S2172AffineBasis v : S2056W.Point) := rfl

/-- The same statement with the module action instead of the linear-map
action. -/
theorem S2501MatrixRep_smul_point (sigma : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) • v) :
          S2056W.Point) =
      S2056PointMap sigma (S2172AffineBasis v : S2056W.Point) := by
  rw [← S2501MatrixRep_affine sigma v]
  congr 1

/-- The module-action form in the actual affine torsion group. -/
theorem S2501MatrixRep_smul_torsion (sigma : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) • v) =
      S2501AffineTorsionGalois sigma (S2172AffineBasis v) := by
  apply Subtype.ext
  exact S2501MatrixRep_smul_point sigma v

/-! ## 2. The pair computation

The twelve affine pairs are the two-element negation-closed finite sets of
nonzero 5-torsion points (S2056).  The basis-compatible pair map of S2180
sends a representative x of F_5^2 \ {0} to {e x, -e x} for the actual
affine basis e = S2172AffineBasis.  We prove that this map conjugates the
matrix pair action pairAct (S2009) into the actual Galois action
S2056PairMap. -/

/-- Negation on the nonzero 5-torsion is involutive. -/
theorem S2501_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The standard pair {P, -P} of a nonzero 5-torsion point. -/
noncomputable def S2501PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
  ⟨{P, -P}, Finset.card_pair (S2056_ne_neg P), by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (S2501_neg_neg P)⟩

/-- The standard pair of a point determines the pair. -/
theorem S2501PairOf_eq_of_eq_or_neg {P Q : S2056NonzeroTorsion}
    (h : Q = P ∨ Q = -P) : S2501PairOf P = S2501PairOf Q := by
  apply Subtype.ext
  rcases h with rfl | rfl
  · rfl
  · show ({P, -P} : Finset S2056NonzeroTorsion) = {-P, -(-P)}
    rw [S2501_neg_neg P]
    exact Finset.pair_comm P (-P)

/-- The Galois action on a standard pair is the standard pair of the Galois
action. -/
theorem S2501PairMap_pairOf (sigma : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    S2056PairMap sigma (S2501PairOf P) =
      S2501PairOf (S2056NonzeroTorsionMap sigma P) := by
  apply Subtype.ext
  ext Q
  simp only [S2501PairOf, S2056PairMap, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image]
  constructor
  · rintro ⟨R, hR, rfl⟩
    rcases hR with rfl | rfl
    · exact Or.inl rfl
    · rw [S2056NonzeroTorsionMap_neg]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨P, Or.inl rfl, rfl⟩
    · exact ⟨-P, Or.inr rfl, S2056NonzeroTorsionMap_neg sigma P⟩

/-- The affine basis image of a nonzero coordinate vector is nonzero. -/
theorem S2501E_ne_zero (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    (S2172AffineBasis v : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : S2172AffineBasis v = 0 := Subtype.ext h
  exact hv (S2172AffineBasis.injective (by rw [h0, map_zero]))

/-- The S2180 basis-compatible pair map is the standard pair of the affine
basis image. -/
theorem S2501S2180PairMap_eq_pairOf (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis x =
      S2501PairOf ⟨S2172AffineBasis x.1,
        S2501E_ne_zero x.1 (isRep_ne_zero x.1 x.2)⟩ := by
  apply Subtype.ext
  apply Finset.ext
  intro Q
  simp [S2180PairMap, S2501PairOf]

/-- Coercion of the custom negation on nonzero 5-torsion. -/
theorem S2501NonzeroTorsion_neg_coe (P : S2056NonzeroTorsion) :
    ((-P : S2056NonzeroTorsion) : S2056Torsion) = -P.1 := by
  apply Subtype.ext
  rfl

/-- Coercion of the Galois action on nonzero 5-torsion. -/
theorem S2501NonzeroTorsionMap_coe (sigma : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    ((S2056NonzeroTorsionMap sigma P : S2056NonzeroTorsion) : S2056Torsion) =
      S2501AffineTorsionGalois sigma P.1 := by
  apply Subtype.ext
  rfl

/-- **The matrix pair action of sigma at S1982Basis is the actual Galois
action of sigma on the twelve affine pairs**, after the basis-compatible
pair identification of S2180/S2186. -/
theorem S2501PairAction_apply (sigma : S1725AbsoluteGalois) (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis
        (pairAct
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) x) =
      S2056PairMap sigma (S2180PairMap S2172AffineBasis x) := by
  let g := S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma
  let v : Fin 2 → ZMod S1982Five.value := x.1
  let w : Fin 2 → ZMod S1982Five.value := g • v
  have hw : S2172AffineBasis (normalize w) =
        S2501AffineTorsionGalois sigma (S2172AffineBasis v) ∨
      S2172AffineBasis (normalize w) =
        -S2501AffineTorsionGalois sigma (S2172AffineBasis v) := by
    rcases normalize_eq_or_neg w with h | h
    · left
      rw [h, S2501MatrixRep_smul_torsion]
    · right
      rw [h]
      calc
        S2172AffineBasis (-w) = -S2172AffineBasis w := map_neg _ _
        _ = -S2501AffineTorsionGalois sigma (S2172AffineBasis v) := by
          rw [S2501MatrixRep_smul_torsion]
  rw [S2501S2180PairMap_eq_pairOf, S2501S2180PairMap_eq_pairOf,
    S2501PairMap_pairOf]
  refine S2501PairOf_eq_of_eq_or_neg ?_
  rcases hw with h | h
  · left
    exact Subtype.ext h.symm
  · right
    apply Subtype.ext
    rw [S2501NonzeroTorsionMap_coe, S2501NonzeroTorsion_neg_coe]
    have h' := congrArg (fun z : S2056Torsion => -z) h
    have h'' : -(S2172AffineBasis (normalize w)) =
        S2501AffineTorsionGalois sigma (S2172AffineBasis x.1) := by
      simpa using h'
    exact h''.symm

/-! ## 3. The root and pair permutations of an absolute Galois element

The actual Galois action on the twelve psi_5 roots over K (S2056) gives a
permutation S2501RootPerm sigma.  Transporting it through the canonical
root-pair bijection S2056RootPairEquiv gives the actual action on the twelve
affine pairs; section 2 identifies that with the matrix pair action. -/

/-- The permutation of the twelve psi_5 roots over K induced by an absolute
Galois element. -/
noncomputable def S2501RootPerm (sigma : S1725AbsoluteGalois) :
    Equiv.Perm S2056Root where
  toFun := S2056RootMap sigma
  invFun := S2056RootMap sigma.symm
  left_inv x := Subtype.ext (sigma.symm_apply_apply x.1)
  right_inv x := Subtype.ext (sigma.apply_symm_apply x.1)

@[simp] theorem S2501RootPerm_apply (sigma : S1725AbsoluteGalois)
    (x : S2056Root) : S2501RootPerm sigma x = S2056RootMap sigma x := rfl

/-- The S2480 root permutation is the same permutation as S2501RootPerm
(both are the Galois action on the twelve psi_5 roots). -/
theorem S2501RootPerm_eq_s2480 (sigma : S1725AbsoluteGalois) :
    S2501RootPerm sigma = S2480RootPerm sigma := by
  apply Equiv.ext
  intro x
  rfl

/-- The canonical pair equivalence from the twelve S2009 pairs to the actual
pairs {+-P} of nonzero 5-torsion points (the bijectivity input is S2186). -/
noncomputable def S2501PairEquiv : S2009Pairs ≃ S2056Pair :=
  Equiv.ofBijective (S2180PairMap S2172AffineBasis)
    (S2186PairMap_bijective S2172AffineBasis)

@[simp] theorem S2501PairEquiv_apply (x : S2009Pairs) :
    S2501PairEquiv x = S2180PairMap S2172AffineBasis x := rfl

/-- The S2218 pair equivalence is the canonical pair equivalence. -/
theorem S2501PairEquiv_eq_s2218 : S2501PairEquiv = S2218PairEquiv := by
  apply Equiv.ext
  intro x
  rfl

/-- **The matrix pair permutation and the Galois root permutation of the same
sigma are conjugate, hence have the same cycle type.** -/
theorem S2501RootPairEquiv_permCongr (sigma : S1725AbsoluteGalois) :
    S2056RootPairEquiv.permCongr (S2501RootPerm sigma) =
      S2501PairEquiv.permCongr
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma)) := by
  ext y
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, S2501RootPerm_apply,
    S2056RootPairEquiv_equivariant, Equiv.apply_symm_apply]
  have h : S2501PairEquiv
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma)
          (S2501PairEquiv.symm y)) =
      S2056PairMap sigma (S2501PairEquiv (S2501PairEquiv.symm y)) := by
    change S2180PairMap S2172AffineBasis
        (pairAct
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma)
          (S2501PairEquiv.symm y)) =
      S2056PairMap sigma (S2180PairMap S2172AffineBasis (S2501PairEquiv.symm y))
    exact S2501PairAction_apply sigma _
  rw [h, Equiv.apply_symm_apply]

/-- The actual Galois permutation of the twelve affine pairs, obtained by
transporting the root permutation through the canonical root-pair bijection. -/
noncomputable def S2501GaloisPairPerm (sigma : S1725AbsoluteGalois) :
    Equiv.Perm S2056Pair :=
  S2056RootPairEquiv.permCongr (S2501RootPerm sigma)

/-- **Matrix-pair/root cycle-type equality.**  The pair cycle type of the
matrix of sigma at S1982Basis is the cycle type of the action of sigma on
the twelve psi_5 roots over K. -/
theorem S2501PairMatrix_cycleType (sigma : S1725AbsoluteGalois) :
    (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma)).cycleType =
      (S2501RootPerm sigma).cycleType := by
  have h := congrArg (fun p : Equiv.Perm S2056Pair => p.cycleType)
    (S2501RootPairEquiv_permCongr sigma)
  rw [S2132cycleType_permCongr] at h
  rw [S2132cycleType_permCongr] at h
  exact h.symm

/-! ## 4. Matrix-range readings via S2218 and the S2229 transported range

S2218 transports the matrix pair action through the canonical pair
equivalence; S2229 encodes the Galois pair action through the GL-transported
actual range, and S2243 proves that the transport is the identity on
ZMod S1987Five.value. -/

/-- The Galois pair permutation is the S2218 matrix pair permutation of the
mod-5 matrix at S1982Basis. -/
theorem S2501GaloisPairPerm_eq_s2218 (sigma : S1725AbsoluteGalois) :
    S2501GaloisPairPerm sigma =
      S2218PairPerm
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) := by
  unfold S2501GaloisPairPerm
  rw [S2501RootPairEquiv_permCongr sigma, S2501PairEquiv_eq_s2218]
  rfl

/-- Cycle-type form of the S2218 identification. -/
theorem S2501GaloisPairPerm_cycleType (sigma : S1725AbsoluteGalois) :
    (S2501GaloisPairPerm sigma).cycleType =
      (S2218PairPerm
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).cycleType :=
  congrArg (fun p : Equiv.Perm S2056Pair => p.cycleType)
    (S2501GaloisPairPerm_eq_s2218 sigma)

/-- The actual Galois pair permutation has the same cycle type as the matrix
pair permutation of sigma at S1982Basis. -/
theorem S2501GaloisPairPerm_cycleType_pairPermHom (sigma : S1725AbsoluteGalois) :
    (S2501GaloisPairPerm sigma).cycleType =
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).cycleType := by
  rw [S2501GaloisPairPerm_cycleType]
  exact S2132cycleType_permCongr S2218PairEquiv
    (pairPermHom (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma))

/-- The S2229 Galois pair action at S1982Basis is the matrix pair action at
S1982Basis (S2243: the transported GL map is the identity). -/
theorem S2501S2229PairPerm_eq (sigma : S1725AbsoluteGalois) :
    S2229GaloisPairPerm S1982Basis sigma =
      S2218PairPerm
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) := by
  unfold S2229GaloisPairPerm
  rw [S2243GLMap_eq_id]
  rfl

/-- The actual Galois pair permutation has the same cycle type as the S2229
transported-range pair action at S1982Basis. -/
theorem S2501GaloisPairPerm_cycleType_s2229 (sigma : S1725AbsoluteGalois) :
    (S2501GaloisPairPerm sigma).cycleType =
      (S2229GaloisPairPerm S1982Basis sigma).cycleType := by
  rw [S2501GaloisPairPerm_cycleType, S2501S2229PairPerm_eq]

/-! ## 5. The matrix-pair/root equivariance and S2480FirstMissing

S2480FirstMissing (in the current S2480) is the existence of an absolute
Galois element whose permutation of the twelve psi_5 roots over K has cycle
type (10, 2).  By S2501PairMatrix_cycleType this is exactly the existence of
an element whose matrix pair permutation at S1982Basis has cycle type
(10, 2). -/

/-- The root-cycle form of S2480FirstMissing: an absolute Galois element
whose permutation of the twelve psi_5 roots over K has cycle type (10, 2). -/
def S2501RootCycleTypeRequired : Prop :=
  ∃ sigma : S1725AbsoluteGalois,
    (S2501RootPerm sigma).cycleType = ({10, 2} : Multiset ℕ)

/-- **S2480FirstMissing is the root-cycle statement.**  The current S2480
defines S2480FirstMissing as S2480RootCycleTypeRequired, whose root permutation
is definitionally the one of S2501RootPerm. -/
theorem S2501FirstMissing_iff_rootCycle :
    S2480FirstMissing ↔ S2501RootCycleTypeRequired := by
  unfold S2480FirstMissing S2480RootCycleTypeRequired
  constructor
  · rintro ⟨sigma, hsigma⟩
    exact ⟨sigma, by rwa [S2501RootPerm_eq_s2480]⟩
  · rintro ⟨sigma, hsigma⟩
    exact ⟨sigma, by rwa [← S2501RootPerm_eq_s2480]⟩

/-- The root-cycle statement gives S2480FirstMissing. -/
theorem S2501FirstMissing_of_rootCycle (h : S2501RootCycleTypeRequired) :
    S2480FirstMissing :=
  S2501FirstMissing_iff_rootCycle.mpr h

/-- S2480FirstMissing gives the root-cycle statement. -/
theorem S2501RootCycleType_of_firstMissing (h : S2480FirstMissing) :
    S2501RootCycleTypeRequired :=
  S2501FirstMissing_iff_rootCycle.mp h

/-- The root-cycle statement gives the matrix-range cycle-type target
S2480Target of S2480: an element of the actual mod-5 image (at S1982Basis)
whose pair permutation has cycle type (10, 2). -/
theorem S2501S2480Target_of_rootCycle (h : S2501RootCycleTypeRequired) :
    S2480Target :=
  S2480Target_of_firstMissing (S2501FirstMissing_of_rootCycle h)

/-- **The matrix-pair / root equivariance, packaged.**  For every absolute
Galois element, its actual affine-pair permutation equals the matrix pair
permutation of its mod-5 matrix at S1982Basis, and the two have the same
cycle type. -/
theorem S2501MatrixPairRootEquivariance (sigma : S1725AbsoluteGalois) :
    S2501GaloisPairPerm sigma =
        S2218PairPerm
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma) ∧
      (S2501GaloisPairPerm sigma).cycleType =
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma)).cycleType :=
  ⟨S2501GaloisPairPerm_eq_s2218 sigma, S2501GaloisPairPerm_cycleType_pairPermHom sigma⟩

/-! ## 6. The S2132 target and the exact missing transport

The S2132 honest target is the existence of an F'-automorphism of the psi_5
splitting field S2057FiveDivisionField whose root permutation has cycle
type (10, 2).  Section 5 identifies the corresponding statement over the
algebraic closure with S2480FirstMissing.  The missing step is exactly the
transport of root cycle types from the splitting field to the closure; it is
stated below as a concrete Prop and is not inhabited here. -/

/-- **The exact missing transport.**  The cycle type of the permutation of the
twelve psi_5 roots induced by an F'-automorphism of the actual splitting
field S2057FiveDivisionField is realised by an F'-automorphism of the
algebraic closure, acting on the twelve roots over the closure. -/
def S2501RootCycleTransferRequired : Prop :=
  ∀ tau : S2132L ≃ₐ[S1720Field] S2132L,
    ∃ sigma : S1725AbsoluteGalois,
      (S2501RootPerm sigma).cycleType =
        Equiv.Perm.cycleType (S2132DivisionRootEquiv tau)

/-- The exact remaining implication: the S2132 honest target implies
S2480FirstMissing. -/
def S2501S2132ToFirstMissingRequired : Prop :=
  S2132FrobInducesPairCycleType → S2480FirstMissing

/-- The remaining implication is the root-to-root transfer form. -/
theorem S2501S2132ToFirstMissingRequired_iff :
    S2501S2132ToFirstMissingRequired ↔
      (S2132FrobInducesRootCycleType → S2501RootCycleTypeRequired) := by
  unfold S2501S2132ToFirstMissingRequired
  constructor
  · intro h hroot
    exact S2501FirstMissing_iff_rootCycle.mp (h (S2132FrobInduces_iff.mp hroot))
  · intro h hpair
    exact S2501FirstMissing_iff_rootCycle.mpr (h (S2132FrobInduces_iff.mpr hpair))

/-- The concrete root-cycle transfer implies the exact remaining
implication. -/
theorem S2501S2132ToFirstMissing_of_rootTransfer
    (h : S2132FrobInducesRootCycleType → S2501RootCycleTypeRequired) :
    S2501S2132ToFirstMissingRequired :=
  S2501S2132ToFirstMissingRequired_iff.mpr h

/-- The concrete transport statement implies the root-to-root transfer. -/
theorem S2501RootTransfer_of_transfer (h : S2501RootCycleTransferRequired) :
    S2132FrobInducesRootCycleType → S2501RootCycleTypeRequired := by
  rintro ⟨tau, htau⟩
  obtain ⟨sigma, hsigma⟩ := h tau
  exact ⟨sigma, by rw [hsigma, htau]; decide⟩

/-- **The S2132 target gives S2480FirstMissing from the exact missing
transport.**  This is the precise reduction of the S2132 target to
S2480FirstMissing; both the finite/equivariance half (proved above) and the
splitting-field-to-closure transport are displayed as separate inputs. -/
theorem S2501S2480FirstMissing_of_S2132_and_transfer
    (h2132 : S2132FrobInducesPairCycleType)
    (h : S2501RootCycleTransferRequired) :
    S2480FirstMissing := by
  have hf : S2132FrobInducesPairCycleType → S2480FirstMissing :=
    S2501S2132ToFirstMissing_of_rootTransfer (S2501RootTransfer_of_transfer h)
  exact hf h2132

/-! ## 7. Axiom footprint -/

#print axioms S2501AffineTorsionGalois
#print axioms S2501AffineTorsionEquiv_galois
#print axioms S2501MatrixRep_affine
#print axioms S2501MatrixRep_smul_torsion
#print axioms S2501PairAction_apply
#print axioms S2501RootPairEquiv_permCongr
#print axioms S2501PairMatrix_cycleType
#print axioms S2501GaloisPairPerm_eq_s2218
#print axioms S2501GaloisPairPerm_cycleType
#print axioms S2501S2229PairPerm_eq
#print axioms S2501FirstMissing_iff_rootCycle
#print axioms S2501S2132ToFirstMissingRequired_iff
#print axioms S2501S2480FirstMissing_of_S2132_and_transfer

end LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual

end
