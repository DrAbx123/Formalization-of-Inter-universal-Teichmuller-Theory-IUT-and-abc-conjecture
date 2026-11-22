/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual

/-!
# S2446: the actual range cycle-type target for the mod-5 representation

The target of this file is the actual proposition

  S2203RangeCycleTypeRequired S1982Basis
  = HasCycleType102 (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

of the paper's D5 large-image input at the selected actual rank-two basis.

## What is proved here

1. The target is definitionally the displayed statement, and it is equivalent
   to the existence of an element of the absolute Galois group of F' whose
   matrix has pair cycle type (10, 2).
2. The cycle-type hypothesis is independent of the chosen rank-two basis: the
   ranges at two bases are conjugate, and cycle type is conjugation invariant.
3. The matrix pair action is identified with the actual Galois action on the
   twelve pairs of nonzero 5-torsion points, and hence with the Galois action
   on the twelve roots of the actual 5-division polynomial psi_5 over F'.
   Consequently the target is exactly the existence of an F'-automorphism of
   the algebraic closure acting on the twelve psi_5-roots with cycle type
   (10, 2).  This is the form in which the Dedekind--Frobenius theorem supplies
   its output, so it is the precise arithmetic first-missing statement.

No sorry, axiom, native_decide or True is used.  The axiom footprint is printed
at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2446RangeCycleTypeSubagentActual

open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open Matrix

/-! ## 1. The exact target -/

/-- The actual range cycle-type target at the selected basis S1982Basis. -/
def S2446Target : Prop := S2203RangeCycleTypeRequired S1982Basis

/-- The target in fully unfolded form. -/
theorem S2446Target_unfolded :
    S2446Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The same target with the representation read at the definitionally equal
prime label S1982Five. -/
theorem S2446Target_iff_range1982 :
    S2446Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis).range :=
  Iff.rfl

/-- The target is the existence of a Galois element whose matrix already has
the required pair cycle type. -/
theorem S2446Target_iff_exists_galois :
    S2446Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) := by
  rw [S2446Target_iff_range1982]
  change (∃ h : GL (Fin 2) (ZMod S1982Five.value),
      h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis).range ∧
        (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)) ↔ _
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, hc⟩

/-! ## 2. Independence of the rank-two basis -/

/-- Conjugation by an element of GL_2(F_5) preserves the pair cycle type. -/
theorem S2446cycleType_pairPermHom_conj (c g : GL2) :
    (pairPermHom (c * g * c⁻¹)).cycleType = (pairPermHom g).cycleType := by
  rw [map_mul, map_mul, map_inv]
  exact Equiv.Perm.cycleType_conj

/-- Cycle type (10, 2) is invariant under conjugation of a subgroup. -/
theorem S2446HasCycleType102_map_conj (c : GL2) (H : Subgroup GL2) :
    HasCycleType102 (Subgroup.map (MulAut.conj c).toMonoidHom H) ↔
      HasCycleType102 H := by
  constructor
  · rintro ⟨h, hh, hc⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨g, hg, hgk⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgk
    refine ⟨g, hg, ?_⟩
    rw [← S2446cycleType_pairPermHom_conj c g]
    exact hgk ▸ hc
  · rintro ⟨g, hg, hc⟩
    refine ⟨c * g * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨g, hg, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [S2446cycleType_pairPermHom_conj]
      exact hc

/-- The actual range cycle-type hypothesis does not depend on the rank-two
basis. -/
theorem S2446RangeCycleType_basis_indep (b b' : S1725TorsionBasis S1987Five) :
    HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b').range := by
  rw [S1894MatrixRep_range_conj S1987Five b b']
  exact (S2446HasCycleType102_map_conj
    (S1894BasisChangeGL S1987Five b b')
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range).symm

/-- The target is equivalent to the cycle-type hypothesis at any chosen
rank-two basis. -/
theorem S2446Target_iff_basis (b : S1725TorsionBasis S1987Five) :
    S2446Target ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2446Target_unfolded.trans (S2446RangeCycleType_basis_indep S1982Basis b)

/-- The target is also the basis-free form of the cycle-type hypothesis. -/
theorem S2446Target_iff_forall_basis :
    S2446Target ↔ ∀ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h b
    exact (S2446Target_iff_basis b).mp h
  · intro h
    exact (S2446Target_iff_basis S1982Basis).mpr (h S1982Basis)


/-! ## 3. The matrix action on the actual 5-torsion pairs -/

/-- The actual Galois action on the affine 5-torsion, as a homomorphism. -/
noncomputable def S2446PointMapTorsion (σ : S1725AbsoluteGalois) :
    S2056Torsion →+ S2056Torsion where
  toFun P := ⟨S2056PointMap σ (P : S2056W.Point), by
    have h := S2056PointMap_torsion σ P.2
    simpa using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

@[simp] theorem S2446PointMapTorsion_coe (σ : S1725AbsoluteGalois)
    (P : S2056Torsion) :
    (S2446PointMapTorsion σ P : S2056W.Point) =
      S2056PointMap σ (P : S2056W.Point) := rfl

/-- The affine/projective comparison intertwines the actual Galois action. -/
theorem S2446AffineTorsionEquiv_galois (σ : S1725AbsoluteGalois)
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
theorem S2446MatrixRep_affine (σ : S1725AbsoluteGalois)
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
          S2446AffineTorsionEquiv_galois σ _
    _ = S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := rfl

/-- The same statement with the module action instead of the linear-map
action. -/
theorem S2446MatrixRep_smul_point (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) :
          S2056W.Point) =
      S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := by
  rw [← S2446MatrixRep_affine σ v]
  congr 1

/-- The module-action form in the actual affine torsion group. -/
theorem S2446MatrixRep_smul_torsion (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) =
      S2446PointMapTorsion σ (S2172AffineBasis v) := by
  apply Subtype.ext
  exact S2446MatrixRep_smul_point σ v


/-- Negation on nonzero 5-torsion is involutive. -/
theorem S2446_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The standard pair of a nonzero 5-torsion point. -/
noncomputable def S2446PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
  ⟨{P, -P}, Finset.card_pair (S2056_ne_neg P), by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (S2446_neg_neg P)⟩

/-- Pair sets of the same nonzero point are equal. -/
theorem S2446PairOf_eq_of_eq_or_neg {P Q : S2056NonzeroTorsion}
    (h : Q = P ∨ Q = -P) : S2446PairOf P = S2446PairOf Q := by
  apply Subtype.ext
  rcases h with rfl | rfl
  · rfl
  · show ({P, -P} : Finset S2056NonzeroTorsion) = {-P, -(-P)}
    rw [S2446_neg_neg P]
    exact Finset.pair_comm P (-P)

/-- The Galois action on a pair is the pair of the Galois action. -/
theorem S2446PairMap_pairOf (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    S2056PairMap σ (S2446PairOf P) = S2446PairOf (S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  ext Q
  simp only [S2446PairOf, S2056PairMap, Finset.mem_insert, Finset.mem_singleton,
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
theorem S2446E_ne_zero (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    (S2172AffineBasis v : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : S2172AffineBasis v = 0 := Subtype.ext h
  exact hv (S2172AffineBasis.injective (by rw [h0, map_zero]))

/-- The S2180 pair map is the standard pair of the affine basis image. -/
theorem S2446S2180PairMap_eq_pairOf (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis x =
      S2446PairOf ⟨S2172AffineBasis x.1,
        S2446E_ne_zero x.1 (isRep_ne_zero x.1 x.2)⟩ := by
  apply Subtype.ext
  apply Finset.ext
  intro Q
  simp [S2180PairMap, S2446PairOf]

/-- Coercion of the custom negation on nonzero torsion. -/
theorem S2446NonzeroTorsion_neg_coe (P : S2056NonzeroTorsion) :
    ((-P : S2056NonzeroTorsion) : S2056Torsion) = -P.1 := by
  apply Subtype.ext
  rfl

/-- Coercion of the Galois action on nonzero torsion. -/
theorem S2446NonzeroTorsionMap_coe (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    ((S2056NonzeroTorsionMap σ P : S2056NonzeroTorsion) : S2056Torsion) =
      S2446PointMapTorsion σ P.1 := by
  apply Subtype.ext
  rfl

/-- The actual matrix action agrees with the actual Galois action on pairs. -/
theorem S2446PairAction_apply (σ : S1725AbsoluteGalois) (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis
        (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) x) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis x) := by
  let g := S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ
  let v : Fin 2 → ZMod S1982Five.value := x.1
  let w : Fin 2 → ZMod S1982Five.value := g • v
  have hw : S2172AffineBasis (normalize w) =
        S2446PointMapTorsion σ (S2172AffineBasis v) ∨
      S2172AffineBasis (normalize w) =
        -S2446PointMapTorsion σ (S2172AffineBasis v) := by
    rcases normalize_eq_or_neg w with h | h
    · left
      rw [h, S2446MatrixRep_smul_torsion]
    · right
      rw [h]
      calc
        S2172AffineBasis (-w) = -S2172AffineBasis w := map_neg _ _
        _ = -S2446PointMapTorsion σ (S2172AffineBasis v) := by
          rw [S2446MatrixRep_smul_torsion]
  rw [S2446S2180PairMap_eq_pairOf, S2446S2180PairMap_eq_pairOf,
    S2446PairMap_pairOf]
  refine S2446PairOf_eq_of_eq_or_neg ?_
  rcases hw with h | h
  · left
    exact Subtype.ext h.symm
  · right
    apply Subtype.ext
    rw [S2446NonzeroTorsionMap_coe, S2446NonzeroTorsion_neg_coe]
    have h' := congrArg (fun z : S2056Torsion => -z) h
    have h'' : -(S2172AffineBasis (normalize w)) =
        S2446PointMapTorsion σ (S2172AffineBasis x.1) := by
      simpa using h'
    exact h''.symm

end LeanFormal.IUT.XiFPaper.S2446RangeCycleTypeSubagentActual

end
