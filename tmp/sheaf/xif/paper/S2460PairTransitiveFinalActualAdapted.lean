/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S2375RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2364D5GroupRouteActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

/-!
# S2460: the final attempt at the actual mod-5 range pair-transitivity target

The target of this file is the actual proposition

  S2203RangePairTransitiveRequired S1982Basis
  = PairTransitive (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

of the paper's D5 large-image input, i.e. the twelve-pair transitivity of the
actual mod-5 Galois range of the actual curve E' = S1667Punctured.baseChange F'.

## Status: not closed

The target is **not proved** and no inhabitant of it is produced here.  What is
proved:

1. The target is definitionally the S2203/S2375/S2378/S2218/S2229 formulations;
   the equivalences are Iff.rfl or the previously kernel-checked identifications
   (S2440, S2375, S2378, S2218, S2229, S2243).

2. The sufficient inputs of S2440 are re-exported for the final target: the
   SL_2 containment S1725ImageTail S1987Five S1982Basis, the frozen
   S1987D5LargeImageFive, the whole-range statement, and the twelve-cycle input.

3. **New here.**  The matrix twelve-cycle input is identified with the arithmetic
   twelve-cycle statement on the actual Galois action on the twelve roots of the
   actual odd 5-division polynomial prePsi_5 over F'.  Concretely, for every
   sigma in the absolute Galois group of F', the cycle type of the permutation
   of the twelve pairs induced by the matrix rho_5(sigma) equals the cycle type
   of the permutation of the twelve roots induced by sigma
   (S2460pairPerm_cycleType_eq_rootPerm).  Consequently

     (exists sigma, root cycle type = {12})
       <-> S2440TwelveCycleInputRequired
       -> S2460Target.

   This is the precise matrix-free arithmetic form of the only sufficient input
   for which the paper supplies a numerical certificate.

## Exact first missing

S2460RootTwelveCycleRequired below: there exists an F'-automorphism sigma of
the algebraic closure of F' whose permutation of the twelve roots of the actual
prePsi_5 is a 12-cycle.  Nothing in the tree proves it.  The actual gaps between
the tree and this statement are, in the order in which they occur:

* **Dedekind--Frobenius cycle comparison.**  S2217Missing
  (DedekindFrobeniusOrbitSizeTheorem, S2217) is not proved: Mathlib supplies
  the arithmetic Frobenius arithFrobAt but no comparison of its cycle type on
  roots with the degrees of the irreducible factors of the reduction.

* **The finite-field certificate.**  The S1987 report's certificate
  '2^36 * psi_5 is irreducible modulo 13' is nowhere formalized.  The tree only
  formalizes the *mod 29* certificate (irreducibility of a degree-ten factor,
  S2122/S2126/S2094, and the degree-two factor algebraically).  The exact
  integer model 2^36 * prePsi_5 exists in S2132 (S2132Psi5Z); the statement of
  the mod-13 certificate is recorded below as S2460Mod13Certificate.

* **The Q-level to F'-level transport.**  The mod-13 certificate is a statement
  about the Q-curve.  At a prime above 13 in F' the *relative* Frobenius is a
  power of the Q-Frobenius, and the residual 3-division cubic is irreducible
  modulo 13, so the residue degree of F' at 13 is at least three; the relative
  Frobenius at 13 is therefore not a 12-cycle even though the Q-Frobenius is.
  A 12-cycle in Gal(Fbar/F') must instead come from the restriction-surjectivity
  (linear disjointness) of F' and the 5-division field, which is not formalized
  (S2167 records the same phenomenon at 29: 29 is inert in Q(sqrt(-3))).

No sorry, axiom, True/PUnit gate, native_decide or renamed hypothesis is used
below; every declaration is an actual Lean object and the missing statements are
plain Props with no inhabitants.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2460PairTransitiveFinalActualAdapted

open Matrix
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

/-! ## 1. The target and its equivalent formulations -/

/-- The actual target: pair transitivity of the actual mod-5 range at the
selected basis S1982Basis. -/
def S2460Target : Prop := S2203RangePairTransitiveRequired S1982Basis

/-- The target in unfolded form. -/
theorem S2460Target_unfolded :
    S2460Target ↔
      PairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The target is exactly the S2375 exact first missing. -/
theorem S2460Target_iff_S2375 : S2460Target ↔ S2375ExactFirstMissing := Iff.rfl

/-- The target is exactly the S2378 exact first missing. -/
theorem S2460Target_iff_S2378 : S2460Target ↔ S2378ExactFirstMissing := Iff.rfl

/-- The target is the actual affine-pair transitivity of S2218/S2221. -/
theorem S2460Target_iff_affine :
    S2460Target ↔
      S2218AffinePairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  S2218AffinePairTransitive_iff _

/-- The target is the actual Galois transitivity on the twelve affine pairs. -/
theorem S2460Target_iff_galois : S2460Target ↔ S2229GaloisPairTransitive S1982Basis :=
  (S2375GaloisPairTransitive_iff_range).symm

/-! ## 2. Sufficient inputs (all previously kernel checked) -/

/-- A 12-cycle in the actual range gives the target (S2440). -/
theorem S2460Target_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2460Target :=
  S2440RangePairTransitive_of_twelveCycle h

/-- The SL_2 containment at the selected basis gives the target (S2440). -/
theorem S2460Target_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2460Target :=
  S2440RangePairTransitive_of_imageTail h

/-- The frozen S1987 large-image target gives the target (S2440). -/
theorem S2460Target_of_largeImage (h : S1987D5LargeImageFive) : S2460Target :=
  S2440RangePairTransitive_of_largeImage h

/-- The whole-range statement gives the target (S2378). -/
theorem S2460Target_of_rangeTop (h : S2378RangeTopRequired) : S2460Target :=
  S2378PairTransitive_of_rangeTop h

/-! ## 3. The twelve-cycle input in matrix form and in root form -/

/-- The permutation of the twelve roots of the actual prePsi_5 induced by an
automorphism sigma of the algebraic closure of F'. -/
noncomputable def S2460RootPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Root where
  toFun := S2056RootMap σ
  invFun := S2056RootMap σ.symm
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)

@[simp] theorem S2460RootPerm_apply (σ : S1725AbsoluteGalois) (x : S2056Root) :
    S2460RootPerm σ x = S2056RootMap σ x := rfl

/-- The actual Galois action on the affine 5-torsion, as a homomorphism. -/
noncomputable def S2460PointMapTorsion (σ : S1725AbsoluteGalois) :
    S2056Torsion →+ S2056Torsion where
  toFun P := ⟨S2056PointMap σ (P : S2056W.Point), by
    have h := S2056PointMap_torsion σ P.2
    simpa using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

@[simp] theorem S2460PointMapTorsion_coe (σ : S1725AbsoluteGalois)
    (P : S2056Torsion) :
    (S2460PointMapTorsion σ P : S2056W.Point) =
      S2056PointMap σ (P : S2056W.Point) := rfl

/-- The affine/projective comparison intertwines the actual Galois action. -/
theorem S2460AffineTorsionEquiv_galois (σ : S1725AbsoluteGalois)
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
theorem S2460MatrixRep_affine (σ : S1725AbsoluteGalois)
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
          S2460AffineTorsionEquiv_galois σ _
    _ = S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := rfl

/-- The same statement with the module action instead of the linear-map
action. -/
theorem S2460MatrixRep_smul_point (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    (S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) :
          S2056W.Point) =
      S2056PointMap σ (S2172AffineBasis v : S2056W.Point) := by
  rw [← S2460MatrixRep_affine σ v]
  congr 1

/-- The module-action form in the actual affine torsion group. -/
theorem S2460MatrixRep_smul_torsion (σ : S1725AbsoluteGalois)
    (v : Fin 2 → ZMod S1982Five.value) :
    S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) =
      S2460PointMapTorsion σ (S2172AffineBasis v) := by
  apply Subtype.ext
  exact S2460MatrixRep_smul_point σ v

/-- Negation on nonzero 5-torsion is involutive. -/
theorem S2460_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The standard pair of a nonzero 5-torsion point. -/
noncomputable def S2460PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
  ⟨{P, -P}, Finset.card_pair (S2056_ne_neg P), by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ ⊢
    rcases hQ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (S2460_neg_neg P)⟩

/-- Pair sets of the same nonzero point are equal. -/
theorem S2460PairOf_eq_of_eq_or_neg {P Q : S2056NonzeroTorsion}
    (h : Q = P ∨ Q = -P) : S2460PairOf P = S2460PairOf Q := by
  apply Subtype.ext
  rcases h with rfl | rfl
  · rfl
  · show ({P, -P} : Finset S2056NonzeroTorsion) = {-P, -(-P)}
    rw [S2460_neg_neg P]
    exact Finset.pair_comm P (-P)

/-- The Galois action on a pair is the pair of the Galois action. -/
theorem S2460PairMap_pairOf (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    S2056PairMap σ (S2460PairOf P) = S2460PairOf (S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  ext Q
  simp only [S2460PairOf, S2056PairMap, Finset.mem_insert, Finset.mem_singleton,
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
theorem S2460E_ne_zero (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    (S2172AffineBasis v : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : S2172AffineBasis v = 0 := Subtype.ext h
  exact hv (S2172AffineBasis.injective (by rw [h0, map_zero]))

/-- The S2180 pair map is the standard pair of the affine basis image. -/
theorem S2460S2180PairMap_eq_pairOf (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis x =
      S2460PairOf ⟨S2172AffineBasis x.1,
        S2460E_ne_zero x.1 (isRep_ne_zero x.1 x.2)⟩ := by
  apply Subtype.ext
  apply Finset.ext
  intro Q
  simp [S2180PairMap, S2460PairOf]

/-- Coercion of the custom negation on nonzero torsion. -/
theorem S2460NonzeroTorsion_neg_coe (P : S2056NonzeroTorsion) :
    ((-P : S2056NonzeroTorsion) : S2056Torsion) = -P.1 := by
  apply Subtype.ext
  rfl

/-- Coercion of the Galois action on nonzero torsion. -/
theorem S2460NonzeroTorsionMap_coe (σ : S1725AbsoluteGalois)
    (P : S2056NonzeroTorsion) :
    ((S2056NonzeroTorsionMap σ P : S2056NonzeroTorsion) : S2056Torsion) =
      S2460PointMapTorsion σ P.1 := by
  apply Subtype.ext
  rfl

/-- The actual matrix action agrees with the actual Galois action on pairs. -/
theorem S2460PairAction_apply (σ : S1725AbsoluteGalois) (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis
        (pairAct (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) x) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis x) := by
  let g := S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ
  let v : Fin 2 → ZMod S1982Five.value := x.1
  let w : Fin 2 → ZMod S1982Five.value := g • v
  have hw : S2172AffineBasis (normalize w) =
        S2460PointMapTorsion σ (S2172AffineBasis v) ∨
      S2172AffineBasis (normalize w) =
        -S2460PointMapTorsion σ (S2172AffineBasis v) := by
    rcases normalize_eq_or_neg w with h | h
    · left
      rw [h, S2460MatrixRep_smul_torsion]
    · right
      rw [h]
      calc
        S2172AffineBasis (-w) = -S2172AffineBasis w := map_neg _ _
        _ = -S2460PointMapTorsion σ (S2172AffineBasis v) := by
          rw [S2460MatrixRep_smul_torsion]
  rw [S2460S2180PairMap_eq_pairOf, S2460S2180PairMap_eq_pairOf,
    S2460PairMap_pairOf]
  refine S2460PairOf_eq_of_eq_or_neg ?_
  rcases hw with h | h
  · left
    exact Subtype.ext h.symm
  · right
    apply Subtype.ext
    rw [S2460NonzeroTorsionMap_coe, S2460NonzeroTorsion_neg_coe]
    have h' := congrArg (fun z : S2056Torsion => -z) h
    have h'' : -(S2172AffineBasis (normalize w)) =
        S2460PointMapTorsion σ (S2172AffineBasis x.1) := by
      simpa using h'
    exact h''.symm

/-- The canonical pair equivalence from the twelve S2009 pairs to the actual
pairs {+-P} of nonzero 5-torsion points. -/
noncomputable def S2460PairEquiv : S2009Pairs ≃ S2056Pair :=
  Equiv.ofBijective (S2180PairMap S2172AffineBasis)
    (S2186PairMap_bijective S2172AffineBasis)

@[simp] theorem S2460PairEquiv_apply (x : S2009Pairs) :
    S2460PairEquiv x = S2180PairMap S2172AffineBasis x := rfl

/-- **The matrix pair permutation and the Galois root permutation of the same
sigma are conjugate, hence have the same cycle type.** -/
theorem S2460RootPairEquiv_permCongr (σ : S1725AbsoluteGalois) :
    S2056RootPairEquiv.permCongr (S2460RootPerm σ) =
      S2460PairEquiv.permCongr
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)) := by
  ext y
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, S2460RootPerm_apply,
    S2056RootPairEquiv_equivariant, Equiv.apply_symm_apply]
  have h : S2460PairEquiv
        (pairPermHom
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)
          (S2460PairEquiv.symm y)) =
      S2056PairMap σ (S2460PairEquiv (S2460PairEquiv.symm y)) := by
    change S2180PairMap S2172AffineBasis
        (pairAct
          (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)
          (S2460PairEquiv.symm y)) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis (S2460PairEquiv.symm y))
    exact S2460PairAction_apply σ _
  rw [h, Equiv.apply_symm_apply]

/-- **The cycle type of the matrix action of sigma on the twelve pairs is the
cycle type of the action of sigma on the twelve roots of prePsi_5.** -/
theorem S2460pairPerm_cycleType_eq_rootPerm (σ : S1725AbsoluteGalois) :
    (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
      (S2460RootPerm σ).cycleType := by
  rw [← S2132cycleType_permCongr (e := S2460PairEquiv)
    (σ := pairPermHom
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ))]
  rw [← S2460RootPairEquiv_permCongr σ]
  rw [S2132cycleType_permCongr]

/-- The arithmetic form of the twelve-cycle input: an F'-automorphism of the
algebraic closure whose root permutation is a 12-cycle. -/
def S2460RootTwelveCycleRequired : Prop :=
  ∃ σ : S1725AbsoluteGalois, (S2460RootPerm σ).cycleType = ({12} : Multiset ℕ)

/-- **The matrix twelve-cycle input is exactly the arithmetic root twelve-cycle
statement.** -/
theorem S2460TwelveCycleInput_iff_root :
    S2440TwelveCycleInputRequired ↔ S2460RootTwelveCycleRequired := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, by rw [← S2460pairPerm_cycleType_eq_rootPerm σ]; exact hc⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, ?_⟩
    rw [S2460pairPerm_cycleType_eq_rootPerm σ]
    exact hσ

/-- The root form of the input implies the actual target. -/
theorem S2460Target_of_rootTwelveCycle
    (h : S2460RootTwelveCycleRequired) : S2460Target :=
  S2460Target_of_twelveCycle (S2460TwelveCycleInput_iff_root.mpr h)

/-! ## 4. Exact first missing and the finite-field certificate -/

/-- The exact first missing statement of this file: the arithmetic twelve-cycle
on the actual 5-division roots.  No inhabitant is produced. -/
def S2460ExactFirstMissing : Prop := S2460RootTwelveCycleRequired

/-- The target follows from the exact first missing.  This is a conditional
theorem: no inhabitant of the exact first missing is provided. -/
theorem S2460Target_of_exactFirstMissing
    (h : S2460ExactFirstMissing) : S2460Target :=
  S2460Target_of_rootTwelveCycle h

/-- The finite-field certificate actually needed by the mod-13 route: the S2132
integer model 2^36 * prePsi_5 is irreducible modulo 13.  This is a plain Prop;
no proof is available in the tree. -/
def S2460Mod13Certificate : Prop :=
  Irreducible
    (LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
      (Int.castRingHom (ZMod 13)))

/-- Axiom footprint. -/
#print axioms S2460Target_unfolded
#print axioms S2460Target_iff_affine
#print axioms S2460Target_iff_galois
#print axioms S2460Target_of_twelveCycle
#print axioms S2460Target_of_imageTail
#print axioms S2460Target_of_largeImage
#print axioms S2460Target_of_rangeTop
#print axioms S2460RootPerm
#print axioms S2460PairAction_apply
#print axioms S2460PairEquiv
#print axioms S2460RootPairEquiv_permCongr
#print axioms S2460pairPerm_cycleType_eq_rootPerm
#print axioms S2460TwelveCycleInput_iff_root
#print axioms S2460Target_of_rootTwelveCycle
#print axioms S2460Target_of_exactFirstMissing

end LeanFormal.IUT.XiFPaper.S2460PairTransitiveFinalActualAdapted

end
