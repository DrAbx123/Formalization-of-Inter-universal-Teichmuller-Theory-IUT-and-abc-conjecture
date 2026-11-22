/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2511AffineNaturalityActual
import tmp.sheaf.xif.paper.S2218RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

/-!
# S2512: pointwise compatibility of the actual pair action with the mod-5 matrix action

## Target

For every absolute Galois automorphism sigma of F' = S1720Field and every
actual pair S : S2056Pair of nonzero 5-torsion points of E' = S1720Curve,

  S2056PairMap sigma S
      = S2218PairPerm (S2229GLMap (rho_{5,S1982Basis} sigma)) S,

where

* S2056PairMap sigma is the action of sigma on the twelve pairs {+-P},
  defined through the affine point map S2056PointMap of S2056;
* rho_{5,S1982Basis} sigma is
  S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis sigma;
* S2229GLMap is the ZMod transport of the matrix group (S2229);
* S2218PairPerm is the transported GL_2(F_5) action on S2056Pair along the
  basis-compatible pair equivalence of S2186.

## Route

The proof uses exactly the objects named in the task:

1. S2172AffineBasis is the actual affine lift of the rank-two basis
   S1982Basis (S2172), and S2180PairMap S2172AffineBasis is the
   basis-compatible pair map (S2180).
2. S2186BasisCompatiblePairEquiv packages that map as an equivalence, and
   S2218PairEquiv is precisely its pair equivalence (S2186/S2218).
3. S2511MatrixRep_affine (S2511) identifies the affine point attached to the
   matrix-transported torsion point with the S2056PointMap-image of the affine
   point attached to the original torsion point.  This is the S2511
   naturality input, and its proof uses S1894MatrixRep_acts.
4. Combining 1-3 gives the pair-level naturality S2512PairNaturality: the
   basis-compatible pair map intertwines the matrix pair action with the
   actual Galois pair action.
5. Unfolding S2218PairPerm as S2218PairEquiv.permCongr (pairPermHom _) and
   applying S2218PairPerm_apply turns 4 into the target pointwise identity.

The naturality input is stated below as S2512AffineBasisNaturality and is
proved from S2511MatrixRep_affine (S2512AffineBasisNaturality_actual).
Consequently the main theorems below are unconditional; the
_of_naturality versions are provided for a consumer that wants to supply the
S2511 statement as an explicit hypothesis.

No unfinished placeholders or extra axioms are used.  The file has not been
compiled here; the central build must check it.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2512PairCompatibilityActualAdapted

open Matrix
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2511AffineNaturalityActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-! ## 1. The S2511 naturality inputs -/

/-- The S2511 naturality in affine-basis form.  The actual affine lift
S2172AffineBasis of S1982Basis intertwines the mod-5 matrix action with the
actual Galois action on affine 5-torsion points. -/
def S2512AffineBasisNaturality : Prop :=
  ∀ (σ : S1725AbsoluteGalois) (v : Fin 2 → ZMod S1982Five.value),
    ((S2172AffineBasis
        ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • v) :
          S2056Torsion) : S2056W.Point) =
      S2056PointMap σ ((S2172AffineBasis v : S2056Torsion) : S2056W.Point)

/-- The S2511 naturality transported to pairs.  The basis-compatible pair map
S2180PairMap S2172AffineBasis intertwines the matrix pair action with the
actual Galois pair action S2056PairMap. -/
def S2512PairNaturality : Prop :=
  ∀ (σ : S1725AbsoluteGalois) (x : S2009Pairs),
    S2180PairMap S2172AffineBasis
        (pairAct
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) x) =
      S2056PairMap σ (S2180PairMap S2172AffineBasis x)

/-! ## 2. The matrix action at the affine basis -/

/-- The module action of a general linear matrix is its linear equivalence. -/
theorem S2512Basis_toLin (g : GL2) (v : Fin 2 → ZMod S1982Five.value) :
    (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv v = g • v := by
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, ← Matrix.smul_eq_mulVec]
  rfl

/-- The affine 5-torsion point S2172AffineBasis v is the projective/affine
comparison applied to the projective torsion point S1982Basis v. -/
theorem S2512AffineBasis_coe (v : Fin 2 → ZMod S1982Five.value) :
    ((S2172AffineBasis v : S2056Torsion) : S2056W.Point) =
      S1906ProjAffineEquiv
        ((S1982Basis v : S1720Curve.LTorsion S1982Five) :
          WeierstrassCurve.Projective.Point S2056W) :=
  rfl

/-- The affine-basis naturality is actual.  This is exactly
S2511MatrixRep_affine at the actual prime 5 and the actual basis S1982Basis,
transported through S2172AffineBasis. -/
theorem S2512AffineBasisNaturality_actual : S2512AffineBasisNaturality := by
  intro σ v
  rw [S2512AffineBasis_coe ((S1720Curve.galoisLTorsionMatrixRepresentation
        S1982Five S1982Basis σ) • v), S2512AffineBasis_coe v, ← S2512Basis_toLin]
  exact S2511MatrixRep_affine S1982Five S1982Basis σ v

/-! ## 3. The pair-level naturality -/

/-- The pair {P, -P} attached to a nonzero 5-torsion point. -/
noncomputable def S2512PairOf (P : S2056NonzeroTorsion) : S2056Pair :=
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
theorem S2512_neg_neg (P : S2056NonzeroTorsion) : -(-P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact neg_neg _

/-- The pair attached to a point equals the pair attached to its negative. -/
theorem S2512PairOf_neg (P : S2056NonzeroTorsion) :
    S2512PairOf (-P) = S2512PairOf P := by
  apply Subtype.ext
  show (Finset.insert (-P) (Finset.singleton (-(-P)))) =
    Finset.insert P (Finset.singleton (-P))
  rw [S2512_neg_neg]
  exact Finset.pair_comm (-P) P

/-- The pair of a point only depends on the pair, not on the chosen sign. -/
theorem S2512PairOf_congr {P Q : S2056NonzeroTorsion} (h : Q = P ∨ Q = -P) :
    S2512PairOf Q = S2512PairOf P := by
  rcases h with rfl | rfl
  · rfl
  · exact S2512PairOf_neg P

/-- A nonzero coordinate vector stays nonzero in the affine 5-torsion. -/
theorem S2512E_ne_zero (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (v : Fin 2 → ZMod S1982Five.value) (hv : v ≠ 0) :
    ((e v : S2056Torsion) : S2056W.Point) ≠ 0 := by
  intro h
  have h0 : e v = 0 := Subtype.ext h
  exact hv (e.injective (by rw [h0, map_zero]))

/-- The basis-compatible pair map is the pair-of map. -/
theorem S2512S2180PairMap_eq
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) (x : S2009Pairs) :
    S2180PairMap e x = S2512PairOf ⟨e x.1, S2512E_ne_zero e x.1 (isRep_ne_zero x.1 x.2)⟩ :=
  rfl

/-- The Galois action on the actual pairs sends the pair of P to the pair of
sigma P. -/
theorem S2512PairMap_pairOf (σ : S1725AbsoluteGalois) (P : S2056NonzeroTorsion) :
    S2056PairMap σ (S2512PairOf P) =
      S2512PairOf (S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  change (Finset.image (S2056NonzeroTorsionMap σ) (Finset.insert P (Finset.singleton (-P))))
    = Finset.insert (S2056NonzeroTorsionMap σ P)
        (Finset.singleton (-(S2056NonzeroTorsionMap σ P)))
  rw [Finset.image_insert, Finset.image_singleton, S2056NonzeroTorsionMap_neg]

/-- The affine-basis naturality implies the pair naturality.  This is the
S2172/S2180/S2186 step: a pair {e v, -e v} is sent to {sigma (e v),
-sigma (e v)}, while the matrix acts on v and the normalisation only changes
the chosen sign. -/
theorem S2512PairNaturality_of_affineBasis
    (h : S2512AffineBasisNaturality) : S2512PairNaturality := by
  intro σ x
  have hv : x.1 ≠ 0 := isRep_ne_zero x.1 x.2
  have hAx : ((S2172AffineBasis x.1 : S2056Torsion) : S2056W.Point) ≠ 0 :=
    S2512E_ne_zero S2172AffineBasis x.1 hv
  have hgv :
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) •
          x.1 ≠ 0 := by
    rw [← S2512Basis_toLin]
    intro h0
    exact hv ((Matrix.GeneralLinearGroup.toLin
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)).toLinearEquiv.injective
        (by rw [h0, map_zero]))
  have hAgx : ((S2172AffineBasis
      ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) :
        S2056Torsion) : S2056W.Point) ≠ 0 :=
    S2512E_ne_zero S2172AffineBasis _ hgv
  have hpt : S2056PointMap σ ((S2172AffineBasis x.1 : S2056Torsion) : S2056W.Point)
      = ((S2172AffineBasis
          ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1) :
            S2056Torsion) : S2056W.Point) :=
    (h σ x.1).symm
  have hMap : S2056NonzeroTorsionMap σ
        (⟨S2172AffineBasis x.1, hAx⟩ : S2056NonzeroTorsion)
      = ⟨S2172AffineBasis
          ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1),
          hAgx⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpt
  rw [S2512S2180PairMap_eq, S2512PairMap_pairOf, S2512S2180PairMap_eq, hMap]
  refine S2512PairOf_congr ?_
  rcases normalize_eq_or_neg
      ((S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) • x.1)
      with h' | h'
  · left
    apply Subtype.ext
    apply Subtype.ext
    rw [h']
  · right
    apply Subtype.ext
    apply Subtype.ext
    rw [h', map_neg]
    rfl

/-- The pair naturality is actual, obtained from the affine-basis naturality
above. -/
theorem S2512PairNaturality_actual : S2512PairNaturality :=
  S2512PairNaturality_of_affineBasis S2512AffineBasisNaturality_actual

/-! ## 4. The pointwise pair compatibility -/

/-- Main theorem, pointwise form.  For every absolute Galois automorphism
sigma and every actual pair S, the actual Galois action on S is the
S2218PairPerm action of the transported mod-5 matrix of sigma. -/
theorem S2512PairCompatibility_pointwise_of_naturality
    (h : S2512PairNaturality)
    (σ : S1725AbsoluteGalois) (S : S2056Pair) :
    S2056PairMap σ S =
      S2218PairPerm
        (S2229GLMap
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) S := by
  classical
  let y : S2009Pairs := S2218PairEquiv.symm S
  have hy : S2218PairEquiv y = S := Equiv.apply_symm_apply S2218PairEquiv S
  have hpair_equiv : ∀ x : S2009Pairs,
      S2218PairEquiv x = S2180PairMap S2172AffineBasis x := by
    intro x
    exact (S2186BasisCompatiblePairEquiv S2172AffineBasis).pairEquiv_apply x
  have hg : S2229GLMap
      (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) =
      S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ := by
    rw [S2243GLMap_eq_id]
    rfl
  have hnat := h σ y
  calc
    S2056PairMap σ S
        = S2056PairMap σ (S2180PairMap S2172AffineBasis y) := by
            rw [← hy, hpair_equiv y]
    _ = S2180PairMap S2172AffineBasis
          (pairAct
            (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ) y) :=
          hnat.symm
    _ = S2180PairMap S2172AffineBasis
          (pairAct
            (S2229GLMap
              (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) y) := by
          rw [hg]
    _ = S2218PairEquiv
          (pairAct
            (S2229GLMap
              (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) y) :=
          (hpair_equiv _).symm
    _ = S2218PairPerm
          (S2229GLMap
            (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) S := by
          rw [← hy, S2218PairPerm_apply]

/-- The main theorem in the form in which S2511 is an explicit hypothesis:
assuming the affine-basis naturality, the pointwise pair compatibility holds. -/
theorem S2512PairCompatibility_pointwise_of_affineBasisNaturality
    (h : S2512AffineBasisNaturality)
    (σ : S1725AbsoluteGalois) (S : S2056Pair) :
    S2056PairMap σ S =
      S2218PairPerm
        (S2229GLMap
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) S :=
  S2512PairCompatibility_pointwise_of_naturality
    (S2512PairNaturality_of_affineBasis h) σ S

/-- Main theorem, pointwise form, unconditional. -/
theorem S2512PairCompatibility_pointwise
    (σ : S1725AbsoluteGalois) (S : S2056Pair) :
    S2056PairMap σ S =
      S2218PairPerm
        (S2229GLMap
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) S :=
  S2512PairCompatibility_pointwise_of_affineBasisNaturality
    S2512AffineBasisNaturality_actual σ S

/-! ## 5. Function form -/

/-- Main theorem, function form, conditional on the S2511 naturality. -/
theorem S2512PairCompatibility_of_affineBasisNaturality
    (h : S2512AffineBasisNaturality) (σ : S1725AbsoluteGalois) :
    S2056PairMap σ =
      S2218PairPerm
        (S2229GLMap
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) :=
  funext (S2512PairCompatibility_pointwise_of_affineBasisNaturality h σ)

/-- Main theorem, function form, unconditional. -/
theorem S2512PairCompatibility (σ : S1725AbsoluteGalois) :
    S2056PairMap σ =
      S2218PairPerm
        (S2229GLMap
          (S1720Curve.galoisLTorsionMatrixRepresentation S1982Five S1982Basis σ)) :=
  funext (S2512PairCompatibility_pointwise σ)

/-! ## 6. Axiom footprint -/

#print axioms S2512Basis_toLin
#print axioms S2512AffineBasis_coe
#print axioms S2512AffineBasisNaturality_actual
#print axioms S2512PairNaturality_of_affineBasis
#print axioms S2512PairNaturality_actual
#print axioms S2512PairCompatibility_pointwise_of_naturality
#print axioms S2512PairCompatibility_pointwise
#print axioms S2512PairCompatibility

end LeanFormal.IUT.XiFPaper.S2512PairCompatibilityActualAdapted

end
