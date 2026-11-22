import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCocycle
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Localized affine quotient preglue data

This file packages actual localized quotient charts/overlaps as an
`AffineLocalQuotientPreglueData`.  The chart and overlap schemes are the actual
`chart`/`overlap` quotient covers from `GlobalQuotientTransitionData`; the
scheme maps and cocycle are explicit input fields, because the fixed-point
tensor reassociation fields of `GlobalQuotientCocycle` are not yet constructed.
-/
namespace ABCBridge.GlobalQuotientPreglueData

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The explicit overlap scheme maps and cocycle for the localized quotient
charts.  The transition maps are the actual scheme maps between the `overlap`
and `chart` covers; the fixed-point reassociation data of the previous file is
what remains to construct them from the algebra identifications. -/
structure LocalizedQuotientOverlapMaps where
  f : ∀ i j, (overlap (G := G) t i j).carrier ⟶ (chart (G := G) t i).carrier
  f_open : ∀ i j, IsOpenImmersion (f i j)
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k)
  f_id : ∀ i, IsIso (f i i)
  t : ∀ i j, (overlap (G := G) t i j).carrier ⟶ (overlap (G := G) t j i).carrier
  t_id : ∀ i, t i i = 𝟙 _
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

/-- Actual preglue data from the localized quotient charts, overlap maps and
the global chart maps. -/
noncomputable def toPreglueData
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) :
    AffineLocalQuotientPreglueData S where
  J := ι
  U i := (chart (G := G) t i).carrier
  V p := (overlap (G := G) t p.1 p.2).carrier
  f i j := M.f i j
  f_open i j := M.f_open i j
  f_hasPullback i j k := M.f_hasPullback i j k
  f_id i := M.f_id i
  t i j := M.t i j
  t_id i := M.t_id i
  t' i j k := M.t' i j k
  t_fac i j k := M.t_fac i j k
  cocycle i j k := M.cocycle i j k
  q i := q i
  q_etale i := q_etale i

/-- The glued scheme of the localized preglue data. -/
noncomputable def glued
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) : Scheme.{u} :=
  (toPreglueData (A := A) (G := G) t M S q q_etale).glued


section PreglueProjections

theorem toPreglueData_J
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).J = ι :=
  rfl

theorem toPreglueData_q
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).q i = q i :=
  rfl

theorem toPreglueData_q_etale
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i : ι) :
    Etale ((toPreglueData (A := A) (G := G) t M S q q_etale).q i) :=
  q_etale i

theorem glued_eq_toPreglueData_glued
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) :
    glued (A := A) (G := G) t M S q q_etale =
      (toPreglueData (A := A) (G := G) t M S q q_etale).glued :=
  rfl

theorem toPreglueData_V
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).V (i, j) =
      (overlap (G := G) t i j).carrier :=
  rfl

theorem toPreglueData_f
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).f i j = M.f i j :=
  rfl

theorem toPreglueData_f_open
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j : ι) :
    IsOpenImmersion ((toPreglueData (A := A) (G := G) t M S q q_etale).f i j) :=
  M.f_open i j

theorem toPreglueData_t
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).t i j = M.t i j :=
  rfl

theorem toPreglueData_t'
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j k : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).t' i j k = M.t' i j k :=
  rfl

theorem toPreglueData_cocycle
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j k : ι) :
    (toPreglueData (A := A) (G := G) t M S q q_etale).cocycle i j k =
      M.cocycle i j k :=
  rfl

end PreglueProjections

end ABCBridge.GlobalQuotientPreglueData