import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPreglueDataFromPieces

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {G : Type u} [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
variable {S : Scheme.{u}}

abbrev quotientBase : Scheme.{u} := Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G)))

abbrev pieceScheme (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) (i : C.index) : Scheme.{u} :=
  (quotientPieceOpen (R := R) (A := A) (G := G) (C.element i) : (quotientBase (R := R) (A := A) (G := G)).Opens).toScheme

noncomputable def pieceOpenCover
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    (quotientBase (R := R) (A := A) (G := G)).OpenCover :=
  { I₀ := C.index
    X := pieceScheme (R := R) (A := A) (G := G) C
    f := fun i => (quotientPieceOpen (R := R) (A := A) (G := G) (C.element i)).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      constructor
      · intro x
        have hx : x ∈ (⨆ i, quotientPieceOpen (R := R) (A := A) (G := G) (C.element i)) := by
          rw [C.cover_eq_top]; trivial
        rw [TopologicalSpace.Opens.mem_iSup] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, ⟨x, hi⟩, rfl⟩
      · infer_instance }

noncomputable def preglueDataFromPieces
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G))
    (base : quotientBase (R := R) (A := A) (G := G) ⟶ S) [Etale base] :
    AffineLocalQuotientPreglueData S where
  J := C.index
  U := pieceScheme (R := R) (A := A) (G := G) C
  V := fun ij => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.V ij
  f := fun i j => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.f i j
  f_open := fun i j => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.f_open i j
  f_hasPullback := fun i j k => inferInstance
  f_id := fun i => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.f_id i
  t := fun i j => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.t i j
  t_id := fun i => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.t_id i
  t' := fun i j k => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.t' i j k
  t_fac := fun i j k => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.t_fac i j k
  cocycle := fun i j k => (pieceOpenCover (R := R) (A := A) (G := G) C).gluedCover.cocycle i j k
  q := fun i => (quotientPieceOpen (R := R) (A := A) (G := G) (C.element i)).ι ≫ base
  q_etale := fun i => by infer_instance

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPreglueDataFromPieces
