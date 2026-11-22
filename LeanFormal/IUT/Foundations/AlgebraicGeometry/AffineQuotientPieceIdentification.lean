import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ABCBridge.FiniteEtaleFixedPoints

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification

universe u

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {G : Type u} [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]

abbrev fixedSubalgebra : Subalgebra R A := fixedPointSubalgebra R A G

/-- The affine quotient map q : Spec A -> Spec A^G. -/
noncomputable def affineQuotientMap :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G))) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.val (fixedSubalgebra (R := R) (A := A) (G := G))))

/-- Underlying prime-spectrum map of q. -/
theorem affineQuotientMap_apply (p : PrimeSpectrum A) :
    (affineQuotientMap (R := R) (A := A) (G := G)).base p =
      PrimeSpectrum.comap (Subalgebra.val (fixedSubalgebra (R := R) (A := A) (G := G)) :
        fixedSubalgebra (R := R) (A := A) (G := G) →+* A) p :=
  rfl

/-- Underlying map is surjective because A is integral over A^G. -/
theorem affineQuotientMap_surjective :
    Function.Surjective (affineQuotientMap (R := R) (A := A) (G := G)).base := by
  change Function.Surjective (PrimeSpectrum.comap
    (Subalgebra.val (fixedSubalgebra (R := R) (A := A) (G := G)) :
      fixedSubalgebra (R := R) (A := A) (G := G) →+* A))
  haveI := fixedPointSubalgebra_isIntegral (R := R) (A := A) (G := G)
  exact Algebra.IsIntegral.comap_surjective
    (R := fixedSubalgebra (R := R) (A := A) (G := G)) (S := A)

/-- The section of Spec A corresponding to an element of A. -/
noncomputable def specSectionA (x : A) :
    Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv x

/-- The section of Spec A^G corresponding to an element of A^G. -/
noncomputable def specSectionFixed (x : fixedSubalgebra (R := R) (A := A) (G := G)) :
    Γ(Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G))), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G)))).inv x

/-- The principal G-stable affine piece D(f) in Spec A. -/
noncomputable def pieceOpen (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    (Spec (CommRingCat.of A)).Opens :=
  (Spec (CommRingCat.of A)).basicOpen (specSectionA (f : A))

/-- The corresponding principal piece D(f) in the quotient Spec A^G. -/
noncomputable def quotientPieceOpen (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    (Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G)))).Opens :=
  (Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G)))).basicOpen
    (specSectionFixed f)

/-- q^{-1}(D(f)) = D(f). -/
theorem affineQuotientMap_preimage_quotientPiece
    (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    affineQuotientMap (R := R) (A := A) (G := G) ⁻¹ᵁ
        quotientPieceOpen (R := R) (A := A) (G := G) f =
      pieceOpen (R := R) (A := A) (G := G) f := by
  rw [affineQuotientMap, quotientPieceOpen, pieceOpen, Scheme.preimage_basicOpen]
  apply congrArg (fun s => (Spec (CommRingCat.of A)).basicOpen s)
  exact (congrArg (fun g => g f)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Subalgebra.val (fixedSubalgebra (R := R) (A := A) (G := G)) :
        fixedSubalgebra (R := R) (A := A) (G := G) →+* A)))).symm

/-- The piece D(f) is affine. -/
theorem pieceOpen_isAffine (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    IsAffineOpen (pieceOpen (R := R) (A := A) (G := G) f) :=
  (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen (specSectionA (f : A))

/-- The quotient piece is affine. -/
theorem quotientPieceOpen_isAffine (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) f) :=
  (isAffineOpen_top (Spec (CommRingCat.of (fixedSubalgebra (R := R) (A := A) (G := G))))).basicOpen
    (specSectionFixed f)

/-- Topological quotient piece D(f) inside Spec A^G. -/
noncomputable def quotientPiecePrimeOpen (f : fixedSubalgebra (R := R) (A := A) (G := G)) :
    TopologicalSpace.Opens (PrimeSpectrum (fixedSubalgebra (R := R) (A := A) (G := G))) :=
  PrimeSpectrum.basicOpen f

/-- The topological quotient pieces cover Spec A^G when the corresponding
invariant elements generate the unit ideal. -/
theorem quotientPiecePrimeOpen_iSup_eq_top
    {ι : Type u} (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    (⨆ i, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (s i)) = ⊤ := by
  change (⨆ i, PrimeSpectrum.basicOpen (s i)) = ⊤
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  exact hs

/-- A finite family of invariant elements generating the unit ideal gives a
finite affine quotient-piece cover of Spec A^G. -/
theorem quotientPiece_finite_cover
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    (⨆ i, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (s i)) = ⊤ ∧
      ∀ i, IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) (s i)) :=
  ⟨quotientPiecePrimeOpen_iSup_eq_top (R := R) (A := A) (G := G) s hs,
    fun i => quotientPieceOpen_isAffine (R := R) (A := A) (G := G) (s i)⟩

/-- The affine quotient-piece cover interface consumed by the chart presentation
chain: a finite index, invariant elements, generation, and affine pieces. -/
structure AffineQuotientPieceCover where
  index : Type u
  finite_index : Finite index
  element : index → fixedSubalgebra (R := R) (A := A) (G := G)
  spans_top : Ideal.span (Set.range element) = ⊤
  cover_eq_top : (⨆ i, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (element i)) = ⊤
  piece_affine : ∀ i, IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) (element i))

/-- Construct an affine quotient-piece cover from a finite generating family. -/
noncomputable def AffineQuotientPieceCover.ofFamily
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    AffineQuotientPieceCover (R := R) (A := A) (G := G) where
  index := ι
  finite_index := inferInstance
  element := s
  spans_top := hs
  cover_eq_top := quotientPiecePrimeOpen_iSup_eq_top (R := R) (A := A) (G := G) s hs
  piece_affine := fun i => quotientPieceOpen_isAffine (R := R) (A := A) (G := G) (s i)

theorem AffineQuotientPieceCover.span_top
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    Ideal.span (Set.range C.element) = ⊤ := C.spans_top

theorem AffineQuotientPieceCover.cover
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    (⨆ i, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (C.element i)) = ⊤ := C.cover_eq_top

theorem AffineQuotientPieceCover.preimage
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) (i : C.index) :
    affineQuotientMap (R := R) (A := A) (G := G) ⁻¹ᵁ
        quotientPieceOpen (R := R) (A := A) (G := G) (C.element i) =
      pieceOpen (R := R) (A := A) (G := G) (C.element i) :=
  affineQuotientMap_preimage_quotientPiece (R := R) (A := A) (G := G) (C.element i)

/-- Chart-cover data extracted from an affine quotient-piece cover. -/
structure AffineQuotientChartCoverData where
  cover : AffineQuotientPieceCover (R := R) (A := A) (G := G)
  chart_affine : ∀ i : cover.index,
    IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) (cover.element i))
  chart_cover : (⨆ i : cover.index,
    quotientPiecePrimeOpen (R := R) (A := A) (G := G) (cover.element i)) = ⊤

noncomputable def AffineQuotientChartCoverData.ofFamily
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    AffineQuotientChartCoverData (R := R) (A := A) (G := G) where
  cover := AffineQuotientPieceCover.ofFamily (R := R) (A := A) (G := G) s hs
  chart_affine := fun i => quotientPieceOpen_isAffine (R := R) (A := A) (G := G) (s i)
  chart_cover := quotientPiecePrimeOpen_iSup_eq_top (R := R) (A := A) (G := G) s hs

theorem AffineQuotientChartCoverData.cover_eq_top
    (D : AffineQuotientChartCoverData (R := R) (A := A) (G := G)) :
    (⨆ i : D.cover.index,
      quotientPiecePrimeOpen (R := R) (A := A) (G := G) (D.cover.element i)) = ⊤ :=
  D.chart_cover


theorem AffineQuotientPieceCover.finite_index'
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    Finite C.index := C.finite_index

theorem AffineQuotientPieceCover.cover_eq_top'
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    (⨆ i : C.index, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (C.element i)) = ⊤ :=
  C.cover_eq_top

theorem AffineQuotientPieceCover.piece_affine'
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) (i : C.index) :
    IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) (C.element i)) :=
  C.piece_affine i

theorem AffineQuotientChartCoverData.finite_index
    (D : AffineQuotientChartCoverData (R := R) (A := A) (G := G)) :
    Finite D.cover.index := D.cover.finite_index

theorem AffineQuotientChartCoverData.piece_affine
    (D : AffineQuotientChartCoverData (R := R) (A := A) (G := G)) (i : D.cover.index) :
    IsAffineOpen (quotientPieceOpen (R := R) (A := A) (G := G) (D.cover.element i)) :=
  D.chart_affine i

/-- The quotient-piece cover data as chart-cover data. -/
noncomputable def AffineQuotientPieceCover.toChartCoverData
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    AffineQuotientChartCoverData (R := R) (A := A) (G := G) where
  cover := C
  chart_affine := C.piece_affine
  chart_cover := C.cover_eq_top

theorem AffineQuotientPieceCover.toChartCoverData_cover
    (C : AffineQuotientPieceCover (R := R) (A := A) (G := G)) :
    (C.toChartCoverData (R := R) (A := A) (G := G)).cover = C := rfl

/-- Membership in the topological quotient piece is nonvanishing of the
invariant element at the prime. -/
theorem quotientPiecePrimeOpen_mem_iff
    (f : fixedSubalgebra (R := R) (A := A) (G := G))
    (p : PrimeSpectrum (fixedSubalgebra (R := R) (A := A) (G := G))) :
    p ∈ quotientPiecePrimeOpen (R := R) (A := A) (G := G) f ↔ f ∉ p.asIdeal :=
  PrimeSpectrum.mem_basicOpen f p

/-- A generating family gives a cover with the expected index and elements. -/
theorem AffineQuotientPieceCover.ofFamily_index
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    (AffineQuotientPieceCover.ofFamily (R := R) (A := A) (G := G) s hs).index = ι :=
  rfl

theorem AffineQuotientPieceCover.ofFamily_element
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) (i : ι) :
    (AffineQuotientPieceCover.ofFamily (R := R) (A := A) (G := G) s hs).element i = s i :=
  rfl

theorem AffineQuotientChartCoverData.ofFamily_cover
    {ι : Type u} [Finite ι] (s : ι → fixedSubalgebra (R := R) (A := A) (G := G))
    (hs : Ideal.span (Set.range s) = ⊤) :
    (⨆ i, quotientPiecePrimeOpen (R := R) (A := A) (G := G) (s i)) = ⊤ :=
  quotientPiecePrimeOpen_iSup_eq_top (R := R) (A := A) (G := G) s hs
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientPieceIdentification
