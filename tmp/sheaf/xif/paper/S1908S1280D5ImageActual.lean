import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S1637D5TorsionClauseActual

/-!
# S1908: S1894 basis-independence on the actual S1280 Gaussian curve, and
the S1880 D5 clause / exact residual

This file applies the generic basis-independence of S1894
(`S1894GenImageTail_congr`, `S1894GenImageContainsSL2_iff_forall`, coming
from the change-of-basis conjugation `S1894GenMatrixRep_conj`) to the actual
Gaussian curve of S1280:

  `E_G = (S1280Arithmetic l).curve = concreteSplitPuncturedCurve.baseChange
     GaussianField`, i.e. `y^2 + xy = x^3 + 5` over `Q(i)`.

## What is proved

1. The paper's `SL_2(F_l) <= im rho_{l,b}` containment is independent of the
   chosen rank-two basis of the *actual* Gaussian `E_G[l]`
   (`S1908ImageTail_congr`); the two matrix representations are conjugate by
   the actual change-of-basis matrix in `GL_2(F_l)`
   (`S1908MatrixRep_conj`, `S1908MatrixRep_range_conj`).

2. Consequently the paper's existential large-image field for the Gaussian
   curve, `S1298LargeImageField l = SerreStyleLargeImageStatement E_G l`, is
   exactly the conjunction of the rank-two basis and the basis-free S1894
   input:

     `S1908ExactMissing l <-> S1298LargeImageField l`

   with `S1908ExactMissing l = Nonempty (rank-two basis) /\ S1908LargeImageInput l`
   and `S1908LargeImageInput l = forall b, S1908ImageTail l b`
   (`S1908ExactMissing_iff_serre`).  There is no further basis-dependent
   content.

3. The S1880 D5 clause slot over the actual S1280 Gaussian data is filled
   conditionally on the exact residual
   `S1908D5Residual l` (`S1908SourceTorsionClause`):

     * the torsion carrier is the actual Gaussian `mu_6`
       `S1298SixTorsionCarrier l`, with the actual primitive-root `Fin 6`
       label `s1298SixTorsionLabel l`;
     * the representation is the actual absolute Galois group of `Q(i)` and
       the actual mod-l general-linear representation on `E_G[l]`,
       range-restricted so that it is surjective;
     * the image field is the basis-free S1894 input; given a rank-two basis
       it is equivalent to the literal paper field
       (`S1908SourceTorsionClause_image_iff`);
     * the six-torsion field is the literal paper condition (b)
       `Torsion23Rational E_G` (`S1637SixTorsionIndependent`);
     * the l-compatibility field is the literal condition (c)
       `S1637LTorsionCompatible`.

   The clause feeds `S1880FirstMissing l`
   (`S1908S1880FirstMissing_nonempty`) and the torsion slot of
   `S1280RemainingClauses l` / `S1880PaperClauseSupply l`
   (`S1908RemainingClausesWithTorsion`).  The S1880 aliases
   `S1880FirstMissing l` and `S1880PaperClauseSupply l` are definitionally
   `SourceTorsionClause l` and `S1280RemainingClauses l`; the file states the
   definitional alias `S1908S1880FirstMissing` and uses
   `S1280RemainingClauses` directly, so it does not import the heavy S1880
   route.

4. The exact residual is

     `S1908D5Residual l =
        S1908ExactMissing l /\ S1637SixTorsionIndependent l /\
        S1637LTorsionCompatible l`.

   It is equivalent to the nonemptiness of the faithful S1637 gap
   `S1637D5Gap l` (`S1908D5Residual_iff_gap`) and to the paper field plus
   conditions (b) and (c) (`S1908D5Residual_iff_serre`).  At `l = 5` the
   residual is refuted, because the only bad place of the S1280 selection has
   residue characteristic 5 (`S1908D5Residual_impossible_at_five`, from
   S1637).

## What is *not* proved (the exact boundary, no fake)

* `S1908LargeImageInput l` is the Serre large-image input.  It is exposed,
  never asserted.  Like S1894, this file only proves that its basis-dependent
  and basis-free forms agree.
* `S1637SixTorsionIndependent l = Torsion23Rational E_G` is the literal
  paper condition (b).  It is not proved here.  The audit in
  S1637D5TorsionClauseActual, Section 6, records that this condition is in
  fact **false** for the Gaussian curve: the 2-torsion points have
  `y = -x/2` and `4x^3 + x^2 + 20 = 0`, and this cubic has no root in
  `Q(i)` (it is irreducible over `Q`, and a non-rational conjugate pair in
  `Q(i)` would force the third root to be rational).  That refutation is
  *not* formalized (neither here nor in the tree); this file therefore keeps
  the paper condition as an explicit hypothesis and does not claim that the
  Gaussian D5 clause exists unconditionally.  No `True`/`PUnit` six-torsion
  field, and no `sorry`/`axiom`/arbitrary inhabitant, is used.
* The other three S1880 clause supplies (D6 orbicurve, D7 sections, D8 cusp)
  are untouched; `S1908RemainingClausesWithTorsion` only fills the D5 slot.

## Axiom footprint

Every declaration below depends only on `propext`, `Classical.choice` and
`Quot.sound`; see the probes at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1908S1280D5ImageActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction

/-! ## 1. The actual Gaussian curve and the S1894 basis-independence -/

/-- The actual Gaussian curve of the S1280/S1880 route:
`concreteSplitPuncturedCurve.baseChange GaussianField` over `Q(i)`. -/
abbrev S1908Curve (l : PrimeGeFive) :
    PuncturedEllipticCurve (S1280Arithmetic l).F :=
  (S1280Arithmetic l).curve

/-- A rank-two `ZMod l`-basis of the actual Gaussian `E_G[l]`. -/
abbrev S1908TorsionBasis (l : PrimeGeFive) : Type :=
  S1894GenBasis (S1908Curve l) l

/-- The paper's `SL_2(F_l) <= im rho_{l,b}` containment for the actual
Gaussian matrix representation, in the S1894 generic vocabulary. -/
def S1908ImageTail (l : PrimeGeFive) (b : S1908TorsionBasis l) : Prop :=
  S1894GenImageTail (S1908Curve l) l b

/-- The S1894 containment is exactly the S1637 containment at the same
Gaussian basis. -/
theorem S1908ImageTail_iff_s1637 (l : PrimeGeFive)
    (b : S1908TorsionBasis l) :
    S1908ImageTail l b ↔ S1637ImageContainsSL2 l b :=
  Iff.rfl

/-- **Change of basis conjugates the actual Gaussian matrix
representations.**  This is S1894's generic theorem specialized to
`E_G = concreteSplitPuncturedCurve.baseChange GaussianField`. -/
theorem S1908MatrixRep_conj (l : PrimeGeFive)
    (b b' : S1908TorsionBasis l) :
    ∀ sigma : AlgebraicClosure (S1280Arithmetic l).F ≃ₐ[(S1280Arithmetic l).F]
        AlgebraicClosure (S1280Arithmetic l).F,
      (S1908Curve l).galoisLTorsionMatrixRepresentation l b' sigma =
        S1894GenBasisChangeGL (S1908Curve l) l b b' *
            (S1908Curve l).galoisLTorsionMatrixRepresentation l b sigma *
          (S1894GenBasisChangeGL (S1908Curve l) l b b')⁻¹ :=
  S1894GenMatrixRep_conj (S1908Curve l) l b b'

/-- The ranges of the actual Gaussian representations at two bases are
conjugate subgroups of `GL_2(F_l)`. -/
theorem S1908MatrixRep_range_conj (l : PrimeGeFive)
    (b b' : S1908TorsionBasis l) :
    ((S1908Curve l).galoisLTorsionMatrixRepresentation l b').range =
      Subgroup.map
        (MulAut.conj (S1894GenBasisChangeGL (S1908Curve l) l b b')).toMonoidHom
        ((S1908Curve l).galoisLTorsionMatrixRepresentation l b).range :=
  S1894GenMatrixRep_range_conj (S1908Curve l) l b b'

/-- **The paper's large-image containment is independent of the chosen
rank-two basis of the actual Gaussian `E_G[l]`.** -/
theorem S1908ImageTail_congr (l : PrimeGeFive)
    (b b' : S1908TorsionBasis l) :
    S1908ImageTail l b ↔ S1908ImageTail l b' :=
  S1894GenImageTail_congr (S1908Curve l) l b b'

/-- **The basis-free S1894 large-image input for the actual Gaussian curve**:
for every rank-two `ZMod l`-basis of `E_G[l]`, the actual mod-l
representation contains all determinant-one matrices.  No basis is chosen, no
containment is asserted. -/
def S1908LargeImageInput (l : PrimeGeFive) : Prop :=
  ∀ b : S1908TorsionBasis l, S1908ImageTail l b

/-- The basis-free input is literally the generic S1894 input at the Gaussian
curve. -/
theorem S1908LargeImageInput_iff_gen (l : PrimeGeFive) :
    S1908LargeImageInput l ↔
      ∀ b : S1894GenBasis (S1908Curve l) l,
        S1894GenImageTail (S1908Curve l) l b :=
  Iff.rfl

/-- **The basis-free input is exactly the paper's existential large-image
field once a rank-two basis exists.**  This is S1894's
`S1894GenImageContainsSL2_iff_forall` applied to the actual Gaussian
curve. -/
theorem S1908LargeImageInput_iff_serre_of_basis (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l)) :
    S1908LargeImageInput l ↔ S1298LargeImageField l := by
  have h := S1894GenImageContainsSL2_iff_forall (S1908Curve l) l hb
  change (∀ b : S1894GenBasis (S1908Curve l) l,
      S1894GenImageTail (S1908Curve l) l b) ↔
    (∃ b : S1894GenBasis (S1908Curve l) l,
      S1894GenImageTail (S1908Curve l) l b)
  exact h.symm

/-- The exact S1894-style missing image input on the Gaussian curve: a
rank-two basis together with the basis-free `SL_2` containment. -/
def S1908ExactMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1908TorsionBasis l) ∧ S1908LargeImageInput l

/-- **The S1894 exact missing input on the Gaussian curve is literally the
paper's large-image field `SerreStyleLargeImageStatement E_G l`** (S1298). -/
theorem S1908ExactMissing_iff_serre (l : PrimeGeFive) :
    S1908ExactMissing l ↔ S1298LargeImageField l := by
  constructor
  · rintro ⟨hb, h⟩
    exact (S1908LargeImageInput_iff_serre_of_basis l hb).mp h
  · intro h
    exact ⟨⟨h.choose⟩,
      (S1908LargeImageInput_iff_serre_of_basis l ⟨h.choose⟩).mpr h⟩

/-! ## 2. The S1880 D5 clause with the basis-free image field -/

/-- **The S1880 D5 clause over the actual S1280 Gaussian data, with the
basis-free S1894 image field.**

The carrier, label, absolute Galois group and range-restricted mod-l
representation are the actual S1298 Gaussian objects.  The image field is the
basis-free input; `hb` certifies that a rank-two basis actually exists, so
the universal field is not vacuous.  The six-torsion and l-compatibility
fields are the literal paper conditions (b) and (c). -/
noncomputable def S1908SourceTorsionClause (l : PrimeGeFive)
    (_hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l)
    (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1298SixTorsionCarrier l
  torsionCarrierLaw := s1298SixTorsionCarrierGroup l
  torsionLabel := s1298SixTorsionLabel l
  torsionNonempty := ⟨1⟩
  representationCarrier := SourceAbsoluteGalois (S1280Arithmetic l)
  representationCarrierLaw := inferInstance
  representationGroup := S1298RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1298Representation l
  representation_surjective :=
    (S1298GeneralLinearRepresentation l).rangeRestrict_surjective
  imageContainsSL2 := S1908LargeImageInput l
  imageContainsSL2_proved := himg
  sixTorsionIndependent := S1637SixTorsionIndependent l
  sixTorsionIndependent_proved := h6
  lTorsionCompatible := S1637LTorsionCompatible l
  lTorsionCompatible_proved := hc

@[simp] theorem S1908SourceTorsionClause_torsionCarrier (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).torsionCarrier =
      S1298SixTorsionCarrier l := rfl

@[simp] theorem S1908SourceTorsionClause_torsionLabel (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).torsionLabel =
      s1298SixTorsionLabel l := rfl

@[simp] theorem S1908SourceTorsionClause_representationCarrier
    (l : PrimeGeFive) (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).representationCarrier =
      SourceAbsoluteGalois (S1280Arithmetic l) := rfl

@[simp] theorem S1908SourceTorsionClause_representation (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).representation =
      S1298Representation l := rfl

@[simp] theorem S1908SourceTorsionClause_imageContainsSL2 (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).imageContainsSL2 =
      S1908LargeImageInput l := rfl

@[simp] theorem S1908SourceTorsionClause_sixTorsionIndependent
    (l : PrimeGeFive) (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).sixTorsionIndependent =
      S1637SixTorsionIndependent l := rfl

@[simp] theorem S1908SourceTorsionClause_lTorsionCompatible
    (l : PrimeGeFive) (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).lTorsionCompatible =
      S1637LTorsionCompatible l := rfl

/-- With a rank-two basis, the image field of the constructed clause is
exactly the paper's large-image field for the actual Gaussian curve. -/
theorem S1908SourceTorsionClause_image_iff (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).imageContainsSL2 ↔
      S1298LargeImageField l :=
  S1908LargeImageInput_iff_serre_of_basis l hb

/-- The three non-carrier fields of the clause are exactly the three paper
conditions supplied by the residual. -/
theorem S1908SourceTorsionClause_fields (l : PrimeGeFive)
    (hb : Nonempty (S1908TorsionBasis l))
    (himg : S1908LargeImageInput l) (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    (S1908SourceTorsionClause l hb himg h6 hc).imageContainsSL2 ∧
      (S1908SourceTorsionClause l hb himg h6 hc).sixTorsionIndependent ∧
      (S1908SourceTorsionClause l hb himg h6 hc).lTorsionCompatible :=
  ⟨himg, h6, hc⟩

/-- **The S1880 D5 clause from the paper's existential large-image field.**
This is the direct S1880-facing constructor: `S1298LargeImageField l` is
`SerreStyleLargeImageStatement E_G l`, i.e. exactly the paper's
`SL_2` image input, and the other two conditions are (b) and (c). -/
noncomputable def S1908SourceTorsionClause_of_serre (l : PrimeGeFive)
    (h : S1298LargeImageField l)
    (h6 : S1637SixTorsionIndependent l)
    (hc : S1637LTorsionCompatible l) :
    SourceTorsionClause.{0, 0, 0} l :=
  S1908SourceTorsionClause l ⟨h.choose⟩
    ((S1908LargeImageInput_iff_serre_of_basis l ⟨h.choose⟩).mpr h) h6 hc

/-! ## 3. The exact residual and its consumers -/

/-- **The exact residual of the S1880 D5 clause over the actual S1280
Gaussian data**: the S1894 image gap (rank-two basis plus basis-free large
image), the paper condition (b) `Torsion23Rational E_G`, and the paper
condition (c) l-compatibility at the selected bad place. -/
def S1908D5Residual (l : PrimeGeFive) : Prop :=
  S1908ExactMissing l ∧ S1637SixTorsionIndependent l ∧
    S1637LTorsionCompatible l

/-- The exact residual written with the paper's existential large-image
field. -/
theorem S1908D5Residual_iff_serre (l : PrimeGeFive) :
    S1908D5Residual l ↔
      S1298LargeImageField l ∧ S1637SixTorsionIndependent l ∧
        S1637LTorsionCompatible l := by
  rw [S1908D5Residual, S1908ExactMissing_iff_serre]

/-- The exact residual is literally the nonemptiness of the faithful S1637 D5
gap.  Thus S1894's basis-independence removes exactly the basis-dependence of
the image field and leaves the same three paper conditions. -/
theorem S1908D5Residual_iff_gap (l : PrimeGeFive) :
    S1908D5Residual l ↔ Nonempty (S1637D5Gap l) := by
  constructor
  · rintro ⟨⟨hb, himg⟩, h6, hc⟩
    obtain ⟨b⟩ := hb
    exact ⟨⟨b, (S1908ImageTail_iff_s1637 l b).mp (himg b), h6, hc⟩⟩
  · rintro ⟨G⟩
    exact ⟨⟨⟨G.basis⟩, fun b =>
      (S1908ImageTail_congr l b G.basis).mpr
        ((S1908ImageTail_iff_s1637 l G.basis).mpr G.largeImage)⟩,
      G.sixTorsion, G.lCompatible⟩

/-- The exact residual decomposed into the S1894 image gap and the two
remaining paper conditions. -/
theorem S1908D5Residual_decomposition (l : PrimeGeFive) :
    S1908D5Residual l ↔
      S1908ExactMissing l ∧ S1637SixTorsionIndependent l ∧
        S1637LTorsionCompatible l :=
  Iff.rfl

/-- Supplying the exact residual supplies the S1880 D5 clause. -/
theorem S1908D5Residual_nonempty_clause (l : PrimeGeFive)
    (R : S1908D5Residual l) :
    Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  ⟨S1908SourceTorsionClause l R.1.1 R.1.2 R.2.1 R.2.2⟩

/-- The S1880 D5 slot: by definition the D5 torsion clause.  The S1880 file
`S1880OriginalXiFActual` abbreviates `S1880FirstMissing l` to exactly this
type; stating the alias here keeps the import graph of this file to the
S1280/S1637/S1894 route. -/
abbrev S1908S1880FirstMissing (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-- The alias is literally the S1880 first-missing type. -/
theorem S1908S1880FirstMissing_eq (l : PrimeGeFive) :
    S1908S1880FirstMissing l = SourceTorsionClause.{0, 0, 0} l := rfl

/-- **S1880's first missing field is supplied by the exact residual.**  The
S1880 first missing field is definitionally the D5 torsion clause
`SourceTorsionClause l`; the constructed clause is an inhabitant. -/
theorem S1908S1880FirstMissing_nonempty (l : PrimeGeFive)
    (R : S1908D5Residual l) :
    Nonempty (S1908S1880FirstMissing l) :=
  S1908D5Residual_nonempty_clause l R

/-- At `l = 5` the exact residual is refuted over the actual S1280
selection: its only bad place has residue characteristic 5, so condition (c)
fails. -/
theorem S1908D5Residual_impossible_at_five :
    ¬ S1908D5Residual S1280Five := by
  rintro ⟨-, -, hc⟩
  exact s1637LTorsionCompatible_refuted_at_five hc

/-- The D5 slot of `S1280RemainingClauses l` (equivalently
`S1880PaperClauseSupply l`) filled by the constructed clause; only D6, D7
and D8 remain as supplies. -/
noncomputable def S1908RemainingClausesWithTorsion (l : PrimeGeFive)
    (R : S1908D5Residual l)
    (orbicurve : SourceOrbicurveClause.{0, 0, 0})
    (sections : SourceSectionClause.{0, 0, 0})
    (cusp : SourceCuspClause) :
    S1280RemainingClauses l where
  torsion := S1908SourceTorsionClause l R.1.1 R.1.2 R.2.1 R.2.2
  orbicurve := orbicurve
  sections := sections
  cusp := cusp

@[simp] theorem S1908RemainingClausesWithTorsion_torsion
    (l : PrimeGeFive) (R : S1908D5Residual l)
    (orbicurve : SourceOrbicurveClause.{0, 0, 0})
    (sections : SourceSectionClause.{0, 0, 0})
    (cusp : SourceCuspClause) :
    (S1908RemainingClausesWithTorsion l R orbicurve sections cusp).torsion =
      S1908SourceTorsionClause l R.1.1 R.1.2 R.2.1 R.2.2 := rfl

/-! ## 4. Axiom footprint -/

#print axioms S1908MatrixRep_conj
#print axioms S1908MatrixRep_range_conj
#print axioms S1908ImageTail_congr
#print axioms S1908LargeImageInput_iff_serre_of_basis
#print axioms S1908ExactMissing_iff_serre
#print axioms S1908SourceTorsionClause
#print axioms S1908SourceTorsionClause_image_iff
#print axioms S1908SourceTorsionClause_fields
#print axioms S1908SourceTorsionClause_of_serre
#print axioms S1908D5Residual_iff_serre
#print axioms S1908D5Residual_iff_gap
#print axioms S1908D5Residual_decomposition
#print axioms S1908D5Residual_nonempty_clause
#print axioms S1908S1880FirstMissing_eq
#print axioms S1908S1880FirstMissing_nonempty
#print axioms S1908D5Residual_impossible_at_five
#print axioms S1908RemainingClausesWithTorsion

end LeanFormal.IUT.XiFPaper.S1908S1280D5ImageActual
