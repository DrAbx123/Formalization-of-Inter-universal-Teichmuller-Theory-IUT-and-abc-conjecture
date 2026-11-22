import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction

/-!
# S1894: the D5 large-image input on the actual curve E'/F' (S1720)

S1725 constructs the paper's Definition 3.1(c) record 'SourceTorsionClause l'
for the actual curve 'E' = S1667Punctured.baseChange F'' over the actual number
field 'F' = SplittingField (S1687H * (X^2 + 1))' of S1720, conditional on one
explicit source input

  'S1725ImageContainsSL2 l = exists b : E'[l] ~= (Fin 2 -> ZMod l),
     SL_2(F_l) <= range (rho_{l,b})'.

This file attacks exactly that input.  It proves that the existential basis in
it is *not* an independent gap: the containment condition is invariant under
change of basis, because in a matrix group

  'Subgroup.map Matrix.SpecialLinearGroup.toGL top = det.ker'
  (S1894SL2_eq_detKer),

i.e. SL_2(F_l) is precisely the subgroup of matrices of determinant one, and
'det.ker' is conjugation invariant.  Consequently the 'exists a basis' form is
equivalent to the 'for every basis' form
(S1894ImageContainsSL2_iff_forall_of_basisGap), and the image input splits
exactly into

  rank-two freeness of E'[l]  (the tree's open RankTwoTorsionBasisGap)
  AND the basis-free large-image condition S1894LargeImageInput l
  (S1894ImageContainsSL2_iff).

The basis-free condition is stated as: for every rank-two ZMod l-basis of the
actual E'[l], the image of the actual mod-l Galois representation contains
every determinant-one matrix.  Equivalently (S1894ImageTail_iff_detOne) it is
the literal paper condition SL_2(F_l) <= im rho_{l,b}.

No part of this file assumes, asserts or fakes the large-image statement: the
only occurrences of S1725ImageContainsSL2 are as a hypothesis or inside an
equivalence.  The paper's D5 clause for E'/F' is reconstructed below with its
image field set to the basis-free condition (S1894SourceTorsionClause), so
that the clause exposes exactly what the paper supplies and nothing else.

Status (see S1894ExactMissing): the arithmetic side of D5 is complete for
E'/F' (S1720 reduction/split reduction, S1724/S1721 torsion 2*3, S1725 mu_6
carrier and l-coprimality at the selected bad place above 5 or 7).  The one
open mathematical input is the Serre-style large-image statement for the actual
mod-l image; it is not a formal consequence of any object in the tree and no
proof of it is introduced here.

The basis-independence argument is proved for an arbitrary punctured elliptic
curve (section 7), so it applies verbatim to the S1667 curve over S1687Field
(S1715) and to the S1280 concrete Gaussian curve of the paper route as well.

Machine-checked summary of the gap:

* S1894SL2_eq_detKer : SL_2(F_l) is exactly det.ker inside GL_2(F_l);
* S1894GenImageTail_congr : the containment is independent of the basis;
* S1894ImageContainsSL2_iff : the D5 image input is exactly the rank-two basis
  gap together with the basis-free large-image condition;
* S1894ExactMissing_iff_serre : the first missing input is literally the frozen
  'SerreStyleLargeImageStatement E' l' of the tree;
* S1894SourceTorsionClause : the paper's Definition 3.1(c) record for E'/F'
  with the basis-free image field, every other field being a theorem
  (S1724/S1721 torsion 2*3, S1725 mu_6 carrier and l-coprimality, surjectivity
  of the representation onto its range).

All declarations below depend only on propext, Classical.choice and
Quot.sound; see the axiom footprint at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.Theorem311Source

/-! ## 1. SL_2(F_l) is the determinant-one subgroup of GL_2(F_l) -/

/-- The image of the special linear group in the general linear group is
literally the kernel of the determinant.  This is what makes the paper's
containment SL_2(F_l) <= im rho a basis-free condition on the abstract
ZMod l-linear image. -/
theorem S1894SL2_eq_detKer (l : PrimeGeFive) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) =
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker := by
  ext A
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, -, rfl⟩
    exact MonoidHom.mem_ker.mpr (Matrix.SpecialLinearGroup.coeToGL_det g)
  · intro hA
    rw [MonoidHom.mem_ker] at hA
    refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) (ZMod l.value)), ?_⟩, Subgroup.mem_top _, ?_⟩
    · have h := Matrix.GeneralLinearGroup.val_det_apply A
      rw [hA] at h
      simpa using h.symm
    · exact Units.ext rfl

/-- Membership in the determinant-one subgroup, transported through the
identification of S1894SL2_eq_detKer. -/
theorem S1894mem_detKer_iff (l : PrimeGeFive)
    (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :
    A ∈ (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker ↔
      Matrix.GeneralLinearGroup.det A = 1 :=
  MonoidHom.mem_ker

/-- Conjugation preserves the determinant-one subgroup. -/
theorem S1894det_conj (l : PrimeGeFive)
    (c k : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
    (hk : Matrix.GeneralLinearGroup.det k = 1) :
    Matrix.GeneralLinearGroup.det (c * k * c⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv, hk, mul_one, mul_inv_cancel]

/-- The determinant-one subgroup is invariant under conjugation by any element
of GL_2(F_l).  Hence the paper containment does not depend on the chosen
basis: conjugating the image by a change-of-basis matrix does not change
whether it contains all determinant-one matrices. -/
theorem S1894detKer_le_conj_iff (l : PrimeGeFive)
    (c : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) :
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker ≤ H ↔
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker ≤
        Subgroup.map (MulAut.conj c).toMonoidHom H := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_map]
    have hx' : c⁻¹ * x * c ∈
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker := by
      rw [S1894mem_detKer_iff]
      simpa using S1894det_conj l c⁻¹ x (S1894mem_detKer_iff l x |>.mp hx)
    refine ⟨c⁻¹ * x * c, h hx', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro h x hx
    have hx' : c * x * c⁻¹ ∈
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker := by
      rw [S1894mem_detKer_iff]
      exact S1894det_conj l c x (S1894mem_detKer_iff l x |>.mp hx)
    have hmem := h hx'
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hyx' : c * y = c * x := mul_right_cancel hyx
    have : y = x := mul_left_cancel hyx'
    rw [this] at hy
    exact hy

/-! ## 2. Change of basis conjugates the matrix representation -/

/-- The tree's 'galoisLTorsionMatrixRepresentation_acts', read inside the actual
torsion module E'[l]: the 'b'-coordinates of the image of a torsion point are
the matrix of the representation applied to the 'b'-coordinates of the point. -/
theorem S1894MatrixRep_acts (l : PrimeGeFive) (b : S1725TorsionBasis l)
    (sigma : S1725AbsoluteGalois) (x : Fin 2 → ZMod l.value) :
    b ((Matrix.GeneralLinearGroup.toLin
        (S1720Curve.galoisLTorsionMatrixRepresentation l b sigma)).toLinearEquiv x) =
      S1720Curve.galoisActionOnLTorsionLinearEquiv l sigma (b x) := by
  apply Subtype.ext
  have h := PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_acts
    l S1720Curve b sigma x
  simpa [PuncturedEllipticCurve.galoisActionOnLTorsion_coe,
    PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply] using h

/-- An invertible linear endomorphism, read back as a linear equivalence. -/
theorem S1894ofLinearEquiv_toLinearEquiv (l : PrimeGeFive)
    (u : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value)) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv u).toLinearEquiv = u := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- Reading back the unit attached to a linear equivalence is injective. -/
theorem S1894toLinearEquiv_injective (l : PrimeGeFive) :
    Function.Injective
      (LinearMap.GeneralLinearGroup.toLinearEquiv (R := ZMod l.value)
        (M := Fin 2 → ZMod l.value)) := by
  intro f g hfg
  apply Units.ext
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun e : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value) =>
      (e : (Fin 2 → ZMod l.value) → (Fin 2 → ZMod l.value)) x) hfg
  simpa using h

/-- The change of basis from 'b' to 'b'': the unique linear equivalence 'u' with
'b'' (u y) = b y'. -/
noncomputable def S1894BasisChange (l : PrimeGeFive) (b b' : S1725TorsionBasis l) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value) :=
  b.trans b'.symm

/-- The defining property of the change of basis. -/
theorem S1894BasisChange_apply (l : PrimeGeFive) (b b' : S1725TorsionBasis l)
    (y : Fin 2 → ZMod l.value) :
    b' (S1894BasisChange l b b' y) = b y := by
  simp [S1894BasisChange, LinearEquiv.trans_apply]

/-- The change of basis as an element of GL_2(F_l). -/
noncomputable def S1894BasisChangeGL (l : PrimeGeFive) (b b' : S1725TorsionBasis l) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (S1894BasisChange l b b'))

/-- The GL_2 element really is the chosen change of basis. -/
theorem S1894BasisChangeGL_toLinearEquiv (l : PrimeGeFive)
    (b b' : S1725TorsionBasis l) :
    (Matrix.GeneralLinearGroup.toLin (S1894BasisChangeGL l b b')).toLinearEquiv =
      S1894BasisChange l b b' := by
  have h : Matrix.GeneralLinearGroup.toLin (S1894BasisChangeGL l b b') =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (S1894BasisChange l b b') :=
    MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin _
  rw [h, S1894ofLinearEquiv_toLinearEquiv]

/-- **The matrix representations attached to two different rank-two bases of the
actual E'[l] are conjugate in GL_2(F_l).**  This is the only place where the
choice of basis enters the D5 image condition. -/
theorem S1894MatrixRep_conj (l : PrimeGeFive) (b b' : S1725TorsionBasis l) :
    ∀ sigma : S1725AbsoluteGalois,
      S1720Curve.galoisLTorsionMatrixRepresentation l b' sigma =
        S1894BasisChangeGL l b b' *
            S1720Curve.galoisLTorsionMatrixRepresentation l b sigma *
          (S1894BasisChangeGL l b b')⁻¹ := by
  set u : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value) :=
    S1894BasisChange l b b' with hu
  have hstep : Matrix.GeneralLinearGroup.toLin (S1894BasisChangeGL l b b') =
      LinearMap.GeneralLinearGroup.ofLinearEquiv u := by
    rw [hu]
    exact MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin _
  have hbu : ∀ y, b' (u y) = b y := by
    intro y
    rw [hu]
    exact S1894BasisChange_apply l b b' y
  intro sigma
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.map_inv, hstep]
  apply S1894toLinearEquiv_injective l
  rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    S1894ofLinearEquiv_toLinearEquiv]
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  apply b'.injective
  have hbx : b' x = b (u.symm x) := by
    rw [← hbu (u.symm x), LinearEquiv.apply_symm_apply]
  rw [S1894MatrixRep_acts l b' sigma x]
  simp only [hbu]
  rw [S1894MatrixRep_acts l b sigma (u.symm x), hbx]

/-- The ranges of the matrix representations attached to two bases are conjugate
subgroups of GL_2(F_l). -/
theorem S1894MatrixRep_range_conj (l : PrimeGeFive) (b b' : S1725TorsionBasis l) :
    (S1720Curve.galoisLTorsionMatrixRepresentation l b').range =
      Subgroup.map (MulAut.conj (S1894BasisChangeGL l b b')).toMonoidHom
        (S1720Curve.galoisLTorsionMatrixRepresentation l b).range := by
  ext A
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨sigma, rfl⟩
    refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation l b sigma,
      MonoidHom.mem_range.mpr ⟨sigma, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (S1894MatrixRep_conj l b b' sigma).symm
  · rintro ⟨B, hB, hBA⟩
    rw [MonoidHom.mem_range] at hB
    obtain ⟨sigma, rfl⟩ := hB
    refine ⟨sigma, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hBA
    rw [S1894MatrixRep_conj l b b' sigma]
    exact hBA

/-- **The D5 image condition of the paper does not depend on the basis**: the
containment 'SL_2(F_l) <= im rho_{l,b}' holds for one rank-two basis of E'[l]
if and only if it holds for every one. -/
theorem S1894ImageTail_congr (l : PrimeGeFive) (b b' : S1725TorsionBasis l) :
    S1725ImageTail l b ↔ S1725ImageTail l b' := by
  have h := S1894detKer_le_conj_iff l (S1894BasisChangeGL l b b')
    (S1720Curve.galoisLTorsionMatrixRepresentation l b).range
  rw [← S1894MatrixRep_range_conj l b b'] at h
  rw [S1725ImageTail, S1725ImageTail, S1894SL2_eq_detKer] at *
  exact h

/-- The existential-basis form of the D5 image input is the universal-basis
form, as soon as one rank-two basis exists at all. -/
theorem S1894ImageContainsSL2_iff_forall_of_basisGap (l : PrimeGeFive)
    (hb : S1725RankTwoBasisGap l) :
    S1725ImageContainsSL2 l ↔ ∀ b : S1725TorsionBasis l, S1725ImageTail l b := by
  constructor
  · rintro ⟨b0, h0⟩ b
    exact (S1894ImageTail_congr l b b0).mpr h0
  · intro h
    exact ⟨hb.some, h hb.some⟩

/-- **Exact decomposition of the D5 image input on the actual curve E'/F'.**  It
is the conjunction of the rank-two freeness of E'[l] and the basis-free
large-image condition; no further basis-dependent content remains. -/
theorem S1894ImageContainsSL2_iff (l : PrimeGeFive) :
    S1725ImageContainsSL2 l ↔
      S1725RankTwoBasisGap l ∧ ∀ b : S1725TorsionBasis l, S1725ImageTail l b := by
  constructor
  · intro h
    refine ⟨S1725ImageContainsSL2_basis l h, ?_⟩
    rintro b
    exact (S1894ImageTail_congr l b h.choose).mpr h.choose_spec
  · rintro ⟨hb, h⟩
    exact (S1894ImageContainsSL2_iff_forall_of_basisGap l hb).mpr h

/-! ## 3. The basis-free large-image input on E'/F' -/

/-- **The D5 large-image input in basis-free form**: for *every* rank-two
ZMod l-basis of the actual E'[l], the matrix of the actual mod-l Galois
representation has image containing all determinant-one matrices. -/
def S1894LargeImageInput (l : PrimeGeFive) : Prop :=
  ∀ b : S1725TorsionBasis l, S1725ImageTail l b

/-- The same condition written as a determinant-one containment.  This is the
literal content of 'SL_2(F_l) <= im rho_{l,b}'. -/
theorem S1894LargeImageInput_iff_detKer (l : PrimeGeFive) :
    S1894LargeImageInput l ↔
      ∀ b : S1725TorsionBasis l,
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker ≤
          (S1720Curve.galoisLTorsionMatrixRepresentation l b).range := by
  simp only [S1894LargeImageInput, S1725ImageTail, S1894SL2_eq_detKer]

/-- The basis-free input implies the paper's D5 clause for E'/F' as soon as
E'[l] is free of rank two. -/
noncomputable def S1894SourceTorsionClause_of_basis_free (l : PrimeGeFive)
    (hb : S1725RankTwoBasisGap l) (h : S1894LargeImageInput l) :
    SourceTorsionClause.{0, 0, 0} l :=
  S1725SourceTorsionClause l
    ((S1894ImageContainsSL2_iff_forall_of_basisGap l hb).mpr h)

/-- **A sufficient condition in the tree's vocabulary**: if the mod-l image is
all of GL_2(F_l) in one basis, the D5 image input holds.  This records what
would have to be proved, without asserting it. -/
theorem S1894ImageContainsSL2_of_fullRange (l : PrimeGeFive)
    (b : S1725TorsionBasis l)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation l b).range = ⊤) :
    S1725ImageContainsSL2 l :=
  ⟨b, by
    show Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (S1720Curve.galoisLTorsionMatrixRepresentation l b).range
    rw [h]
    exact le_top⟩

/-! ## 4. The arithmetic side of D5 for E'/F' is unconditional -/

/-- The paper's condition (b) for the actual curve E'/F' (2 * 3-torsion
rational), from S1724/S1721. -/
theorem S1894SixTorsionIndependent :
    S1725SixTorsionIndependent :=
  S1725SixTorsionIndependent_proved

/-- The residue-characteristic half of Definition 3.1(c) at the selected
actual bad place, for every l (S1725). -/
theorem S1894LTorsionCompatible_proved (l : PrimeGeFive) :
    S1725LTorsionCompatible l :=
  S1725LTorsionCompatible_proved l

/-- E' has split multiplicative reduction at the selected bad place (S1720). -/
theorem S1894SplitAtPlace (l : PrimeGeFive) :
    S1720Curve.HasSplitMultiplicativeReductionAt (S1725D5Place l) :=
  S1725SplitAtPlace l

/-- The residue characteristic of the selected bad place is odd. -/
theorem S1894OddResidue (l : PrimeGeFive) :
    Odd (NumberFieldFinitePlace.residueCharacteristic (S1725D5Place l)) :=
  S1725OddResidue l

/-- The D5 torsion carrier is the literal mu_6 of F', with six elements. -/
theorem S1894SixTorsionCarrier_card :
    Nat.card S1725SixTorsionCarrier = 6 :=
  S1725SixTorsionCarrier_card

/-- The D5 torsion label is the primitive-root label, hence surjective onto the
six slots. -/
theorem S1894SixTorsionLabel_surjective :
    Function.Surjective S1725SixTorsionLabel :=
  S1725SixTorsionLabel_surjective

/-! ## 5. The paper's D5 clause with the basis-free image field -/

/-- The paper's Definition 3.1(c) record for the actual curve E'/F', with the
image field stated as the *basis-free* large-image input.  Every field other
than the image is the actual arithmetic already proved in S1720/S1721/S1724/
S1725; the image field is exactly the open input, exposed as a hypothesis. -/
noncomputable def S1894SourceTorsionClause (l : PrimeGeFive)
    (h : S1894LargeImageInput l) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1725SixTorsionCarrier
  torsionCarrierLaw := inferInstance
  torsionLabel := S1725SixTorsionLabel
  torsionNonempty := ⟨1⟩
  representationCarrier := S1725AbsoluteGalois
  representationCarrierLaw := inferInstance
  representationGroup := S1725RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1725Representation l
  representation_surjective := S1725Representation_surjective l
  imageContainsSL2 := S1894LargeImageInput l
  imageContainsSL2_proved := h
  sixTorsionIndependent := S1725SixTorsionIndependent
  sixTorsionIndependent_proved := S1725SixTorsionIndependent_proved
  lTorsionCompatible := S1725LTorsionCompatible l
  lTorsionCompatible_proved := S1725LTorsionCompatible_proved l

/-- The image field of the reconstructed clause is literally the basis-free
large-image input. -/
@[simp] theorem S1894SourceTorsionClause_imageContainsSL2 (l : PrimeGeFive)
    (h : S1894LargeImageInput l) :
    (S1894SourceTorsionClause l h).imageContainsSL2 = S1894LargeImageInput l :=
  rfl

/-- The six-torsion field of the reconstructed clause is the actual S1724
theorem. -/
@[simp] theorem S1894SourceTorsionClause_sixTorsionIndependent
    (l : PrimeGeFive) (h : S1894LargeImageInput l) :
    (S1894SourceTorsionClause l h).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1720Curve := rfl

/-- The l-compatibility field of the reconstructed clause is the actual
residue-characteristic condition. -/
@[simp] theorem S1894SourceTorsionClause_lTorsionCompatible
    (l : PrimeGeFive) (h : S1894LargeImageInput l) :
    (S1894SourceTorsionClause l h).lTorsionCompatible =
      S1725LTorsionCompatible l := rfl

/-- Given a rank-two basis, the image field of the reconstructed clause is
equivalent to the paper's existential large-image statement for E'/F'. -/
theorem S1894SourceTorsionClause_image_iff (l : PrimeGeFive)
    (hb : S1725RankTwoBasisGap l) (h : S1894LargeImageInput l) :
    (S1894SourceTorsionClause l h).imageContainsSL2 ↔ S1725ImageContainsSL2 l :=
  (S1894ImageContainsSL2_iff_forall_of_basisGap l hb).symm

/-- The reconstructed clause carries the actual absolute Galois group of F'
and the actual mod-l representation on E'[l]. -/
theorem S1894SourceTorsionClause_representation (l : PrimeGeFive)
    (h : S1894LargeImageInput l) :
    (S1894SourceTorsionClause l h).representationCarrier = S1725AbsoluteGalois ∧
      (S1894SourceTorsionClause l h).representation = S1725Representation l :=
  ⟨rfl, rfl⟩

/-! ## 6. The exact first missing statement -/

/-- **The exact first missing input**: the conjunction of rank-two freeness of
the actual E'[l] and the basis-free large-image condition. -/
def S1894ExactMissing (l : PrimeGeFive) : Prop :=
  S1725RankTwoBasisGap l ∧ S1894LargeImageInput l

/-- The exact first missing input is literally the paper's large-image source
input for E'/F'. -/
theorem S1894ExactMissing_iff_image (l : PrimeGeFive) :
    S1894ExactMissing l ↔ S1725ImageContainsSL2 l :=
  (S1894ImageContainsSL2_iff l).symm

/-- The exact first missing input is literally the frozen Serre-style
large-image statement for the actual curve E'. -/
theorem S1894ExactMissing_iff_serre (l : PrimeGeFive) :
    S1894ExactMissing l ↔ SerreStyleLargeImageStatement S1720Curve l :=
  (S1894ExactMissing_iff_image l).trans (S1725ImageContainsSL2_iff_serre l)

/-- The rank-two part of the missing input is exactly the finrank-two statement
for the actual torsion module, once it is known to be finite. -/
theorem S1894RankTwoBasisGap_iff_finrank (l : PrimeGeFive)
    [Module.Finite (ZMod l.value) (S1720Curve.LTorsion l)] :
    S1725RankTwoBasisGap l ↔
      Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2 :=
  rankTwoTorsionBasisGap_iff_finrank_eq_two S1720Curve l

/-- The D5 clause for E'/F' exists as soon as the exact missing input is
supplied: nothing else about the actual curve is assumed. -/
theorem S1894D5_nonempty_of_exactMissing (l : PrimeGeFive)
    (M : S1894ExactMissing l) : Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  ⟨S1894SourceTorsionClause_of_basis_free l M.1 M.2⟩

/-- Uniform form: supplying the exact missing input at every l supplies the
paper's D5 clause at every l. -/
theorem S1894D5_all_of_exactMissing (h : ∀ l : PrimeGeFive, S1894ExactMissing l) :
    ∀ l : PrimeGeFive, Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  fun l => S1894D5_nonempty_of_exactMissing l (h l)

/-- Supplying the paper's large-image input for E'/F' supplies the D5 clause:
the rest of Definition 3.1(c) is already a theorem for the actual curve. -/
theorem S1894D5_of_serre (l : PrimeGeFive)
    (h : SerreStyleLargeImageStatement S1720Curve l) :
    Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  S1894D5_nonempty_of_exactMissing l ((S1894ExactMissing_iff_serre l).mpr h)

/-- **Recognition of the image field.**  Any D5 clause whose image field is the
basis-free large-image input has, as its proved content, exactly the paper's
large-image statement for E'/F'.  There is no hidden extra input. -/
theorem S1894LargeImageInput_of_clause (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (hT : T.imageContainsSL2 = S1894LargeImageInput l) :
    S1894LargeImageInput l :=
  hT ▸ T.imageContainsSL2_proved

/-- The clause constructed in section 5 is recognised by the previous theorem:
its image content is exactly the large-image input. -/
theorem S1894LargeImageInput_of_constructedClause (l : PrimeGeFive)
    (h : S1894LargeImageInput l) :
    S1894LargeImageInput l :=
  S1894LargeImageInput_of_clause l (S1894SourceTorsionClause l h) rfl

/-! ## 7. The same reduction for an arbitrary actual curve -/

section Generic

variable {F : Type} [Field F]

/-- A rank-two ZMod l-basis of the actual l-torsion of an arbitrary punctured
elliptic curve. -/
abbrev S1894GenBasis (X : PuncturedEllipticCurve F) (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l

/-- The paper's SL_2 containment for an arbitrary actual curve and basis. -/
def S1894GenImageTail (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (b : S1894GenBasis X l) : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
    (X.galoisLTorsionMatrixRepresentation l b).range

/-- The matrix representation acts by the Galois action, read inside E[l]. -/
theorem S1894GenMatrixRep_acts (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (b : S1894GenBasis X l)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (x : Fin 2 → ZMod l.value) :
    b ((Matrix.GeneralLinearGroup.toLin
        (X.galoisLTorsionMatrixRepresentation l b sigma)).toLinearEquiv x) =
      X.galoisActionOnLTorsionLinearEquiv l sigma (b x) := by
  apply Subtype.ext
  have h := PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_acts
    l X b sigma x
  simpa [PuncturedEllipticCurve.galoisActionOnLTorsion_coe,
    PuncturedEllipticCurve.galoisActionOnLTorsionLinearEquiv_apply] using h

/-- The change of basis from 'b' to 'b''. -/
noncomputable def S1894GenBasisChange (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (b b' : S1894GenBasis X l) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value) :=
  b.trans b'.symm

theorem S1894GenBasisChange_apply (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (b b' : S1894GenBasis X l) (y : Fin 2 → ZMod l.value) :
    b' (S1894GenBasisChange X l b b' y) = b y := by
  simp [S1894GenBasisChange, LinearEquiv.trans_apply]

/-- The change of basis as an element of GL_2(F_l). -/
noncomputable def S1894GenBasisChangeGL (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (b b' : S1894GenBasis X l) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (S1894GenBasisChange X l b b'))

theorem S1894GenBasisChangeGL_toLinearEquiv (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (b b' : S1894GenBasis X l) :
    (Matrix.GeneralLinearGroup.toLin
        (S1894GenBasisChangeGL X l b b')).toLinearEquiv =
      S1894GenBasisChange X l b b' := by
  have h : Matrix.GeneralLinearGroup.toLin (S1894GenBasisChangeGL X l b b') =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (S1894GenBasisChange X l b b') :=
    MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin _
  rw [h, S1894ofLinearEquiv_toLinearEquiv]

/-- **Change of basis only conjugates the matrix representation**, for any
actual curve. -/
theorem S1894GenMatrixRep_conj (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (b b' : S1894GenBasis X l) :
    ∀ sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      X.galoisLTorsionMatrixRepresentation l b' sigma =
        S1894GenBasisChangeGL X l b b' *
            X.galoisLTorsionMatrixRepresentation l b sigma *
          (S1894GenBasisChangeGL X l b b')⁻¹ := by
  set u : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (Fin 2 → ZMod l.value) :=
    S1894GenBasisChange X l b b' with hu
  have hstep : Matrix.GeneralLinearGroup.toLin (S1894GenBasisChangeGL X l b b') =
      LinearMap.GeneralLinearGroup.ofLinearEquiv u := by
    rw [hu]
    exact MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin _
  have hbu : ∀ y, b' (u y) = b y := by
    intro y
    rw [hu]
    exact S1894GenBasisChange_apply X l b b' y
  intro sigma
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [MulEquiv.map_mul, MulEquiv.map_mul, MulEquiv.map_inv, hstep]
  apply S1894toLinearEquiv_injective l
  rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    S1894ofLinearEquiv_toLinearEquiv]
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  apply b'.injective
  have hbx : b' x = b (u.symm x) := by
    rw [← hbu (u.symm x), LinearEquiv.apply_symm_apply]
  rw [S1894GenMatrixRep_acts X l b' sigma x]
  simp only [hbu]
  rw [S1894GenMatrixRep_acts X l b sigma (u.symm x), hbx]

/-- The ranges are conjugate subgroups of GL_2(F_l). -/
theorem S1894GenMatrixRep_range_conj (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (b b' : S1894GenBasis X l) :
    (X.galoisLTorsionMatrixRepresentation l b').range =
      Subgroup.map (MulAut.conj (S1894GenBasisChangeGL X l b b')).toMonoidHom
        (X.galoisLTorsionMatrixRepresentation l b).range := by
  ext A
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨sigma, rfl⟩
    refine ⟨X.galoisLTorsionMatrixRepresentation l b sigma,
      MonoidHom.mem_range.mpr ⟨sigma, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (S1894GenMatrixRep_conj X l b b' sigma).symm
  · rintro ⟨B, hB, hBA⟩
    rw [MonoidHom.mem_range] at hB
    obtain ⟨sigma, rfl⟩ := hB
    refine ⟨sigma, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hBA
    rw [S1894GenMatrixRep_conj X l b b' sigma]
    exact hBA

/-- **The paper's SL_2 containment is independent of the chosen rank-two basis,
for any actual punctured elliptic curve.**  This is the form in which the
statement applies to every actual curve of the tree (E'/F' of S1720, the S1667
curve over S1687Field, and the S1280 concrete Gaussian curve). -/
theorem S1894GenImageTail_congr (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (b b' : S1894GenBasis X l) :
    S1894GenImageTail X l b ↔ S1894GenImageTail X l b' := by
  have h := S1894detKer_le_conj_iff l (S1894GenBasisChangeGL X l b b')
    (X.galoisLTorsionMatrixRepresentation l b).range
  rw [← S1894GenMatrixRep_range_conj X l b b'] at h
  rw [S1894GenImageTail, S1894GenImageTail, S1894SL2_eq_detKer] at *
  exact h

/-- The existential-basis and universal-basis forms of the large-image
statement agree for every actual curve. -/
theorem S1894GenImageContainsSL2_iff_forall (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) (hb : Nonempty (S1894GenBasis X l)) :
    (∃ b : S1894GenBasis X l, S1894GenImageTail X l b) ↔
      ∀ b : S1894GenBasis X l, S1894GenImageTail X l b := by
  constructor
  · rintro ⟨b0, h0⟩ b
    exact (S1894GenImageTail_congr X l b b0).mpr h0
  · intro h
    exact ⟨hb.some, h hb.some⟩

end Generic

/-- The generic containment is literally the D5 containment of E'/F' at
'S1720Curve'. -/
theorem S1894GenImageTail_curve (l : PrimeGeFive) (b : S1725TorsionBasis l) :
    S1894GenImageTail S1720Curve l b ↔ S1725ImageTail l b :=
  Iff.rfl

/-! ## 7. Axiom footprint -/

#print axioms S1894SL2_eq_detKer
#print axioms S1894detKer_le_conj_iff
#print axioms S1894MatrixRep_acts
#print axioms S1894MatrixRep_conj
#print axioms S1894MatrixRep_range_conj
#print axioms S1894ImageTail_congr
#print axioms S1894ImageContainsSL2_iff_forall_of_basisGap
#print axioms S1894ImageContainsSL2_iff
#print axioms S1894LargeImageInput_iff_detKer
#print axioms S1894SourceTorsionClause_of_basis_free
#print axioms S1894ImageContainsSL2_of_fullRange
#print axioms S1894SourceTorsionClause
#print axioms S1894SourceTorsionClause_image_iff
#print axioms S1894ExactMissing_iff_serre
#print axioms S1894D5_nonempty_of_exactMissing
#print axioms S1894D5_all_of_exactMissing
#print axioms S1894D5_of_serre
#print axioms S1894LargeImageInput_of_clause
#print axioms S1894GenMatrixRep_acts
#print axioms S1894GenMatrixRep_conj
#print axioms S1894GenMatrixRep_range_conj
#print axioms S1894GenImageTail_congr
#print axioms S1894GenImageContainsSL2_iff_forall
#print axioms S1894GenImageTail_curve

end LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual