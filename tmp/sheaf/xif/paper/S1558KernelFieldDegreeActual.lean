import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.FieldTheory.Finite.Basic
import tmp.sheaf.xif.paper.S1544LTorsionKernelFieldActual

/-!
# S1558: the l-torsion kernel field is nontrivial and has degree at least l(l^2-1)

This file ports the kernel-field half of promachina's
Iut.Foundations.InitialThetaData.ThetaLTorsionRepresentationData
(InitialThetaData.lean:4845-4959) onto the current v4.32.2 local
PuncturedEllipticCurve.galoisLTorsionKernelField of
LeanFormal.IUT.Foundations.Geometry.EllipticTorsion.

The promachina record binds a field K to the fixed field of the mod-l
representation kernel through a torsion basis and an F-algebra isomorphism
kIdentification, and derives embeddedK = kernelFixedField.  Locally the field
K is already the canonical fixed field, so the same large-image input has a
direct numerical consequence.

For a field F of characteristic zero, a punctured elliptic curve X over F, an
odd prime l >= 5 and a ZMod l-basis of the actual torsion module E[l], put

  K := X.galoisLTorsionKernelField l basis

(the fixed field in AlgebraicClosure F of the kernel of the actual
Galois representation on E[l]).  The main results are:

* galoisLTorsionKernelField_finrank_eq_index:
  [K : F] = index of the representation kernel;
* card_specialLinearGroup: |SL2(ZMod l)| = l * (l^2 - 1);
* card_specialLinearGroup_le_kernelSubgroup_index: if the image of the
  representation contains SL2(ZMod l), then the index of the kernel is at
  least |SL2(ZMod l)|;
* galoisLTorsionKernelField_finrank_ge_of_imageContainsSL2:
  ImageContainsSL2 -> l * (l^2 - 1) <= [K : F];
* galoisLTorsionKernelField_finrank_ne_one_of_imageContainsSL2 and
  galoisLTorsionKernelField_ne_bot_of_imageContainsSL2:
  ImageContainsSL2 -> K != F;
* at l = 5, ImageContainsSL2 -> 120 <= [K : F];
* the S1543/S1544 consumer layer: for the actual Gaussian curve,
  gaussianKernelField_finrank_ge_of_imageContainsSL2,
  gaussianKernelField_finrank_ge_120_of_imageContainsSL2,
  gaussianKernelField_ne_bot_of_imageContainsSL2 and
  gaussianKernelField_finrank_ne_one_of_imageContainsSL2, together with
  s1543CorrectedK_of_imageContainsSL2 which fills the S1543 corrected K
  structure with the actual kernel field under ImageContainsSL2.

No source hypothesis is weakened into a definitional identity and no field
data is invented: the statements are conditional on the displayed
ImageContainsSL2 hypothesis, and the conclusion is proved.
-/

noncomputable section

namespace LeanFormal.IUT

universe u

/-- The determinant-kernel subgroup of GL2 over ZMod l is the special linear
group.  This is only a type equivalence; the cardinality computation below
uses it to identify Nat.card SL2 with Nat.card of the determinant kernel. -/
private noncomputable def sl2DetEquiv (l : PrimeGeFive) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) ≃
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g, by
    rw [MonoidHom.mem_ker]
    exact Matrix.SpecialLinearGroup.coeToGL_det g⟩
  invFun A := ⟨(A.1 : Matrix (Fin 2) (Fin 2) (ZMod l.value)), by
    have h : ((Matrix.GeneralLinearGroup.det A.1 : (ZMod l.value)ˣ) : ZMod l.value) = 1 := by
      rw [show Matrix.GeneralLinearGroup.det A.1 = 1 from A.2]
      rfl
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- The exact cardinality of SL2 over ZMod l for an odd prime l. -/
theorem card_specialLinearGroup (l : PrimeGeFive) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) =
      l.value * (l.value ^ 2 - 1) := by
  letI : Fact l.value.Prime := l.factPrime
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) =
      (l.value ^ 2 - 1) * (l.value ^ 2 - l.value) := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) *
      Nat.card (ZMod l.value)ˣ =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) := by
    have hker : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) =
        Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker :=
      Nat.card_congr (sl2DetEquiv l)
    rw [hker]
    have hidx : (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod l.value)).ker.index =
        Nat.card (ZMod l.value)ˣ := by
      rw [Subgroup.index_ker,
        MonoidHom.range_eq_top.mpr
          (Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) (R := ZMod l.value)),
        Subgroup.card_top]
    rw [← hidx, Subgroup.card_mul_index]
  have hunit : Nat.card (ZMod l.value)ˣ = l.value - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) * (l.value - 1) =
      (l.value ^ 2 - 1) * (l.value ^ 2 - l.value) := by
    rw [← hunit, ← hGL]
    exact hcard
  have hl : l.value ^ 2 - l.value = l.value * (l.value - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) * (l.value - 1) =
      (l.value * (l.value ^ 2 - 1)) * (l.value - 1) := by
    rw [h2, hl]
    ac_rfl
  have hpos : 0 < l.value - 1 := by
    have := l.ge_five
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos h3

namespace PuncturedEllipticCurve

variable {F : Type u} [Field F] [CharZero F]
variable (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
variable (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)

/-- The large-image hypothesis of IUT I, Definition 3.1(c): the image of the
actual mod-l Galois representation contains every element of SL2(ZMod l). -/
def LTorsionImageContainsSL2 : Prop :=
  ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      X.galoisLTorsionMatrixRepresentation l basis σ = Matrix.SpecialLinearGroup.toGL g

omit [CharZero F] in
/-- The subgroup-map form of the large-image hypothesis (as used by the
S1544/S1545 corrected-K layer) implies the existential form above. -/
theorem lTorsionImageContainsSL2_of_map_top_le_range
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (X.galoisLTorsionMatrixRepresentation l basis).range) :
    LTorsionImageContainsSL2 X l basis := by
  intro g
  exact hlarge
    (Subgroup.mem_map_of_mem Matrix.SpecialLinearGroup.toGL (Subgroup.mem_top g))

/-- The degree of the kernel field is the index of the representation kernel.
This is the local replacement for promachina's kIdentification/embeddedK
degree computation. -/
theorem galoisLTorsionKernelField_finrank_eq_index :
    Module.finrank F (X.galoisLTorsionKernelField l basis) =
      (X.galoisLTorsionKernelSubgroup l basis).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    X.galoisLTorsionKernelField_fixingSubgroup l basis]

/-- If the image contains SL2, the kernel has at least |SL2| cosets. -/
theorem card_specialLinearGroup_le_kernelSubgroup_index
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) ≤
      (X.galoisLTorsionKernelSubgroup l basis).index := by
  let G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F
  let φ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
    X.galoisLTorsionMatrixRepresentation l basis
  let H : Subgroup G := φ.ker
  have hH : H = X.galoisLTorsionKernelSubgroup l basis := rfl
  haveI hHnormal : H.Normal := MonoidHom.normal_ker φ
  have hHopen : IsOpen (H : Set G) := by
    have h := X.galoisLTorsionMatrixRepresentation_ker_isOpen l basis
    simpa [H, φ] using h
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  let f : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) → G ⧸ H :=
    fun g => QuotientGroup.mk (Classical.choose (hSL2 g))
  have hf : Function.Injective f := by
    intro g1 g2 h
    have hσ1 : φ (Classical.choose (hSL2 g1)) = Matrix.SpecialLinearGroup.toGL g1 :=
      Classical.choose_spec (hSL2 g1)
    have hσ2 : φ (Classical.choose (hSL2 g2)) = Matrix.SpecialLinearGroup.toGL g2 :=
      Classical.choose_spec (hSL2 g2)
    have hmem : Classical.choose (hSL2 g1) / Classical.choose (hSL2 g2) ∈ H :=
      (QuotientGroup.eq_iff_div_mem).mp h
    have hφ : φ (Classical.choose (hSL2 g1) / Classical.choose (hSL2 g2)) = 1 := by
      simpa [H] using hmem
    rw [map_div, hσ1, hσ2] at hφ
    exact Matrix.SpecialLinearGroup.toGL_injective (div_eq_one.mp hφ)
  have hle := Nat.card_le_card_of_injective f hf
  rw [hH] at hle
  rwa [← Subgroup.index_eq_card] at hle

/-- The main degree lower bound: if the mod-l image contains SL2, the kernel
field has degree at least l(l^2-1) over F. -/
theorem galoisLTorsionKernelField_finrank_ge_of_imageContainsSL2
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    l.value * (l.value ^ 2 - 1) ≤
      Module.finrank F (X.galoisLTorsionKernelField l basis) := by
  rw [galoisLTorsionKernelField_finrank_eq_index X l basis]
  calc l.value * (l.value ^ 2 - 1)
      = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :=
        (card_specialLinearGroup l).symm
    _ ≤ (X.galoisLTorsionKernelSubgroup l basis).index :=
        card_specialLinearGroup_le_kernelSubgroup_index X l basis hSL2

/-- In particular, the extension degree is never one under the large-image
hypothesis. -/
theorem galoisLTorsionKernelField_finrank_ne_one_of_imageContainsSL2
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    Module.finrank F (X.galoisLTorsionKernelField l basis) ≠ 1 := by
  have hge := galoisLTorsionKernelField_finrank_ge_of_imageContainsSL2 X l basis hSL2
  have h25 : 25 ≤ l.value * l.value := by
    calc 25 = 5 * 5 := by norm_num
      _ ≤ l.value * l.value := Nat.mul_le_mul l.ge_five l.ge_five
  have h24 : 24 ≤ l.value ^ 2 - 1 := by
    rw [pow_two]
    omega
  have h120 : 120 ≤ l.value * (l.value ^ 2 - 1) := by
    calc 120 = 5 * 24 := by norm_num
      _ ≤ l.value * (l.value ^ 2 - 1) := Nat.mul_le_mul l.ge_five h24
  omega

/-- The kernel field is not the base field: ImageContainsSL2 forces K != F. -/
theorem galoisLTorsionKernelField_ne_bot_of_imageContainsSL2
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    X.galoisLTorsionKernelField l basis ≠ ⊥ := by
  intro hbot
  have h1 : Module.finrank F (X.galoisLTorsionKernelField l basis) = 1 := by
    rw [hbot]
    exact IntermediateField.finrank_bot
  exact galoisLTorsionKernelField_finrank_ne_one_of_imageContainsSL2 X l basis hSL2 h1

/-- Name used by the S1543/S1544 donor interface. -/
theorem kernelField_ne_bot_of_imageContainsSL2
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    X.galoisLTorsionKernelField l basis ≠ ⊥ :=
  galoisLTorsionKernelField_ne_bot_of_imageContainsSL2 X l basis hSL2

/-- At l = 5 the general bound reads [K : F] >= 120. -/
theorem galoisLTorsionKernelField_finrank_ge_120_of_imageContainsSL2
    (h5 : l.value = 5)
    (hSL2 : LTorsionImageContainsSL2 X l basis) :
    120 ≤ Module.finrank F (X.galoisLTorsionKernelField l basis) := by
  have h := galoisLTorsionKernelField_finrank_ge_of_imageContainsSL2 X l basis hSL2
  rw [h5] at h
  norm_num at h ⊢
  exact h

end PuncturedEllipticCurve

end LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S1558KernelFieldDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1543CorrectedGaussianArithmeticActual
open LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual

variable {l : PrimeGeFive}

/-- Bridge from the S1544/S1545 subgroup-map form of the large-image
hypothesis to the existential form used in this file. -/
theorem imageContainsSL2_of_map_top_le_range
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    PuncturedEllipticCurve.LTorsionImageContainsSL2
      (GaussianCurve (l := l)) l b :=
  PuncturedEllipticCurve.lTorsionImageContainsSL2_of_map_top_le_range
    (l := l) (X := GaussianCurve (l := l)) (basis := b) hlarge

/-- Donor for the actual Gaussian kernel field: the degree is at least
l(l^2-1) whenever the mod-l image contains SL2. -/
theorem gaussianKernelField_finrank_ge_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    l.value * (l.value ^ 2 - 1) ≤
      Module.finrank (S1280Arithmetic l).F (gaussianKernelField (l := l) b) := by
  exact PuncturedEllipticCurve.galoisLTorsionKernelField_finrank_ge_of_imageContainsSL2
    (l := l) (X := GaussianCurve (l := l)) (basis := b)
    (imageContainsSL2_of_map_top_le_range (l := l) b hlarge)

/-- Donor at l = 5: the actual Gaussian kernel field has degree at least 120
over F whenever the mod-l image contains SL2. -/
theorem gaussianKernelField_finrank_ge_120_of_imageContainsSL2
    (b : GaussianTorsionBasis l) (h5 : l.value = 5)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    120 ≤ Module.finrank (S1280Arithmetic l).F (gaussianKernelField (l := l) b) := by
  exact PuncturedEllipticCurve.galoisLTorsionKernelField_finrank_ge_120_of_imageContainsSL2
    (l := l) (X := GaussianCurve (l := l)) (basis := b) h5
    (imageContainsSL2_of_map_top_le_range (l := l) b hlarge)

/-- The Gaussian kernel field is nontrivial under the large-image hypothesis. -/
theorem gaussianKernelField_ne_bot_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    gaussianKernelField (l := l) b ≠ ⊥ := by
  exact PuncturedEllipticCurve.galoisLTorsionKernelField_ne_bot_of_imageContainsSL2
    (l := l) (X := GaussianCurve (l := l)) (basis := b)
    (imageContainsSL2_of_map_top_le_range (l := l) b hlarge)

/-- The Gaussian kernel field has extension degree not equal to one under the
large-image hypothesis. -/
theorem gaussianKernelField_finrank_ne_one_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    Module.finrank (S1280Arithmetic l).F (gaussianKernelField (l := l) b) ≠ 1 := by
  exact PuncturedEllipticCurve.galoisLTorsionKernelField_finrank_ne_one_of_imageContainsSL2
    (l := l) (X := GaussianCurve (l := l)) (basis := b)
    (imageContainsSL2_of_map_top_le_range (l := l) b hlarge)

/-- Donor for S1543 corrected K: the actual Gaussian kernel field, with the
actual finite/Galois/number-field instances, fills S1543CorrectedK once the
mod-l image contains SL2. -/
noncomputable def s1543CorrectedK_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    S1543CorrectedK l where
  K := gaussianKernelField (l := l) b
  numberFieldK := NumberField.of_module_finite (S1280Arithmetic l).F
    (gaussianKernelField (l := l) b)
  nontrivial := gaussianKernelField_finrank_ne_one_of_imageContainsSL2 (l := l) b hlarge

end LeanFormal.IUT.XiFPaper.S1558KernelFieldDegreeActual
