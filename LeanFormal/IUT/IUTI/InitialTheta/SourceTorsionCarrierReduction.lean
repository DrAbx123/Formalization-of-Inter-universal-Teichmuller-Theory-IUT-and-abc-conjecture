/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import Mathlib.Tactic

/-!
# D5 reduction: torsion carrier, Galois representation, and large image

IUT I, Definition 3.1(c) fixes the mod-`l` torsion data of the initial
Theta-datum: the image of `G_F -> GL_2(F_l)` determined by the `l`-torsion
points of `E_F` contains `SL_2(F_l)`, and `K` is the finite Galois extension
of `F` determined by the kernel of this homomorphism.  The obligation
`IUT-I.definition-3.1-D5` records the corresponding construction gap.

This file freezes that clause at the level of `InitialThetaArithmeticData`
and reduces it to named source data:

* `SourceTorsionDatum` is the frozen D5 shape: the actual `ZMod l`-module
  `E_F[l]` is presented by a chosen basis, the large-image condition is the
  literal subgroup containment of the paper, and `K` is identified with the
  kernel field of the canonical representation.
* The containment of `SL_2(F_l)` in the image is *not* proved here: the
  clause fixes it as part of the source data.  `SerreStyleLargeImageStatement`
  records the precise unproved statement; `RankTwoTorsionBasisGap` records
  the rank-two basis gap and is reduced to finite-dimensionality plus
  `finrank = 2` of the torsion carrier.
* `largeImageSL2_iff_forall` shows that the literal subgroup containment
  and the "every `SL_2` element is hit" shape used by the vendored
  shape-reference ledger are the same condition.
* `algEquiv_range_coe_eq_intermediateField` proves that the range condition
  `kernel_field_identification_range` demanded by `SourceClauseC` is
  *forced* by the identification `A.K ~= kernelField`; the conditional
  assembly `SourceTorsionDatum.toSourceClauseC` therefore consumes one
  hypothesis fewer than the raw constructor
  `SourceClauseC.ofCanonicalRepresentation`.

The two gap statements are plain `Prop`-valued definitions; they are never
asserted, and the only theorems that mention them are implications between
those statements.  No placeholder is introduced and the file adds no extra
proof assumption beyond the three standard kernel axioms.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

namespace TorsionCarrierReduction

/-! ## The large-image condition in its two shapes -/

/-- The large-image condition of IUT I, Definition 3.1(c) in the
"every `SL_2` element is the image of some Galois element" shape used by the
vendored shape-reference ledger (`ImageContainsSL2`). -/
def LargeImageContainsSL2 {l : PrimeGeFive} {G : Type*} [Group G]
    (representation : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) : Prop :=
  ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
    ∃ sigma : G, representation sigma = Matrix.SpecialLinearGroup.toGL g

/-- The literal containment shape `SL_2(F_l) <= im(rho)` of the paper and
the "every element is hit" shape are the same condition. -/
theorem largeImageSL2_iff_forall {l : PrimeGeFive} {G : Type*} [Group G]
    (representation : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      representation.range ↔
    LargeImageContainsSL2 representation := by
  constructor
  · intro h g
    have hg : Matrix.SpecialLinearGroup.toGL g ∈
        Subgroup.map Matrix.SpecialLinearGroup.toGL
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) :=
      Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩
    exact MonoidHom.mem_range.mp (h hg)
  · intro h x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨g, -, rfl⟩ := hx
    exact MonoidHom.mem_range.mpr (h g)

/-! ## General reductions -/

/-- An algebra equivalence onto an intermediate field has exactly that
intermediate field as the range of its underlying coercion.  This is the
step that makes the explicit range condition of `SourceClauseC` redundant
once the identification of `A.K` with the kernel field is supplied. -/
theorem algEquiv_range_coe_eq_intermediateField {F L : Type u} [Field F]
    [Field L] [Algebra F L] {k : Type u} [Field k] [Algebra F k]
    (K' : IntermediateField F L) (phi : k ≃ₐ[F] K') :
    Set.range (fun x : k => (phi x : L)) = (K' : Set L) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (phi x).property
  · intro hy
    exact ⟨phi.symm ⟨y, hy⟩,
      congrArg Subtype.val (phi.apply_symm_apply ⟨y, hy⟩)⟩

/-! ## Carrier facts for the actual `l`-torsion subgroup -/

/-- The D5 carrier is genuine `l`-torsion: every element of `E_F[l]` is
killed by `l`. -/
theorem lTorsion_nsmul_eq_zero {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (P : X.LTorsion l) : l.value • P = 0 :=
  AddSubgroup.torsionBy.nsmul P

/-- Membership in the carrier is exactly being killed by `l`.  Together
with the `ZMod l`-module instance of `PuncturedEllipticCurve.lTorsionModule`
this is the torsion-module structure of the D5 carrier. -/
theorem mem_lTorsion_iff {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (P : X.AlgebraicClosurePoint) : P ∈ X.LTorsion l ↔ l.value • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

/-! ## The frozen D5 shape -/

/-- The frozen clause-(c) data for one `InitialThetaArithmeticData`.

* `torsion_basis` presents the actual carrier `E_F[l]` as a rank-two
  `ZMod l`-module; its existence is the open `RankTwoTorsionBasisGap`.
* `image_contains_SL2` is the literal containment of Definition 3.1(c);
  it is a hypothesis on the source data, not a theorem about arbitrary
  arithmetic data (`SerreStyleLargeImageStatement`).
* `kernel_field_identification` states that `K` is the kernel field of the
  canonical representation; it forces the range condition required by
  `SourceClauseC` (`kernelField_identification_range`). -/
structure SourceTorsionDatum (l : PrimeGeFive)
    (A : InitialThetaArithmeticData.{u} l) where
  torsion_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l
  image_contains_SL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (A.curve.galoisLTorsionMatrixRepresentation l torsion_basis).range
  kernel_field_identification :
    A.K ≃ₐ[A.F] A.curve.galoisLTorsionKernelField l torsion_basis

namespace SourceTorsionDatum

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}

/-- The clause-(c) outer homomorphism, fixed to the canonical matrix
representation of the supplied torsion basis. -/
noncomputable def representation (D : SourceTorsionDatum l A) :
    SourceAbsoluteGalois A →* Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis

theorem representation_eq_canonical (D : SourceTorsionDatum l A) :
    D.representation =
      A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis :=
  rfl

/-- The clause's statement that `K` is determined by the kernel of the
outer homomorphism: the fixing subgroup of the kernel field is exactly the
kernel of the frozen representation. -/
theorem kernelField_fixingSubgroup (D : SourceTorsionDatum l A) :
    (A.curve.galoisLTorsionKernelField l D.torsion_basis).fixingSubgroup =
      D.representation.ker := by
  simpa [representation,
    PuncturedEllipticCurve.galoisLTorsionKernelSubgroup] using
    A.curve.galoisLTorsionKernelField_fixingSubgroup l D.torsion_basis

/-- The range condition of `SourceClauseC` is forced by the identification
of `A.K` with the kernel field; it is not independent input. -/
theorem kernelField_identification_range (D : SourceTorsionDatum l A) :
    Set.range (fun x : A.K =>
        (D.kernel_field_identification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l D.torsion_basis :
        Set (AlgebraicClosure A.F)) :=
  algEquiv_range_coe_eq_intermediateField _ D.kernel_field_identification

/-- The literal containment in the "every `SL_2` element is hit" shape. -/
theorem image_contains_SL2_forall (D : SourceTorsionDatum l A) :
    LargeImageContainsSL2 D.representation :=
  (largeImageSL2_iff_forall D.representation).mp
    (by simpa [representation] using D.image_contains_SL2)

variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-- Conditional assembly: the frozen D5 data plus clause-(b) rationality
produces the literal clause-(c) record.  The explicit range condition of
`SourceClauseC` is discharged by `kernelField_identification_range`. -/
noncomputable def toSourceClauseC
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    SourceClauseC A S C B :=
  SourceClauseC.ofCanonicalRepresentation (S := S) (C := C) (B := B)
    torsion23Rational D.torsion_basis D.image_contains_SL2
    D.kernel_field_identification D.kernelField_identification_range

@[simp] theorem toSourceClauseC_torsion_basis
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    (toSourceClauseC (S := S) (C := C) (B := B) D torsion23Rational).torsion_basis =
      D.torsion_basis :=
  rfl

@[simp] theorem toSourceClauseC_representation
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    (toSourceClauseC (S := S) (C := C) (B := B) D torsion23Rational).representation =
      D.representation :=
  rfl

/-- Recognition: every literal clause-(c) record already determines a
frozen D5 datum. -/
noncomputable def ofSourceClauseC (D : SourceClauseC A S C B) :
    SourceTorsionDatum l A where
  torsion_basis := D.torsion_basis
  image_contains_SL2 := by
    rw [← D.representation_eq_canonical]
    exact D.image_contains_SL2
  kernel_field_identification := D.kernel_field_identification

end SourceTorsionDatum

/-! ## The frozen universal target -/

/-- The frozen D5 target in the same quantifier shape as the D9/D10 goals
of `SourceDefinition31RootLemmas`: for every arithmetic datum and prime
label, the clause-(c) data exist.  The paper does not prove this for
arbitrary arithmetic data either: clause (c) is part of the description of
an initial Theta-datum that is *fixed satisfying* (a)-(f), so its
large-image component is a source-satisfaction hypothesis rather than a
theorem (`SerreStyleLargeImageStatement`). -/
def Definition31D5Target (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l, Nonempty (SourceTorsionDatum l A)

/-- Conditional reduction of the frozen D5 target: the D5 datum plus the
clause-(b) six-torsion rationality component supply every field of the
literal clause-(c) record. -/
theorem sourceClauseC_nonempty_of_d5Target_and_torsion23
    (hD5 : Definition31D5Target.{u} l)
    (torsion23Rational : ∀ A : InitialThetaArithmeticData.{u} l,
      PuncturedEllipticCurve.Torsion23Rational A.curve) :
    ∀ (A : InitialThetaArithmeticData.{u} l)
      (S : SourceSignQuotientData A) (C : SourceClauseA A S)
      (B : SourceClauseB A S C), Nonempty (SourceClauseC A S C B) := by
  intro A S C B
  obtain ⟨D⟩ := hD5 A
  exact ⟨D.toSourceClauseC (S := S) (C := C) (B := B) (torsion23Rational A)⟩

/-! ## Exact cards for the two still-open sub-propositions -/

/-- CARD (D5-gap-rank-two, unproved).  Existence of the rank-two torsion
basis `(ZMod l)^2 ~= E_F[l]`.

`rankTwoTorsionBasisGap_iff_finrank_eq_two` shows that, given
`Module.Finite (ZMod l) E_F[l]`, this is exactly
`Module.finrank (ZMod l) E_F[l] = 2`.  Neither the finiteness nor the
finrank value is available in Mathlib for `E[l]` over an algebraic closure
(audit obligation `Foundations.Geometry.elliptic-l-torsion-rank-two`
records the same gap); the division-polynomial bridges of
`ABCBridge.Galois.EllipticTorsionAlgebraicity` prove integrality of
coordinates, not module rank. -/
def RankTwoTorsionBasisGap {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive) : Prop :=
  Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)

/-- Exact reduction of the rank-two basis gap to finite-dimensionality and
finrank two of the torsion carrier. -/
theorem rankTwoTorsionBasisGap_iff_finrank_eq_two {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    [Module.Finite (ZMod l.value) (X.LTorsion l)] :
    RankTwoTorsionBasisGap X l ↔
      Module.finrank (ZMod l.value) (X.LTorsion l) = 2 := by
  haveI : Fact (Nat.Prime l.value) := PrimeGeFive.factPrime l
  rw [RankTwoTorsionBasisGap,
    FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq,
    Module.finrank_fin_fun]
  exact eq_comm

/-- The constructive direction of the rank-two reduction. -/
theorem rankTwoBasis_of_finrank_eq_two {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    [Module.Finite (ZMod l.value) (X.LTorsion l)]
    (h : Module.finrank (ZMod l.value) (X.LTorsion l) = 2) :
    RankTwoTorsionBasisGap X l :=
  (rankTwoTorsionBasisGap_iff_finrank_eq_two X l).mpr h

/-- CARD (D5-gap-large-image, unproved).  The Serre-style large-image
statement: for the arithmetic curve there is a torsion basis whose
canonical representation contains `SL_2(F_l)`.

This is exactly the open `image_contains_SL2` input of
`SourceTorsionDatum`.  It is not derivable from `InitialThetaArithmeticData`
alone: curves with small mod-`l` image (complex multiplication, rational
`l`-isogenies) violate it, and the paper supplies it by *fixing* initial
Theta-data satisfying (a)-(f).  No version is available in Mathlib (audit
obligation `IUT-I.elliptic-l-torsion-large-image` records the same gap);
the three blocked Mathlib routes to the odd-`n` division-polynomial bridge
are documented in the header of
`ABCBridge.Galois.EllipticTorsionAlgebraicity`. -/
def SerreStyleLargeImageStatement {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive) : Prop :=
  ∃ basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l,
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (X.galoisLTorsionMatrixRepresentation l basis).range

/-- The large-image card presupposes the rank-two card: any witness of
`SerreStyleLargeImageStatement` already supplies a rank-two basis. -/
theorem rankTwoTorsionBasisGap_of_serreStyleLargeImage {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive)
    (h : SerreStyleLargeImageStatement X l) : RankTwoTorsionBasisGap X l :=
  ⟨h.choose⟩

end TorsionCarrierReduction

end InitialThetaSource

end

end LeanFormal.IUT
