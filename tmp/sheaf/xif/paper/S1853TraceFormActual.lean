import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual
import tmp.sheaf.xif.paper.S1853FieldCaseActual
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open scoped Matrix
open LinearMap
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual

namespace LeanFormal.IUT.XiFPaper.S1853TraceFormActual

/-!
# S1853: trace-form perfectness for finite etale algebras over R'

This file proves the two local ingredients of trace-form perfectness for finite etale
R'-algebras:

* **field case** (in S1853FieldCaseActual): for a field k and a finite etale
  k-algebra A, the trace form (x,y) |-> Tr(x y) is nondegenerate;
* **local case** (this file): for a local ring R and a finite etale R-algebra A,
  the trace form is nondegenerate.

The local case is proved by reducing modulo the maximal ideal.  The trace matrix of
A with respect to an R-basis is the reduction of the trace matrix of the residue
algebra A / mA (Mathlib's Algebra.trace_quotient_mk and
IsLocalRing.basisQuotient).  The residue algebra is finite etale over the residue
field, so by the field case its trace matrix has nonzero determinant.  Hence the
determinant of the original trace matrix is not in the maximal ideal, i.e. it is a
unit in the local ring, and the trace form is nondegenerate.

The remaining global step is isolated as the proposition S1853GlobalTracePerfect:
passing from perfectness at every local ring (proved here) to perfectness over R'.
This requires the localisation compatibility of the trace form for finite projective
algebras (equivalently a finite free cover of Spec R' together with
Algebra.trace_localization on the free pieces), which is not available in
Mathlib 4.32.2 in the form needed.  No sorry, admit, or new axiom is used in this
file; S1853GlobalTracePerfect is a plain Prop with no inhabitant, and the only
consequences drawn from it are explicit hypotheses of conditional theorems.
-/

/-! ## 1. Matrix criterion for nondegeneracy over a local ring -/

/-- If the determinant of the matrix of a bilinear form is a unit, then the form is
nondegenerate.  This is the matrix form of the fact that an invertible matrix over a
commutative ring gives a perfect pairing. -/
lemma Matrix.toBilin'_nondegenerate_of_isUnit_det
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : IsUnit M.det) :
    (Matrix.toBilin' M).Nondegenerate := by
  constructor
  · intro x hx
    have hmul : Mᵀ *ᵥ x = 0 := by
      ext j
      have h := hx (Pi.single j 1)
      rw [Matrix.toBilin'_apply', Matrix.mulVec_single_one] at h
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm, mul_left_comm,
        mul_assoc] using h
    calc x = (1 : Matrix ι ι R) *ᵥ x := by simp
      _ = ((M⁻¹)ᵀ * Mᵀ) *ᵥ x := by
        rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv M h]
        simp
      _ = (M⁻¹)ᵀ *ᵥ (Mᵀ *ᵥ x) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  · intro y hy
    have hmul : M *ᵥ y = 0 := by
      ext i
      have h := hy (Pi.single i 1)
      rw [Matrix.toBilin'_apply', single_one_dotProduct] at h
      simpa using h
    calc y = (1 : Matrix ι ι R) *ᵥ y := by simp
      _ = (M⁻¹ * M) *ᵥ y := by
        rw [Matrix.nonsing_inv_mul M h]
      _ = M⁻¹ *ᵥ (M *ᵥ y) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]

/-- If the matrix of a bilinear form with respect to a basis has unit determinant, the
form is nondegenerate. -/
lemma nondegenerate_of_isUnit_det
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M)
    (B : LinearMap.BilinForm R M) (h : IsUnit ((LinearMap.BilinForm.toMatrix b) B).det) :
    B.Nondegenerate := by
  have h' : (Matrix.toBilin' ((LinearMap.BilinForm.toMatrix b) B)).Nondegenerate :=
    Matrix.toBilin'_nondegenerate_of_isUnit_det _ h
  have hcongr : (LinearMap.BilinForm.congr b.equivFun) B =
      Matrix.toBilin' ((LinearMap.BilinForm.toMatrix b) B) := by
    apply LinearMap.BilinForm.ext
    intro x y
    rw [LinearMap.BilinForm.congr_apply]
    rw [Matrix.toBilin'_apply']
    exact (LinearMap.BilinForm.dotProduct_toMatrix_mulVec (b := b) (B := B) (x := x) (y := y)).symm
  rw [← hcongr] at h'
  exact (LinearMap.BilinForm.nondegenerate_congr_iff b.equivFun).mp h'

/-! ## 2. The trace matrix modulo the maximal ideal -/

section LocalRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing R]
  [Module.Free R A] [Module.Finite R A] [Algebra.Etale R A]

local notation "p" => IsLocalRing.maximalIdeal R
local notation "pA" => Ideal.map (algebraMap R A) p

/-- The trace matrix of the residue algebra is the reduction of the trace matrix of
A.  This is the matrix form of Algebra.trace_quotient_mk. -/
lemma traceMatrix_quotient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R A) :
    Algebra.traceMatrix (R ⧸ p) (IsLocalRing.basisQuotient b) =
      (Ideal.Quotient.mk p).mapMatrix (Algebra.traceMatrix R b) := by
  classical
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Algebra.traceMatrix_apply, Algebra.traceMatrix_apply]
  rw [IsLocalRing.basisQuotient_apply, IsLocalRing.basisQuotient_apply]
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  rw [← map_mul]
  rw [Algebra.trace_quotient_mk]

/-- The residue algebra A / mA is finite etale over the residue field. -/
theorem etale_residueAlgebra :
    Algebra.Etale (R ⧸ p) (A ⧸ pA) := by
  let e : (A ⧸ pA) ≃ₐ[(R ⧸ p)] ((R ⧸ p) ⊗[R] A) :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor A p
  exact Algebra.Etale.of_equiv e.symm

/-- The trace form of the residue algebra is nondegenerate (field case). -/
theorem traceForm_residue_nondegenerate :
    (Algebra.traceForm (R ⧸ p) (A ⧸ pA)).Nondegenerate := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Algebra.Etale (R ⧸ p) (A ⧸ pA) := etale_residueAlgebra
  exact @LeanFormal.IUT.XiFPaper.S1853FieldCaseActual.traceForm_nondegenerate_of_field
    (R ⧸ p) (A ⧸ pA) (Ideal.Quotient.field p) inferInstance inferInstance inferInstance

/-- **Local trace-form perfectness.**  For a finite etale algebra over a local ring,
the trace form is nondegenerate. -/
theorem traceForm_nondegenerate_of_isLocalRing :
    (Algebra.traceForm R A).Nondegenerate := by
  classical
  letI : Module.Flat R A := inferInstance
  letI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Module.Free.ChooseBasisIndex R A) R A := Module.Free.chooseBasis R A
  letI : DecidableEq (Module.Free.ChooseBasisIndex R A) := Classical.decEq _
  let k := R ⧸ p
  let Abar := A ⧸ pA
  haveI : Field k := Ideal.Quotient.field p
  letI : Algebra.Etale k Abar := etale_residueAlgebra
  have hfield : (Algebra.traceForm k Abar).Nondegenerate := traceForm_residue_nondegenerate
  have hdet : (Algebra.traceMatrix k (IsLocalRing.basisQuotient b)).det ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (IsLocalRing.basisQuotient b)).mp hfield
    simpa [Algebra.traceMatrix_of_basis] using this
  have hdet' : Ideal.Quotient.mk p ((Algebra.traceMatrix R b).det) ≠ 0 := by
    change (Algebra.traceMatrix (R ⧸ p) (IsLocalRing.basisQuotient b)).det ≠ 0 at hdet
    rw [traceMatrix_quotient b] at hdet
    simpa [RingHom.map_det] using hdet
  have hunit : IsUnit (Algebra.traceMatrix R b).det := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact fun hmem => hdet' (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hunit' : IsUnit ((LinearMap.BilinForm.toMatrix b) (Algebra.traceForm R A)).det := by
    simpa [Algebra.traceMatrix_of_basis] using hunit
  exact nondegenerate_of_isUnit_det b (Algebra.traceForm R A) hunit'

end LocalRing

/-! ## 3. The exact remaining global input -/

/-- **The exact remaining missing input.**  The trace form of every finite etale
R'-algebra is nondegenerate.  The local (local-ring) and residue-field cases are
proved above; the missing step is the local-to-global assembly for finite projective
modules (localisation compatibility of the trace form / a finite free cover of
Spec R'). -/
def S1853GlobalTracePerfect : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R),
    (Algebra.traceForm S1779R (A : Type)).Nondegenerate

/-- The same statement in the form needed by the equal-rank inclusion argument:
a finite etale R'-algebra is its own trace dual, so every linear functional on it is
represented by an element.  This is stronger than S1853GlobalTracePerfect over a
non-field base and is the precise input consumed by the trace-duality proof of
S1849EqualRankInclusion. -/
def S1853GlobalTraceDuality : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R),
    ∀ φ : (A : Type) →ₗ[S1779R] S1779R,
      ∃! a : (A : Type), ∀ b : (A : Type),
        Algebra.traceForm S1779R (A : Type) a b = φ b

/-! ## 4. From trace duality to trace perfectness -/

/-- Trace duality implies nondegeneracy: the zero functional has a unique representing
element, so an element orthogonal to everything must be zero.  The right-separating
condition follows from symmetry of the trace form. -/
theorem S1853GlobalTracePerfect_of_duality (h : S1853GlobalTraceDuality) :
    S1853GlobalTracePerfect := by
  intro A
  have hleft : ∀ x : (A : Type),
      (∀ b : (A : Type), Algebra.traceForm S1779R (A : Type) x b = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, ha, huniq⟩ := h A (0 : (A : Type) →ₗ[S1779R] S1779R)
    have hx_eq : x = a := huniq x hx
    have h0_eq : (0 : (A : Type)) = a := huniq 0 (by simp)
    rw [hx_eq, ← h0_eq]
  constructor
  · exact hleft
  · intro y hy
    apply hleft y
    intro x
    rw [← (Algebra.traceForm_isSymm (R := S1779R) (S := (A : Type))).eq x y]
    exact hy x

/-! ## 5. Formal checks -/

#check Matrix.toBilin'_nondegenerate_of_isUnit_det
#check nondegenerate_of_isUnit_det
#check traceMatrix_quotient
#check etale_residueAlgebra
#check traceForm_residue_nondegenerate
#check traceForm_nondegenerate_of_isLocalRing
#check S1853GlobalTracePerfect
#check S1853GlobalTraceDuality
#check S1853GlobalTracePerfect_of_duality

#print axioms Matrix.toBilin'_nondegenerate_of_isUnit_det
#print axioms nondegenerate_of_isUnit_det
#print axioms traceMatrix_quotient
#print axioms etale_residueAlgebra
#print axioms traceForm_residue_nondegenerate
#print axioms traceForm_nondegenerate_of_isLocalRing
#print axioms S1853GlobalTracePerfect_of_duality

end LeanFormal.IUT.XiFPaper.S1853TraceFormActual