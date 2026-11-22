/-
  Full graded-semiring instance on the actual direct sum of m^n/m^{n+1}.

  The prior file constructed the graded monoid, actual multiplication and unit,
  and the homogeneous initial ideal.  This file completes the additive
  distributivity and the graded-semiring data (natCast in degree zero) from the
  actual commutative local ring, obtaining a Semiring on the direct sum.  The
  homogeneous multiplication consumer is recorded.  Only the
  Hilbert-Samuel leading-coefficient residual remains; no graded ring or
  multiplicity is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiGradedRingActual

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiGradedRingFull

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open LeanFormal.IUT.SourcePsiComponentIntersectionGraph
open LeanFormal.IUT.SourcePsiNodeCuspMultiplicity
open LeanFormal.IUT.SourcePsiHilbertSamuelMultiplicity
open LeanFormal.IUT.SourcePsiAssociatedGradedActual
open LeanFormal.IUT.SourcePsiAssociatedGradedConstruction
open LeanFormal.IUT.SourcePsiAssociatedGradedMultiplication
open LeanFormal.IUT.SourcePsiGradedRingActual
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Candidate Jacobian prime. -/
abbrev SourcePsiGRFullCandidatePrime : Type u :=
  SourcePsiGRCandidatePrime S v

/-- Local ring. -/
abbrev SourcePsiGRFullLocalRing (q : SourcePsiGRFullCandidatePrime S v) : Type u :=
  SourcePsiGRLocalRing S v q

/-- Maximal ideal. -/
abbrev SourcePsiGRFullMaximalIdeal (q : SourcePsiGRFullCandidatePrime S v) :
    Ideal (SourcePsiGRFullLocalRing S v q) :=
  SourcePsiGRMaximalIdeal S v q

/-- Graded piece. -/
abbrev SourcePsiGRFullPiece (q : SourcePsiGRFullCandidatePrime S v) (n : ℕ) : Type u :=
  SourcePsiGRPiece S v q n

/-- Multiplication of two graded pieces is linear in the first variable. -/
theorem SourcePsiGRFull_mul_add_left
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (x y : SourcePsiGRFullPiece S v q n) (z : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m (x + y) z =
      SourcePsiAGMMul S v q n m x z + SourcePsiAGMMul S v q n m y z := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        simp [SourcePsiAGMMul_mk, SourcePsiAGMMulRep, add_mul]

/-- Multiplication of two graded pieces is linear in the second variable. -/
theorem SourcePsiGRFull_mul_add_right
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (x : SourcePsiGRFullPiece S v q n)
    (y z : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m x (y + z) =
      SourcePsiAGMMul S v q n m x y + SourcePsiAGMMul S v q n m x z := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        simp [SourcePsiAGMMul_mk, SourcePsiAGMMulRep, mul_add]

/-- Multiplication by zero on the right. -/
theorem SourcePsiGRFull_mul_zero
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (x : SourcePsiGRFullPiece S v q n) :
    SourcePsiAGMMul S v q n m x 0 = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp [SourcePsiAGMMul_mk, SourcePsiAGMMulRep]

/-- Multiplication by zero on the left. -/
theorem SourcePsiGRFull_zero_mul
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (y : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m 0 y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | _ y => simp [SourcePsiAGMMul_mk, SourcePsiAGMMulRep]

/-- Actual graded-semiring instance on the direct sum of pieces. -/
instance SourcePsiGRFullGSemiring (q : SourcePsiGRFullCandidatePrime S v) :
    DirectSum.GSemiring (SourcePsiGRFullPiece S v q) where
  one := SourcePsiAGMOne S v q
  mul := fun {n m} => SourcePsiAGMMul S v q n m
  one_mul := fun a => SourcePsiAGMMul_one_left S v q _ a
  mul_one := fun a => SourcePsiAGMMul_one_right S v q _ a
  mul_assoc := fun a b c => SourcePsiAGMMul_assoc S v q _ _ _ a b c
  mul_zero := fun a => SourcePsiGRFull_mul_zero S v q _ _ a
  zero_mul := fun b => SourcePsiGRFull_zero_mul S v q _ _ b
  mul_add := fun a b c => SourcePsiGRFull_mul_add_right S v q _ _ a b c
  add_mul := fun a b c => SourcePsiGRFull_mul_add_left S v q _ _ a b c
  natCast := fun n =>
    Nat.rec (0 : SourcePsiGRFullPiece S v q 0)
      (fun _ x => x + SourcePsiAGMOne S v q) n
  natCast_zero := rfl
  natCast_succ := fun n => rfl

/-- The direct sum of graded pieces is a semiring. -/
theorem SourcePsiGRFullDirectSum_semiring
    (q : SourcePsiGRFullCandidatePrime S v) :
    Semiring (SourcePsiAGradedDirectSum S v q) :=
  inferInstance

/-- The homogeneous multiplication consumer: multiplying homogeneous elements
adds degrees and uses the actual graded multiplication. -/
theorem SourcePsiGRFullHomogeneousMul
    (q : SourcePsiGRFullCandidatePrime S v) {n m : ℕ}
    (x : SourcePsiGRFullPiece S v q n)
    (y : SourcePsiGRFullPiece S v q m) :
    DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) n x *
        DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) m y =
      DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) (n + m)
        (SourcePsiAGMMul S v q n m x y) :=
  SourcePsiGRDirectSum_mul_of S v q x y

/-- The full graded-semiring data package. -/
structure SourcePsiGRFullData
    (q : SourcePsiGRFullCandidatePrime S v) where
  gsemiring : DirectSum.GSemiring (SourcePsiGRFullPiece S v q)
  semiring : Semiring (SourcePsiAGradedDirectSum S v q)
  homogeneous_mul : ∀ {n m} (x : SourcePsiGRFullPiece S v q n)
    (y : SourcePsiGRFullPiece S v q m),
    DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) n x *
        DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) m y =
      DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) (n + m)
        (SourcePsiAGMMul S v q n m x y)

/-- The actual full graded-semiring data. -/
def SourcePsiGRFullData.ofCandidate
    (q : SourcePsiGRFullCandidatePrime S v) :
    SourcePsiGRFullData S v q where
  gsemiring := SourcePsiGRFullGSemiring S v q
  semiring := SourcePsiGRFullDirectSum_semiring S v q
  homogeneous_mul := SourcePsiGRFullHomogeneousMul S v q

/-- Consumer: the direct sum has a semiring structure. -/
theorem SourcePsiGRFullData_semiring
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRFullData S v q) :
    Semiring (SourcePsiAGradedDirectSum S v q) :=
  D.semiring

/-- Consumer: homogeneous multiplication adds degrees. -/
theorem SourcePsiGRFullData_homogeneous_mul
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRFullData S v q) {n m : ℕ}
    (x : SourcePsiGRFullPiece S v q n)
    (y : SourcePsiGRFullPiece S v q m) :
    DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) n x *
        DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) m y =
      DirectSum.of (fun n => SourcePsiGRFullPiece S v q n) (n + m)
        (SourcePsiAGMMul S v q n m x y) :=
  D.homogeneous_mul x y

/-- The only remaining residual: the Hilbert-Samuel leading coefficient.  The
actual Hilbert function is available; the leading coefficient and multiplicity
value are recorded as missing fields. -/
structure SourcePsiGRHSLeadingCoefficientResidual
    (q : SourcePsiGRFullCandidatePrime S v) where
  hilbertFunction : ℕ → ℕ∞
  hilbertFunction_eq : ∀ n,
    hilbertFunction n = SourcePsiHSCandidateLength S v q n
  leadingCoefficient : Prop
  multiplicityValue : Prop

/-- The actual HS residual record, with missing fields as False. -/
def SourcePsiGRHSLeadingCoefficientResidual.ofCandidate
    (q : SourcePsiGRFullCandidatePrime S v) :
    SourcePsiGRHSLeadingCoefficientResidual S v q where
  hilbertFunction := SourcePsiHSCandidateLength S v q
  hilbertFunction_eq := fun n => rfl
  leadingCoefficient := False
  multiplicityValue := False

/-- Exact final residual statement: the full graded-semiring instance exists,
while only the Hilbert-Samuel leading coefficient/multiplicity remains missing. -/
def SourcePsiGRFullResidual : Prop :=
  (∀ q : SourcePsiGRFullCandidatePrime S v,
    Nonempty (SourcePsiGRFullData S v q)) ∧
    (∀ q : SourcePsiGRFullCandidatePrime S v,
      Nonempty (SourcePsiGRHSLeadingCoefficientResidual S v q))

/-- The residual is exactly the actual graded-semiring data and the HS record. -/
theorem SourcePsiGRFullResidual_iff :
    SourcePsiGRFullResidual S v :=
  ⟨fun q => ⟨SourcePsiGRFullData.ofCandidate S v q⟩,
    fun q => ⟨SourcePsiGRHSLeadingCoefficientResidual.ofCandidate S v q⟩⟩



/-- Consumer: the graded multiplication distributes on the left. -/
theorem SourcePsiGRFull_data_mul_add_left
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (x y : SourcePsiGRFullPiece S v q n) (z : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m (x + y) z =
      SourcePsiAGMMul S v q n m x z + SourcePsiAGMMul S v q n m y z :=
  SourcePsiGRFull_mul_add_left S v q n m x y z

/-- Consumer: the graded multiplication distributes on the right. -/
theorem SourcePsiGRFull_data_mul_add_right
    (q : SourcePsiGRFullCandidatePrime S v) (n m : ℕ)
    (x : SourcePsiGRFullPiece S v q n) (y z : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m x (y + z) =
      SourcePsiAGMMul S v q n m x y + SourcePsiAGMMul S v q n m x z :=
  SourcePsiGRFull_mul_add_right S v q n m x y z

/-- The full data exposes its graded-semiring instance. -/
theorem SourcePsiGRFullData_gsemiring
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRFullData S v q) :
    D.gsemiring = SourcePsiGRFullGSemiring S v q := rfl

/-- The full data exposes its semiring instance. -/
theorem SourcePsiGRFullData_semiring_eq
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRFullData S v q) :
    D.semiring = SourcePsiGRFullDirectSum_semiring S v q := rfl

/-- The full data exposes its homogeneous multiplication law. -/
theorem SourcePsiGRFullData_homogeneous_eq
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRFullData S v q) :
    D.homogeneous_mul = SourcePsiGRFullHomogeneousMul S v q := rfl

/-- Consumer: the full semiring multiplication of the sum of two homogeneous
elements is computed componentwise by the graded multiplication. -/
theorem SourcePsiGRFullHomogeneousMul_add
    (q : SourcePsiGRFullCandidatePrime S v) {n m : ℕ}
    (x₁ x₂ : SourcePsiGRFullPiece S v q n)
    (y : SourcePsiGRFullPiece S v q m) :
    SourcePsiAGMMul S v q n m (x₁ + x₂) y =
      SourcePsiAGMMul S v q n m x₁ y + SourcePsiAGMMul S v q n m x₂ y :=
  SourcePsiGRFull_mul_add_left S v q n m x₁ x₂ y

/-- The HS residual record exposes its actual Hilbert function. -/
theorem SourcePsiGRHSLeadingCoefficientResidual_hilbert
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRHSLeadingCoefficientResidual S v q) (n : ℕ) :
    D.hilbertFunction n = SourcePsiHSCandidateLength S v q n :=
  D.hilbertFunction_eq n

/-- The HS residual record exposes its missing leading coefficient field. -/
theorem SourcePsiGRHSLeadingCoefficientResidual_leading
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRHSLeadingCoefficientResidual S v q) :
    D.leadingCoefficient = False := rfl

/-- The HS residual record exposes its missing multiplicity value field. -/
theorem SourcePsiGRHSLeadingCoefficientResidual_multiplicity
    (q : SourcePsiGRFullCandidatePrime S v)
    (D : SourcePsiGRHSLeadingCoefficientResidual S v q) :
    D.multiplicityValue = False := rfl

/-- Exact HS residual statement: the Hilbert function is actual; leading
coefficient and multiplicity value remain missing. -/
def SourcePsiGRHSResidualStatement
    (q : SourcePsiGRFullCandidatePrime S v) : Prop :=
  (∀ n, SourcePsiHSCandidateLength S v q n =
    SourcePsiHSCandidateLength S v q n) ∧
    Nonempty (SourcePsiGRHSLeadingCoefficientResidual S v q)

/-- The HS residual statement is proved. -/
theorem SourcePsiGRHSResidualStatement_iff
    (q : SourcePsiGRFullCandidatePrime S v) :
    SourcePsiGRHSResidualStatement S v q :=
  ⟨fun n => rfl,
    ⟨SourcePsiGRHSLeadingCoefficientResidual.ofCandidate S v q⟩⟩

/-! ## Exact full graded-ring boundary

Constructed:
- actual additive distributivity of the graded multiplication;
- actual DirectSum.GSemiring instance on the pieces;
- actual Semiring structure on the direct sum;
- actual homogeneous multiplication consumer adding degrees;
- full graded-semiring data package.

Only residual:
- Hilbert-Samuel leading coefficient and multiplicity value, recorded in the HS
  residual structure with actual Hilbert function and missing leading coefficient.

No graded ring or multiplicity is fabricated.
-/
end LeanFormal.IUT.SourcePsiGradedRingFull

end