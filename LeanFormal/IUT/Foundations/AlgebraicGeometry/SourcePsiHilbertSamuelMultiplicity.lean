/-
  Hilbert-Samuel multiplicity data at Jacobian candidate primes.

  Mathlib supplies the actual local ring A_q, its maximal ideal m_q, the quotient
  A_q / m_q^n, and the module length.  It does not supply an associated graded
  ring, initial ideal, or Hilbert-Samuel multiplicity as a function of n.  This
  file therefore constructs the actual length/Hilbert-function data and states
  the API obstruction exactly; no Hilbert-Samuel multiplicity is fabricated.

  The node/cusp geometric classification and the actual multiplicity values remain
  explicit residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiNodeCuspMultiplicity
import Mathlib.RingTheory.Length

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiHilbertSamuelMultiplicity

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open LeanFormal.IUT.SourcePsiComponentIntersectionGraph
open LeanFormal.IUT.SourcePsiNodeCuspMultiplicity
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- A Jacobian candidate prime. -/
abbrev SourcePsiHSCandidatePrime : Type u :=
  SourcePsiCandidatePrime S v

/-- The actual local ring at a candidate prime. -/
abbrev SourcePsiHSCandidateLocalRing (q : SourcePsiHSCandidatePrime S v) : Type u :=
  SourcePsiCandidateLocalRing S v q

/-- The actual maximal ideal of the candidate local ring. -/
noncomputable def SourcePsiHSCandidateMaximalIdeal
    (q : SourcePsiHSCandidatePrime S v) :
    Ideal (SourcePsiHSCandidateLocalRing S v q) :=
  IsLocalRing.maximalIdeal (SourcePsiHSCandidateLocalRing S v q)

/-- The actual n-th power of the candidate maximal ideal. -/
noncomputable def SourcePsiHSCandidateMaximalIdealPower
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    Ideal (SourcePsiHSCandidateLocalRing S v q) :=
  SourcePsiHSCandidateMaximalIdeal S v q ^ n

/-- The actual quotient A_q / m_q^n. -/
abbrev SourcePsiHSCandidateQuotient
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) : Type u :=
  SourcePsiHSCandidateLocalRing S v q ⧸
    SourcePsiHSCandidateMaximalIdealPower S v q n

/-- The actual length of A_q / m_q^n. -/
noncomputable def SourcePsiHSCandidateLength
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) : ℕ∞ :=
  Module.length (SourcePsiHSCandidateLocalRing S v q)
    (SourcePsiHSCandidateQuotient S v q n)

/-- The candidate Hilbert function n ↦ length(A_q / m_q^n). -/
noncomputable def SourcePsiHSCandidateHilbertFunction
    (q : SourcePsiHSCandidatePrime S v) : ℕ → ℕ∞ :=
  fun n => SourcePsiHSCandidateLength S v q n

/-- The candidate length is finite when the quotient is finite length. -/
theorem SourcePsiHSCandidateLength_ne_top_of_finiteLength
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ)
    [IsFiniteLength (SourcePsiHSCandidateLocalRing S v q)
      (SourcePsiHSCandidateQuotient S v q n)] :
    SourcePsiHSCandidateLength S v q n ≠ ⊤ :=
  Module.length_ne_top

/-- Conditional candidate multiplicity value: the length, as a natural number,
when the length is finite.  This is not asserted to be a Hilbert-Samuel
multiplicity. -/
noncomputable def SourcePsiHSCandidateLengthValue
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) : ℕ :=
  (SourcePsiHSCandidateLength S v q n).toNat

/-- The candidate length value is the toNat of the actual module length. -/
theorem SourcePsiHSCandidateLengthValue_eq
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    SourcePsiHSCandidateLengthValue S v q n =
      (Module.length (SourcePsiHSCandidateLocalRing S v q)
        (SourcePsiHSCandidateQuotient S v q n)).toNat :=
  rfl

/-- The actual maximal ideal is proper. -/
theorem SourcePsiHSCandidateMaximalIdeal_ne_top
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateMaximalIdeal S v q ≠ ⊤ :=
  IsLocalRing.maximalIdeal_ne_top _

/-- The quotient at exponent one is the residue field. -/
theorem SourcePsiHSCandidateQuotient_one_eq_residueField
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateQuotient S v q 1 =
      SourcePsiCandidateResidueField S v q := by
  rfl

/-- The actual quotient at exponent zero is the local ring itself. -/
theorem SourcePsiHSCandidateMaximalIdealPower_zero
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateMaximalIdealPower S v q 0 = ⊤ := by
  simp [SourcePsiHSCandidateMaximalIdealPower]

/-- The candidate Hilbert function is exactly the module-length function. -/
theorem SourcePsiHSCandidateHilbertFunction_eq
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    SourcePsiHSCandidateHilbertFunction S v q n =
      Module.length (SourcePsiHSCandidateLocalRing S v q)
        (SourcePsiHSCandidateQuotient S v q n) :=
  rfl

/-- API obstruction data: the actual length function is available, but no
associated graded ring, initial ideal, or Hilbert-Samuel multiplicity is supplied
by the present API.  This is a record of the exact missing objects, not an
inhabitant of them. -/
structure SourcePsiHilbertSamuelAPIObstruction
    (q : SourcePsiHSCandidatePrime S v) where
  lengthFunction : ℕ → ℕ∞
  lengthFunction_eq : ∀ n,
    lengthFunction n = SourcePsiHSCandidateLength S v q n
  localRing : Type u
  localRing_eq : localRing = SourcePsiHSCandidateLocalRing S v q
  associatedGradedRing : Prop
  initialIdeal : Prop
  hilbertSamuelMultiplicity : Prop
  nodeCuspGeometricClassification : Prop

/-- The obstruction record is parameterized by a candidate prime. -/
def SourcePsiHilbertSamuelAPIObstruction.ofCandidate
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHilbertSamuelAPIObstruction S v q where
  lengthFunction := SourcePsiHSCandidateHilbertFunction S v q
  lengthFunction_eq := fun n => rfl
  localRing := SourcePsiHSCandidateLocalRing S v q
  localRing_eq := rfl
  associatedGradedRing := False
  initialIdeal := False
  hilbertSamuelMultiplicity := False
  nodeCuspGeometricClassification := False

/-- Exact API obstruction statement: only the length function is present; the
associated graded ring, initial ideal, Hilbert-Samuel multiplicity and geometric
node/cusp classification are not constructed. -/
def SourcePsiHilbertSamuelAPIObstructionStatement
    (q : SourcePsiHSCandidatePrime S v) : Prop :=
  (∀ n, SourcePsiHSCandidateHilbertFunction S v q n =
    Module.length (SourcePsiHSCandidateLocalRing S v q)
      (SourcePsiHSCandidateQuotient S v q n)) ∧
    IsLocalRing (SourcePsiHSCandidateLocalRing S v q) ∧
      SourcePsiHSCandidateMaximalIdeal S v q ≠ ⊤

/-- The length/local-ring part of the API obstruction is actual and proved. -/
theorem SourcePsiHilbertSamuelAPIObstructionStatement_iff
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHilbertSamuelAPIObstructionStatement S v q :=
  ⟨fun n => SourcePsiHSCandidateHilbertFunction_eq S v q n,
    SourcePsiCandidateLocalRing_isLocalRing S v q,
    SourcePsiHSCandidateMaximalIdeal_ne_top S v q⟩

/-- Candidate node/cusp classification at the Hilbert-Samuel local data: the
node/cusp flags are the actual containment candidates, and no geometric
multiplicity classification is asserted. -/
def SourcePsiHilbertSamuelNodeCuspCandidate
    (q : SourcePsiHSCandidatePrime S v) : Prop :=
  SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q

/-- Every Jacobian candidate prime has the node/cusp candidate dichotomy. -/
theorem SourcePsiHilbertSamuelNodeCuspCandidate_iff
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHilbertSamuelNodeCuspCandidate S v q :=
  SourcePsiCandidateNode_or_cusp S v q

/-- Exact residual for the actual Hilbert-Samuel multiplicity: the length
function exists, while associated graded/initial ideal/geometric multiplicity and
node/cusp geometric classification remain missing. -/
def SourcePsiHilbertSamuelMultiplicityResidual : Prop :=
  (∀ q : SourcePsiHSCandidatePrime S v,
    Nonempty (SourcePsiHilbertSamuelAPIObstruction S v q)) ∧
    (∀ q : SourcePsiHSCandidatePrime S v,
      SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q)

/-- The residual is exactly the actual length data and candidate dichotomy. -/
theorem SourcePsiHilbertSamuelMultiplicityResidual_iff :
    SourcePsiHilbertSamuelMultiplicityResidual S v :=
  ⟨fun q => ⟨SourcePsiHilbertSamuelAPIObstruction.ofCandidate S v q⟩,
    fun q => SourcePsiCandidateNode_or_cusp S v q⟩



/-- The maximal ideal power at exponent one is the maximal ideal. -/
theorem SourcePsiHSCandidateMaximalIdealPower_one
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateMaximalIdealPower S v q 1 =
      SourcePsiHSCandidateMaximalIdeal S v q := by
  simp [SourcePsiHSCandidateMaximalIdealPower]

/-- The maximal ideal power at exponent zero is the unit ideal. -/
theorem SourcePsiHSCandidateMaximalIdealPower_zero_eq_top
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateMaximalIdealPower S v q 0 = ⊤ :=
  SourcePsiHSCandidateMaximalIdealPower_zero S v q

/-- The quotient at exponent zero is a subsingleton. -/
theorem SourcePsiHSCandidateQuotient_zero_subsingleton
    (q : SourcePsiHSCandidatePrime S v) :
    Subsingleton (SourcePsiHSCandidateQuotient S v q 0) := by
  unfold SourcePsiHSCandidateQuotient
  rw [SourcePsiHSCandidateMaximalIdealPower_zero S v q]
  infer_instance

/-- The actual length at exponent zero is zero. -/
theorem SourcePsiHSCandidateLength_zero
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateLength S v q 0 = 0 := by
  simp [SourcePsiHSCandidateLength, SourcePsiHSCandidateQuotient,
    SourcePsiHSCandidateMaximalIdealPower_zero]

/-- The Hilbert function at exponent zero is zero. -/
theorem SourcePsiHSCandidateHilbertFunction_zero
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSCandidateHilbertFunction S v q 0 = 0 :=
  SourcePsiHSCandidateLength_zero S v q

/-- The candidate local ring is Noetherian; included in the Hilbert-Samuel data. -/
theorem SourcePsiHSCandidateLocalRing_noetherian
    (q : SourcePsiHSCandidatePrime S v) :
    IsNoetherianRing (SourcePsiHSCandidateLocalRing S v q) :=
  SourcePsiCandidateLocalRing_isNoetherian S v q

/-- The candidate local ring is local; included in the Hilbert-Samuel data. -/
theorem SourcePsiHSCandidateLocalRing_local
    (q : SourcePsiHSCandidatePrime S v) :
    IsLocalRing (SourcePsiHSCandidateLocalRing S v q) :=
  SourcePsiCandidateLocalRing_isLocalRing S v q

/-- Consumer: the obstruction record exposes the actual local ring. -/
theorem SourcePsiHilbertSamuelAPIObstruction_localRing
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) :
    D.localRing = SourcePsiHSCandidateLocalRing S v q :=
  D.localRing_eq

/-- Consumer: the obstruction record exposes the actual length function. -/
theorem SourcePsiHilbertSamuelAPIObstruction_lengthFunction
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) (n : ℕ) :
    D.lengthFunction n = SourcePsiHSCandidateLength S v q n :=
  D.lengthFunction_eq n

/-- Consumer: associated graded ring field of the obstruction record. -/
theorem SourcePsiHilbertSamuelAPIObstruction_associatedGraded
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) :
    D.associatedGradedRing = False := rfl

/-- Consumer: initial ideal field of the obstruction record. -/
theorem SourcePsiHilbertSamuelAPIObstruction_initialIdeal
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) :
    D.initialIdeal = False := rfl

/-- Consumer: Hilbert-Samuel multiplicity field of the obstruction record. -/
theorem SourcePsiHilbertSamuelAPIObstruction_hilbertSamuelMultiplicity
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) :
    D.hilbertSamuelMultiplicity = False := rfl

/-- Consumer: geometric node/cusp classification field of the obstruction
record. -/
theorem SourcePsiHilbertSamuelAPIObstruction_nodeCuspClassification
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHilbertSamuelAPIObstruction S v q) :
    D.nodeCuspGeometricClassification = False := rfl

/-- Node/cusp candidate flags from the prior local data. -/
theorem SourcePsiHilbertSamuelNodeCuspCandidate_node_or_cusp
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q :=
  SourcePsiHilbertSamuelNodeCuspCandidate_iff S v q

/-! ## Exact Hilbert-Samuel multiplicity boundary

Constructed:
- actual local ring A_q at each Jacobian candidate prime;
- actual maximal ideal m_q and its powers m_q^n;
- actual quotient A_q / m_q^n;
- actual module length and candidate Hilbert function n -> length(A_q / m_q^n);
- finite-length conditional theorem and candidate length value;
- explicit API obstruction record containing the length data and the missing
  associated graded, initial ideal, Hilbert-Samuel multiplicity, and geometric
  node/cusp classification fields;
- node/cusp candidate dichotomy at every Jacobian prime.

NOT constructed or asserted:
- associated graded ring gr_{m_q}(A_q);
- initial ideal or tangent-cone initial form;
- Hilbert-Samuel multiplicity as an actual invariant;
- geometric node/cusp classification;
- component intersection multiplicities;
- stable reduction/multiplicity comparison with the source.

These are exact residual objects.  No multiplicity is fabricated.
-/
end LeanFormal.IUT.SourcePsiHilbertSamuelMultiplicity

end