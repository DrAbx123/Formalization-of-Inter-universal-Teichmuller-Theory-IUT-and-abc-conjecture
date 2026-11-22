/-
  Local rings and candidate node/cusp multiplicity data at Jacobian singular
  candidates.

  The actual component graph file defines the finite singular-candidate type as
  minimal primes of the actual Jacobian ideal in the affine coordinate ring.  For
  each such prime q we construct the actual local ring A_q, its residue field and
  cotangent space, and the finite candidate tangent-cone dimension
  finrank(k(q), m_q/m_q^2).  The node/cusp candidate labels at q are by containment
  of the transported c4.

  Mathlib supplies the local ring, noetherian localization, residue field and
  cotangent space.  Actual Hilbert-Samuel multiplicity and geometric tangent-cone
  initial forms are not formalized here; they remain exact residual.  No
  multiplicity or geometric classification is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiComponentIntersectionGraph
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiNodeCuspMultiplicity

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open LeanFormal.IUT.SourcePsiComponentIntersectionGraph
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- A Jacobian singular candidate prime. -/
abbrev SourcePsiCandidatePrime : Type u :=
  SourcePsiSingularCandidateVertex S v

/-- The actual local ring A_q at a Jacobian candidate prime q. -/
noncomputable def SourcePsiCandidateLocalRing (q : SourcePsiCandidatePrime S v) : Type u :=
  letI : q.1.IsPrime := q.2.isPrime
  Localization.AtPrime q.1

/-- The actual local ring is a local ring. -/
instance SourcePsiCandidateLocalRing_isLocalRing
    (q : SourcePsiCandidatePrime S v) :
    IsLocalRing (SourcePsiCandidateLocalRing S v q) := by
  unfold SourcePsiCandidateLocalRing
  infer_instance

/-- The actual local ring is Noetherian. -/
instance SourcePsiCandidateLocalRing_isNoetherian
    (q : SourcePsiCandidatePrime S v) :
    IsNoetherianRing (SourcePsiCandidateLocalRing S v q) := by
  unfold SourcePsiCandidateLocalRing
  infer_instance

/-- The residue field of the actual local ring. -/
abbrev SourcePsiCandidateResidueField (q : SourcePsiCandidatePrime S v) : Type u :=
  IsLocalRing.ResidueField (SourcePsiCandidateLocalRing S v q)

/-- The cotangent space m_q/m_q² of the actual local ring. -/
abbrev SourcePsiCandidateCotangentSpace (q : SourcePsiCandidatePrime S v) : Type u :=
  CotangentSpace (SourcePsiCandidateLocalRing S v q)

/-- The actual cotangent space is finite-dimensional over the residue field. -/
theorem SourcePsiCandidateCotangentSpace_finiteDimensional
    (q : SourcePsiCandidatePrime S v) :
    FiniteDimensional (SourcePsiCandidateResidueField S v q)
      (SourcePsiCandidateCotangentSpace S v q) :=
  inferInstance

/-- Candidate tangent-cone dimension at q: the embedding dimension of the actual
local ring, i.e. finrank of the cotangent space. -/
noncomputable def SourcePsiCandidateTangentConeDimension
    (q : SourcePsiCandidatePrime S v) : ℕ :=
  finrank (SourcePsiCandidateResidueField S v q)
    (SourcePsiCandidateCotangentSpace S v q)

/-- The c4 value at the candidate prime, transported into the coordinate ring. -/
abbrev SourcePsiCandidateC4 : SourcePsiActualCoordinateRing S v :=
  SourcePsiActualC4InCoordinateRing S v

/-- Candidate node at q: the candidate prime does not contain c4. -/
def SourcePsiCandidateNode (q : SourcePsiCandidatePrime S v) : Prop :=
  SourcePsiCandidateC4 S v ∉ q.1

/-- Candidate cusp at q: the candidate prime contains c4. -/
def SourcePsiCandidateCusp (q : SourcePsiCandidatePrime S v) : Prop :=
  SourcePsiCandidateC4 S v ∈ q.1

/-- Node and cusp candidates at q are disjoint. -/
theorem SourcePsiCandidateNodeCusp_disjoint
    (q : SourcePsiCandidatePrime S v) :
    ¬ (SourcePsiCandidateNode S v q ∧ SourcePsiCandidateCusp S v q) := by
  rintro ⟨hn, hc⟩
  exact hn hc

/-- Every Jacobian candidate prime is a node or cusp candidate. -/
theorem SourcePsiCandidateNode_or_cusp
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q := by
  by_cases h : SourcePsiCandidateC4 S v ∈ q.1
  · exact Or.inr h
  · exact Or.inl h

/-- The candidate local multiplicity data at a Jacobian prime. -/
structure SourcePsiCandidateLocalMultiplicityData
    (q : SourcePsiCandidatePrime S v) where
  localRing : Type u
  residueField : Type u
  cotangentSpace : Type u
  localRing_eq : localRing = SourcePsiCandidateLocalRing S v q
  residueField_eq : residueField = SourcePsiCandidateResidueField S v q
  cotangentSpace_eq : cotangentSpace = SourcePsiCandidateCotangentSpace S v q
  cotangent_finiteDimensional : FiniteDimensional residueField cotangentSpace
  tangentConeDimension : ℕ
  tangentConeDimension_eq : tangentConeDimension =
    SourcePsiCandidateTangentConeDimension S v q
  node : Prop
  cusp : Prop
  node_eq : node = SourcePsiCandidateNode S v q
  cusp_eq : cusp = SourcePsiCandidateCusp S v q
  node_or_cusp : node ∨ cusp

/-- The actual candidate local multiplicity data. -/
def SourcePsiCandidateLocalMultiplicityData.ofCandidate
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateLocalMultiplicityData S v q where
  localRing := SourcePsiCandidateLocalRing S v q
  residueField := SourcePsiCandidateResidueField S v q
  cotangentSpace := SourcePsiCandidateCotangentSpace S v q
  localRing_eq := rfl
  residueField_eq := rfl
  cotangentSpace_eq := rfl
  cotangent_finiteDimensional :=
    SourcePsiCandidateCotangentSpace_finiteDimensional S v q
  tangentConeDimension := SourcePsiCandidateTangentConeDimension S v q
  tangentConeDimension_eq := rfl
  node := SourcePsiCandidateNode S v q
  cusp := SourcePsiCandidateCusp S v q
  node_eq := rfl
  cusp_eq := rfl
  node_or_cusp := SourcePsiCandidateNode_or_cusp S v q

/-- Consumer: the candidate local ring is local and Noetherian. -/
theorem SourcePsiCandidateLocalMultiplicityData_local
    (q : SourcePsiCandidatePrime S v) :
    IsLocalRing (SourcePsiCandidateLocalRing S v q) ∧
      IsNoetherianRing (SourcePsiCandidateLocalRing S v q) :=
  ⟨SourcePsiCandidateLocalRing_isLocalRing S v q,
    SourcePsiCandidateLocalRing_isNoetherian S v q⟩

/-- Consumer: the candidate tangent-cone dimension is the cotangent-space
finrank. -/
theorem SourcePsiCandidateTangentConeDimension_eq_finrank
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateTangentConeDimension S v q =
      finrank (SourcePsiCandidateResidueField S v q)
        (SourcePsiCandidateCotangentSpace S v q) :=
  rfl

/-- Candidate local multiplicity statement: actual local ring, finite cotangent
space, finite tangent-cone dimension, and node/cusp candidate dichotomy. -/
def SourcePsiCandidateLocalMultiplicityStatement
    (q : SourcePsiCandidatePrime S v) : Prop :=
  IsLocalRing (SourcePsiCandidateLocalRing S v q) ∧
    IsNoetherianRing (SourcePsiCandidateLocalRing S v q) ∧
      FiniteDimensional (SourcePsiCandidateResidueField S v q)
        (SourcePsiCandidateCotangentSpace S v q) ∧
        (SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q)

/-- The candidate local multiplicity statement is proved at every Jacobian prime. -/
theorem SourcePsiCandidateLocalMultiplicityStatement_iff
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateLocalMultiplicityStatement S v q :=
  ⟨SourcePsiCandidateLocalRing_isLocalRing S v q,
    SourcePsiCandidateLocalRing_isNoetherian S v q,
    SourcePsiCandidateCotangentSpace_finiteDimensional S v q,
    SourcePsiCandidateNode_or_cusp S v q⟩

/-- Exact residual: actual Hilbert-Samuel multiplicity, geometric tangent-cone
initial form, node/cusp geometric classification, and component intersections.
No multiplicity is fabricated. -/
def SourcePsiNodeCuspMultiplicityResidual : Prop :=
  (∀ q : SourcePsiCandidatePrime S v,
    Nonempty (SourcePsiCandidateLocalMultiplicityData S v q)) ∧
    (∀ q : SourcePsiCandidatePrime S v,
      SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q)

/-- The residual is exactly the actual candidate data and dichotomy. -/
theorem SourcePsiNodeCuspMultiplicityResidual_iff :
    SourcePsiNodeCuspMultiplicityResidual S v :=
  ⟨fun q => ⟨SourcePsiCandidateLocalMultiplicityData.ofCandidate S v q⟩,
    fun q => SourcePsiCandidateNode_or_cusp S v q⟩



/-- The actual localization map A -> A_q. -/
def SourcePsiCandidateLocalizationMap (q : SourcePsiCandidatePrime S v) :
    SourcePsiActualCoordinateRing S v →+*
      SourcePsiCandidateLocalRing S v q :=
  algebraMap (SourcePsiActualCoordinateRing S v)
    (SourcePsiCandidateLocalRing S v q)

/-- The localization map is the canonical algebra map. -/
theorem SourcePsiCandidateLocalizationMap_apply
    (q : SourcePsiCandidatePrime S v) (a : SourcePsiActualCoordinateRing S v) :
    SourcePsiCandidateLocalizationMap S v q a =
      algebraMap (SourcePsiActualCoordinateRing S v)
        (SourcePsiCandidateLocalRing S v q) a :=
  rfl

/-- The actual local ring is the localization at the candidate prime. -/
theorem SourcePsiCandidateLocalRing_isLocalization
    (q : SourcePsiCandidatePrime S v) :
    IsLocalization.AtPrime (SourcePsiCandidateLocalRing S v q) q.1 := by
  unfold SourcePsiCandidateLocalRing
  infer_instance

/-- The cotangent space is a finite module. -/
theorem SourcePsiCandidateCotangentSpace_moduleFinite
    (q : SourcePsiCandidatePrime S v) :
    Module.Finite (SourcePsiCandidateLocalRing S v q)
      (SourcePsiCandidateCotangentSpace S v q) :=
  Module.Finite.of_finiteDimensional

/-- The candidate tangent-cone dimension is finite. -/
theorem SourcePsiCandidateTangentConeDimension_finite
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateTangentConeDimension S v q < ⊤ :=
  ENat.coe_lt_top _

/-- The candidate local multiplicity data exposes its tangent-cone dimension. -/
theorem SourcePsiCandidateLocalMultiplicityData_tangentConeDimension
    (q : SourcePsiCandidatePrime S v)
    (D : SourcePsiCandidateLocalMultiplicityData S v q) :
    D.tangentConeDimension =
      SourcePsiCandidateTangentConeDimension S v q :=
  D.tangentConeDimension_eq

/-- The candidate local multiplicity data exposes its node flag. -/
theorem SourcePsiCandidateLocalMultiplicityData_node
    (q : SourcePsiCandidatePrime S v)
    (D : SourcePsiCandidateLocalMultiplicityData S v q) :
    D.node = SourcePsiCandidateNode S v q :=
  D.node_eq

/-- The candidate local multiplicity data exposes its cusp flag. -/
theorem SourcePsiCandidateLocalMultiplicityData_cusp
    (q : SourcePsiCandidatePrime S v)
    (D : SourcePsiCandidateLocalMultiplicityData S v q) :
    D.cusp = SourcePsiCandidateCusp S v q :=
  D.cusp_eq

/-- The candidate local multiplicity data exposes the node-or-cusp dichotomy. -/
theorem SourcePsiCandidateLocalMultiplicityData_node_or_cusp
    (q : SourcePsiCandidatePrime S v)
    (D : SourcePsiCandidateLocalMultiplicityData S v q) :
    D.node ∨ D.cusp :=
  D.node_or_cusp

/-- Consumer: actual local ring at a candidate is local. -/
theorem SourcePsiCandidateLocalMultiplicityStatement_local
    (q : SourcePsiCandidatePrime S v) :
    IsLocalRing (SourcePsiCandidateLocalRing S v q) :=
  (SourcePsiCandidateLocalMultiplicityStatement_iff S v q).1

/-- Consumer: actual local ring at a candidate is Noetherian. -/
theorem SourcePsiCandidateLocalMultiplicityStatement_noetherian
    (q : SourcePsiCandidatePrime S v) :
    IsNoetherianRing (SourcePsiCandidateLocalRing S v q) :=
  (SourcePsiCandidateLocalMultiplicityStatement_iff S v q).2.1

/-- Consumer: cotangent space at a candidate is finite-dimensional. -/
theorem SourcePsiCandidateLocalMultiplicityStatement_cotangent_finite
    (q : SourcePsiCandidatePrime S v) :
    FiniteDimensional (SourcePsiCandidateResidueField S v q)
      (SourcePsiCandidateCotangentSpace S v q) :=
  (SourcePsiCandidateLocalMultiplicityStatement_iff S v q).2.2.1

/-- Consumer: node-or-cusp candidate dichotomy at every Jacobian prime. -/
theorem SourcePsiCandidateLocalMultiplicityStatement_node_or_cusp
    (q : SourcePsiCandidatePrime S v) :
    SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q :=
  (SourcePsiCandidateLocalMultiplicityStatement_iff S v q).2.2.2

/-! ## Exact node/cusp multiplicity boundary

Constructed/proved:
- actual local ring A_q for each Jacobian minimal prime q;
- local and Noetherian instances for A_q;
- actual residue field and cotangent space m_q/m_q^2;
- finite-dimensional cotangent space and finite actual candidate tangent-cone
  dimension finrank;
- node/cusp candidate labels at q by c4 containment, disjoint and exhaustive;
- candidate local multiplicity data and statement.

NOT constructed or asserted:
- actual Hilbert-Samuel multiplicity of A_q;
- geometric tangent-cone initial form or its reduced/nonreduced structure;
- geometric node/cusp classification;
- component intersection multiplicities;
- stable-reduction multiplicity data;
- source comparison.

These are exact residual objects.  No multiplicity or geometric classification is
fabricated.
-/
end LeanFormal.IUT.SourcePsiNodeCuspMultiplicity

end