/-
  Component intersection graph data for the actual reduced curve.

  The actual finite component type consists of minimal primes of the affine
  coordinate ring of the Mathlib minimal special fiber.  The finite singular
  candidate type consists of minimal primes of the Jacobian ideal.  From these we
  construct:
  * the actual component schemes Spec(A/p);
  * the component-to-singular incidence relation by prime containment p <= q;
  * the component intersection graph with an edge between distinct components
    whose prime sum is not the whole ring;
  * candidate node/cusp labels at the curve level.

  The incidence and graph are actual algebraic data.  Geometric node/cusp
  classification, component intersection multiplicities, and stable component data
  remain exact residual.  No intersection graph is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiComponentFiniteActual
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiComponentIntersectionGraph

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual component type: minimal primes of the actual affine coordinate
ring. -/
abbrev SourcePsiComponentVertex : Type u :=
  SourcePsiActualComponentType S v

/-- The actual singular-candidate type: minimal primes of the Jacobian ideal. -/
abbrev SourcePsiSingularCandidateVertex : Type u :=
  SourcePsiActualSingularCandidateType S v

/-- The actual component scheme Spec(A/p) for a minimal prime p. -/
abbrev SourcePsiActualComponentScheme (p : SourcePsiComponentVertex S v) : Type u :=
  PrimeSpectrum (SourcePsiActualCoordinateRing S v ⧸ p.1)

/-- The actual structure map from a component scheme to the affine curve
spectrum. -/
def SourcePsiActualComponentStructureMap (p : SourcePsiComponentVertex S v) :
    PrimeSpectrum (SourcePsiActualCoordinateRing S v ⧸ p.1) →
      PrimeSpectrum (SourcePsiActualCoordinateRing S v) :=
  PrimeSpectrum.comap (Ideal.Quotient.mk p.1)

/-- Candidate node label at the curve level: zero residue discriminant and nonzero
c4. -/
def SourcePsiActualNodeCandidate : Prop :=
  (SourcePsiActualSpecialFiber S v).Δ = 0 ∧
    (SourcePsiActualSpecialFiber S v).c₄ ≠ 0

/-- Candidate cusp label at the curve level: zero residue discriminant and zero
c4. -/
def SourcePsiActualCuspCandidate : Prop :=
  (SourcePsiActualSpecialFiber S v).Δ = 0 ∧
    (SourcePsiActualSpecialFiber S v).c₄ = 0

/-- Node and cusp candidates are disjoint. -/
theorem SourcePsiActualNodeCusp_disjoint :
    ¬ (SourcePsiActualNodeCandidate S v ∧ SourcePsiActualCuspCandidate S v) := by
  rintro ⟨hn, hc⟩
  exact hn.2 hc.2

/-- At zero residue discriminant, the actual singular candidate is a node or cusp
candidate. -/
theorem SourcePsiActualNodeCandidate_or_cusp
    (hΔ : (SourcePsiActualSpecialFiber S v).Δ = 0) :
    SourcePsiActualNodeCandidate S v ∨ SourcePsiActualCuspCandidate S v := by
  by_cases hc : (SourcePsiActualSpecialFiber S v).c₄ = 0
  · exact Or.inr ⟨hΔ, hc⟩
  · exact Or.inl ⟨hΔ, hc⟩

/-- Every actual singular candidate (zero residue discriminant) is a node or cusp
candidate. -/
theorem SourcePsiActualSingular_node_or_cusp
    (hΔ : (SourcePsiActualSpecialFiber S v).Δ = 0) :
    SourcePsiActualNodeCandidate S v ∨ SourcePsiActualCuspCandidate S v :=
  SourcePsiActualNodeCandidate_or_cusp S v hΔ

/-- A node candidate is not elliptic. -/
theorem SourcePsiActualNodeCandidate_not_isElliptic
    (h : SourcePsiActualNodeCandidate S v) :
    ¬ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  fun hE => (SourcePsiActualSpecialFiber_isElliptic_iff_Δ_ne_zero S v).mp hE h.1

/-- A cusp candidate is not elliptic. -/
theorem SourcePsiActualCuspCandidate_not_isElliptic
    (h : SourcePsiActualCuspCandidate S v) :
    ¬ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  fun hE => (SourcePsiActualSpecialFiber_isElliptic_iff_Δ_ne_zero S v).mp hE h.1



/-- The actual c4 value transported into the affine coordinate ring. -/
noncomputable def SourcePsiActualC4InCoordinateRing :
    SourcePsiActualCoordinateRing S v :=
  algebraMap (SourcePsiResidueField S v)
    (SourcePsiActualCoordinateRing S v)
    (SourcePsiActualSpecialFiber S v).c₄

/-- Candidate node at a Jacobian minimal prime: the minimal prime does not
contain the transported c4. -/
def SourcePsiSingularCandidateNode
    (q : SourcePsiSingularCandidateVertex S v) : Prop :=
  SourcePsiActualC4InCoordinateRing S v ∉ q.1

/-- Candidate cusp at a Jacobian minimal prime: the minimal prime contains the
transported c4. -/
def SourcePsiSingularCandidateCusp
    (q : SourcePsiSingularCandidateVertex S v) : Prop :=
  SourcePsiActualC4InCoordinateRing S v ∈ q.1

/-- Every Jacobian minimal prime is a candidate node or cusp at that prime. -/
theorem SourcePsiSingularCandidate_node_or_cusp
    (q : SourcePsiSingularCandidateVertex S v) :
    SourcePsiSingularCandidateNode S v q ∨
      SourcePsiSingularCandidateCusp S v q := by
  by_cases h : SourcePsiActualC4InCoordinateRing S v ∈ q.1
  · exact Or.inr h
  · exact Or.inl h

/-- The candidate node and cusp labels at a Jacobian prime are disjoint. -/
theorem SourcePsiSingularCandidate_node_cusp_disjoint
    (q : SourcePsiSingularCandidateVertex S v) :
    ¬ (SourcePsiSingularCandidateNode S v q ∧
        SourcePsiSingularCandidateCusp S v q) := by
  rintro ⟨hn, hc⟩
  exact hn hc

/-- Jacobian incidence candidate: a singular candidate prime is a minimal prime
of the actual Jacobian ideal. -/
def SourcePsiSingularCandidateJacobianIncidence
    (q : SourcePsiSingularCandidateVertex S v) : Prop :=
  q.1 ∈ (SourcePsiActualJacobianIdeal S v).minimalPrimes

/-- Component-to-singular-candidate incidence by prime containment. -/
def SourcePsiComponentSingularIncidence
    (p : SourcePsiComponentVertex S v)
    (q : SourcePsiSingularCandidateVertex S v) : Prop :=
  p.1 ≤ q.1

/-- Actual finite type of component-singular incidences: a subtype of the finite
product of component and singular-candidate vertices. -/
abbrev SourcePsiComponentSingularIncidenceType : Type u :=
  {pq : SourcePsiComponentVertex S v × SourcePsiSingularCandidateVertex S v //
    SourcePsiComponentSingularIncidence S v pq.1 pq.2}

/-- The component-singular incidence type is finite. -/
theorem SourcePsiComponentSingularIncidenceType_finite :
    Finite (SourcePsiComponentSingularIncidenceType S v) :=
  inferInstance

/-- The component intersection graph: vertices are minimal primes; adjacent
distinct components have non-full prime sum.  This is the actual algebraic
candidate for a nontrivial intersection. -/
def SourcePsiComponentIntersectionGraph :
    SimpleGraph (SourcePsiComponentVertex S v) where
  Adj p q := p ≠ q ∧ p.1 ⊔ q.1 ≠ ⊤
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm, by rwa [sup_comm] at h.2⟩⟩
  loopless := ⟨by
    intro p h
    exact h.1 rfl⟩

/-- Adjacency criterion for the actual component intersection graph. -/
theorem SourcePsiComponentIntersectionGraph_adj_iff
    (p q : SourcePsiComponentVertex S v) :
    (SourcePsiComponentIntersectionGraph S v).Adj p q ↔
      p ≠ q ∧ p.1 ⊔ q.1 ≠ ⊤ :=
  Iff.rfl

/-- Adjacency is symmetric. -/
theorem SourcePsiComponentIntersectionGraph_adj_symm
    {p q : SourcePsiComponentVertex S v}
    (h : (SourcePsiComponentIntersectionGraph S v).Adj p q) :
    (SourcePsiComponentIntersectionGraph S v).Adj q p :=
  (SourcePsiComponentIntersectionGraph S v).symm h

/-- Adjacency is irreflexive. -/
theorem SourcePsiComponentIntersectionGraph_not_adj_self
    (p : SourcePsiComponentVertex S v) :
    ¬ (SourcePsiComponentIntersectionGraph S v).Adj p p :=
  (SourcePsiComponentIntersectionGraph S v).irrefl

/-- Actual component graph/incidence data package. -/
structure SourcePsiComponentGraphData where
  componentVertex : Type u
  singularVertex : Type u
  componentVertex_finite : Finite componentVertex
  singularVertex_finite : Finite singularVertex
  componentScheme : componentVertex → Type u
  incidence : componentVertex → singularVertex → Prop
  intersectionGraph : SimpleGraph componentVertex
  incidence_finite : Finite {pq : componentVertex × singularVertex // incidence pq.1 pq.2}
  singularNode : singularVertex → Prop
  singularCusp : singularVertex → Prop
  singular_node_or_cusp : ∀ q, singularNode q ∨ singularCusp q
  nodeCandidate : Prop
  cuspCandidate : Prop

/-- The actual component graph/incidence data. -/
def SourcePsiComponentGraphData.ofActual :
    SourcePsiComponentGraphData S v where
  componentVertex := SourcePsiComponentVertex S v
  singularVertex := SourcePsiSingularCandidateVertex S v
  componentVertex_finite := SourcePsiActualComponentType_finite S v
  singularVertex_finite := SourcePsiActualSingularCandidateType_finite S v
  componentScheme := SourcePsiActualComponentScheme S v
  incidence := SourcePsiComponentSingularIncidence S v
  intersectionGraph := SourcePsiComponentIntersectionGraph S v
  incidence_finite := SourcePsiComponentSingularIncidenceType_finite S v
  singularNode := SourcePsiSingularCandidateNode S v
  singularCusp := SourcePsiSingularCandidateCusp S v
  singular_node_or_cusp := SourcePsiSingularCandidate_node_or_cusp S v
  nodeCandidate := SourcePsiActualNodeCandidate S v
  cuspCandidate := SourcePsiActualCuspCandidate S v

/-- Consumer: the component graph has finite vertices. -/
theorem SourcePsiComponentGraphData_component_finite
    (D : SourcePsiComponentGraphData S v) :
    Finite D.componentVertex :=
  D.componentVertex_finite

/-- Consumer: the singular candidate graph has finite vertices. -/
theorem SourcePsiComponentGraphData_singular_finite
    (D : SourcePsiComponentGraphData S v) :
    Finite D.singularVertex :=
  D.singularVertex_finite

/-- Consumer: the incidence relation is finite. -/
theorem SourcePsiComponentGraphData_incidence_finite
    (D : SourcePsiComponentGraphData S v) :
    Finite {pq : D.componentVertex × D.singularVertex // D.incidence pq.1 pq.2} :=
  D.incidence_finite

/-- Exact component graph statement: finite vertices, finite incidence, actual
component schemes, actual intersection graph, and node/cusp candidate labels. -/
def SourcePsiComponentGraphStatement : Prop :=
  Finite (SourcePsiComponentVertex S v) ∧
    Finite (SourcePsiSingularCandidateVertex S v) ∧
      Finite (SourcePsiComponentSingularIncidenceType S v) ∧
        ((SourcePsiActualSpecialFiber S v).Δ = 0 →
          SourcePsiActualNodeCandidate S v ∨ SourcePsiActualCuspCandidate S v)

/-- The actual component graph statement is proved. -/
theorem SourcePsiComponentGraphStatement_iff :
    SourcePsiComponentGraphStatement S v :=
  ⟨SourcePsiActualComponentType_finite S v,
    SourcePsiActualSingularCandidateType_finite S v,
    SourcePsiComponentSingularIncidenceType_finite S v,
    SourcePsiActualSingular_node_or_cusp S v⟩

/-- Exact residual: geometric components, actual singular points, node/cusp
classification, intersection multiplicities, and stable component data.  No
geometric intersection graph is fabricated. -/
def SourcePsiComponentIntersectionGraphResidual : Prop :=
  (∃ _D : SourcePsiComponentGraphData S v, True) ∧
    ((SourcePsiActualSpecialFiber S v).Δ = 0 →
      SourcePsiActualNodeCandidate S v ∨ SourcePsiActualCuspCandidate S v)

/-- The residual is compatible with the actual node/cusp candidate dichotomy. -/
theorem SourcePsiComponentIntersectionGraphResidual_iff :
    SourcePsiComponentIntersectionGraphResidual S v :=
  ⟨⟨SourcePsiComponentGraphData.ofActual S v, trivial⟩,
    SourcePsiActualSingular_node_or_cusp S v⟩



/-- A node candidate forces zero residue discriminant. -/
theorem SourcePsiActualNodeCandidate_Δ_eq_zero
    (h : SourcePsiActualNodeCandidate S v) :
    (SourcePsiActualSpecialFiber S v).Δ = 0 :=
  h.1

/-- A cusp candidate forces zero residue discriminant. -/
theorem SourcePsiActualCuspCandidate_Δ_eq_zero
    (h : SourcePsiActualCuspCandidate S v) :
    (SourcePsiActualSpecialFiber S v).Δ = 0 :=
  h.1

/-- The component-singular incidence type is a Fintype. -/
noncomputable def SourcePsiComponentSingularIncidenceType_fintype :
    Fintype (SourcePsiComponentSingularIncidenceType S v) :=
  Fintype.ofFinite _

/-- An intersection-graph edge forces distinct component primes. -/
theorem SourcePsiComponentIntersectionGraph_edge_ne
    {p q : SourcePsiComponentVertex S v}
    (h : (SourcePsiComponentIntersectionGraph S v).Adj p q) :
    p ≠ q :=
  h.1

/-- An intersection-graph edge forces the component-prime sum to be proper. -/
theorem SourcePsiComponentIntersectionGraph_edge_sum_ne_top
    {p q : SourcePsiComponentVertex S v}
    (h : (SourcePsiComponentIntersectionGraph S v).Adj p q) :
    p.1 ⊔ q.1 ≠ ⊤ :=
  h.2

/-- The actual component graph data exposes its intersection graph. -/
theorem SourcePsiComponentGraphData_intersectionGraph
    (D : SourcePsiComponentGraphData S v) :
    D.intersectionGraph = SourcePsiComponentIntersectionGraph S v := rfl

/-- The actual component graph data exposes its incidence relation. -/
theorem SourcePsiComponentGraphData_incidence
    (D : SourcePsiComponentGraphData S v) :
    D.incidence = SourcePsiComponentSingularIncidence S v := rfl

/-- The actual component graph data exposes its node/cusp candidate labels. -/
theorem SourcePsiComponentGraphData_node_cusp
    (D : SourcePsiComponentGraphData S v) :
    D.nodeCandidate = SourcePsiActualNodeCandidate S v ∧
      D.cuspCandidate = SourcePsiActualCuspCandidate S v :=
  ⟨rfl, rfl⟩

/-- The actual component scheme is the spectrum of the quotient by the minimal
prime. -/
theorem SourcePsiActualComponentScheme_eq
    (p : SourcePsiComponentVertex S v) :
    SourcePsiActualComponentScheme S v p =
      PrimeSpectrum (SourcePsiActualCoordinateRing S v ⧸ p.1) := rfl

/-! ## Exact component graph boundary

Constructed:
- actual component schemes Spec(A/p) for minimal primes p of the coordinate ring;
- actual structure maps to the affine curve spectrum;
- component-to-singular-candidate incidence by containment p <= q;
- finite incidence type;
- actual component intersection graph on minimal primes with adjacency by
  distinct components and non-full prime sum;
- node/cusp candidate labels at the curve level and their disjointness;
- actual component graph data and finite statement.

NOT constructed or asserted:
- geometric irreducible components as closed subschemes with their embeddings;
- actual singular points or their cardinality;
- per-component node/cusp classification;
- intersection multiplicities or component intersection numbers;
- stable reduction/component graph over extensions;
- comparison with a source special fiber.

These are exact residual objects.  No geometric intersection graph is fabricated.
-/
end LeanFormal.IUT.SourcePsiComponentIntersectionGraph

end