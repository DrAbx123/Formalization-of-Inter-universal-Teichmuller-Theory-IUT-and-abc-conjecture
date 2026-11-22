import tmp.sheaf.xif.paper.S1974PsiTildeTopFieldActual

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

open Filter
open scoped Topology

open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual
open LeanFormal.IUT.XiFPaper.S1974PsiTildeTopFieldActual

namespace LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual
/-!
# S1995: the paper's own R1 structure on `Ψ~` is an actual topological division ring

Layer **O**.  Consumes S1974 (the transfer lemmas and the distinction between
the log-transported topology and the finite-stage final topology) and S1962
(`Ψ~`, `psiTildeField`).

## The paper object

[AbsTopIII], Definition 3.1, (i) and (iv) identify
`k^∼ = (O_k^×)^pf` with the *additive* topological group of the MLF `k` via the
`p`-adic logarithm `log_k`, and then transport the field structure of `k` back
along `log_k` to obtain a topological-field structure on `k^∼`.  IUT III,
Definition 1.1, (i) is the corresponding construction for `Ψ~_{†F_v}`.  The
carrier here is the actual unit perfection `Ψ~ = SourceUnitPerfection (QPlace v)`
of S1962, the logarithmic identification is the actual
`sourceUnitPerfectionEquiv : Ψ~ ≃ₗ[ℚ] SourceAlgebraicClosure`, and the
paper's topology is

`psiTildeLogTopology v = induced (sourceUnitPerfectionEquiv (QPlace v)) (norm topology)`,

i.e. exactly the topology pulled back along `log_k`.  This is *not* the
finite-stage final topology `psiTildeIndTopology v` of S1962/S1974.

## What is proved here (no `sorry`, no axiom, no fake topology)

1. **The ring equivalence of S1974, instantiated.**  `psiTildeRingEquiv v` is
   the bijection underlying `sourceUnitPerfectionEquiv`, made into an actual
   `SourceAlgebraicClosure (QPlace v) ≃+* PsiTilde v` for the field structure
   `psiTildeField v`.

2. **The logarithmic topology is the pullback of the MLF topology.**
   `continuous_sourceUnitPerfectionEquiv`,
   `continuous_sourceUnitPerfectionEquiv_symm`, and the homeomorphism
   `psiTildeLogHomeomorph v : Ψ~ ≃ₜ SourceAlgebraicClosure (QPlace v)`.

3. **The paper's R1 structure.**  `psiTildeLogTopology_isTopologicalDivisionRing v`
   proves `IsTopologicalDivisionRing (PsiTilde v)` for `psiTildeField v` and
   `psiTildeLogTopology v`, by applying S1974's
   `isTopologicalDivisionRing_transfer` to the actual ring equivalence and the
   actual homeomorphism.  `PaperR1Structure v` records the proposition and
   `paperR1Structure v` proves it.  The topological-ring and inversion parts
   are `psiTildeLogTopology_isTopologicalRing`,
   `psiTildeLogTopology_continuousInv₀`, and the joint continuities
   `psiTildeLogTopology_continuousAdd` and
   `psiTildeLogTopology_continuousMul`.

4. **The exact relation to S1962's `R1FirstMissing`.**
   S1974's `isOpen_of_isOpen_algebraicClosure` proves at the source level that
   every norm-open subset of the actual algebraic closure is open for the
   finite-stage final topology, i.e. the final topology refines the MLF
   topology.  Consequently S1962's `R1FirstMissing v`, which asks for the
   *final* topology on `Ψ~`, is strictly stronger than the paper's assertion;
   here we record the exact logical consequence:
   `r1FirstMissing_of_logTopology_eq_indTopology` derives it once the two
   topologies are identified.  The `Ψ~`-level set-theoretic transport of the
   refinement itself is not formalized in this file.

## The instance-coherence point (why this file exists)

`psiTildeField v` is `(sourceUnitPerfectionEquiv (QPlace v)).toEquiv.field`:
the field operations are transported along the logarithmic equivalence, so the
transported addition is `Equiv.add` and the transported multiplication is
`Equiv.mul` of that equivalence.  However, `Ψ~` also carries the direct
`OreLocalization.instAdd` instance of the underlying localized module, and in a
context `[Field (PsiTilde v)]` plain type-class search for `Add (PsiTilde v)`
selects *that* untransported direct instance (a direct instance beats the
derived field projection).  Stating the `RingEquiv` obligations with only
`psiTildeField v` in scope would therefore silently use the untransported
localized-module addition and would not prove anything about the paper's field
structure.  We resolve this by registering the transported operations as
direct instances:

* `psiTildeAdd v = Equiv.add (sourceUnitPerfectionEquiv (QPlace v)).toEquiv`,
* `psiTildeMul v = Equiv.mul (sourceUnitPerfectionEquiv (QPlace v)).toEquiv`.

These are definitionally the operations of `psiTildeField v` (this is what
makes the S1974 transfer lemma applicable at the concrete carrier: it forces
the `Add`/`Mul` arguments of the `RingEquiv` to coincide with the projections
of `psiTildeField v`), and the final statements use only
`psiTildeField v` and `psiTildeLogTopology v`.  No operation is postulated and
no topology is replaced by an abstract one.

## Source locations

* [AbsTopIII], Definition 3.1, (i) (log and `k^∼`) and (iv) (topological field
  structure via the inverse of `log_k`).
* IUT III, Definition 1.1, (i), text l.1259--1351 (`Ψ~` with its
  ind-topological field structure).
* Upstream actual sources: `FinitePlaceSourceAlgebraicUnitPerfection`
  (`sourceUnitPerfectionEquiv`), `FinitePlaceSourceIndTopology`,
  `AlgebraicUnitLogarithmRationalization`.
-/

/-! ## 1. The transported operations and the ring equivalence -/

/-- The addition on `Ψ~` transported along the logarithmic identification
`sourceUnitPerfectionEquiv`.  This is definitionally the addition of the
paper's field structure `psiTildeField`; it is recorded as a direct `Add`
instance so that the ring-equivalence obligations are stated against the
transported operation rather than the untransported localized-module
addition (see the module docstring). -/
noncomputable abbrev psiTildeAdd (v : FinitePrimePlace 2 7) : Add (PsiTilde v) :=
  Equiv.add (sourceUnitPerfectionEquiv (QPlace v)).toEquiv

/-- The multiplication on `Ψ~` transported along the logarithmic identification
`sourceUnitPerfectionEquiv`; definitionally the multiplication of
`psiTildeField`. -/
noncomputable abbrev psiTildeMul (v : FinitePrimePlace 2 7) : Mul (PsiTilde v) :=
  Equiv.mul (sourceUnitPerfectionEquiv (QPlace v)).toEquiv

/-- The zero of `Ψ~` transported along the logarithmic identification
`sourceUnitPerfectionEquiv`; definitionally the zero of `psiTildeField`.
Recorded as a direct `Zero` instance for the same coherence reason as
`psiTildeAdd` and `psiTildeMul` (the underlying localized module carries a
direct `OreLocalization.instZero`). -/
noncomputable abbrev psiTildeZero (v : FinitePrimePlace 2 7) : Zero (PsiTilde v) :=
  Equiv.zero (sourceUnitPerfectionEquiv (QPlace v)).toEquiv

/-- Definitional unfolding of the transported addition: it is the conjugation
of the addition of the actual algebraic closure by the logarithmic
identification. -/
theorem psiTildeAdd_apply (v : FinitePrimePlace 2 7) (x y : PsiTilde v) :
    letI := psiTildeAdd v
    x + y = (sourceUnitPerfectionEquiv (QPlace v)).symm
      ((sourceUnitPerfectionEquiv (QPlace v)) x +
        (sourceUnitPerfectionEquiv (QPlace v)) y) := rfl

/-- Definitional unfolding of the transported multiplication. -/
theorem psiTildeMul_apply (v : FinitePrimePlace 2 7) (x y : PsiTilde v) :
    letI := psiTildeMul v
    x * y = (sourceUnitPerfectionEquiv (QPlace v)).symm
      ((sourceUnitPerfectionEquiv (QPlace v)) x *
        (sourceUnitPerfectionEquiv (QPlace v)) y) := rfl

/-- **The actual ring equivalence along `log_k`.**  The underlying bijection is
`sourceUnitPerfectionEquiv`, and the ring structure on `Ψ~` is the transported
field structure `psiTildeField`, i.e. the paper's field structure. -/
noncomputable def psiTildeRingEquiv (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeAdd v
    letI := psiTildeMul v
    SourceAlgebraicClosure (QPlace v) ≃+* PsiTilde v := by
  letI := psiTildeField v
  letI := psiTildeAdd v
  letI := psiTildeMul v
  refine { toEquiv := (sourceUnitPerfectionEquiv (QPlace v)).symm.toEquiv,
           map_add' := ?_, map_mul' := ?_ }
  · intro x y
    change (sourceUnitPerfectionEquiv (QPlace v)).symm (x * y) =
      (sourceUnitPerfectionEquiv (QPlace v)).symm
        ((sourceUnitPerfectionEquiv (QPlace v))
          ((sourceUnitPerfectionEquiv (QPlace v)).symm x) *
         (sourceUnitPerfectionEquiv (QPlace v))
          ((sourceUnitPerfectionEquiv (QPlace v)).symm y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · intro x y
    change (sourceUnitPerfectionEquiv (QPlace v)).symm (x + y) =
      (sourceUnitPerfectionEquiv (QPlace v)).symm
        ((sourceUnitPerfectionEquiv (QPlace v))
          ((sourceUnitPerfectionEquiv (QPlace v)).symm x) +
         (sourceUnitPerfectionEquiv (QPlace v))
          ((sourceUnitPerfectionEquiv (QPlace v)).symm y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-! ## 2. Continuity of the logarithmic identification -/

/-- `log_k : Ψ~ → k` is continuous for the log-transported topology. -/
theorem continuous_sourceUnitPerfectionEquiv (v : FinitePrimePlace 2 7) :
    letI := psiTildeLogTopology v
    Continuous (sourceUnitPerfectionEquiv (QPlace v) :
      PsiTilde v → SourceAlgebraicClosure (QPlace v)) := by
  letI := psiTildeLogTopology v
  exact continuous_induced_dom

/-- The inverse of `log_k` is continuous for the log-transported topology, so
that `log_k` is a homeomorphism onto the actual algebraic closure. -/
theorem continuous_sourceUnitPerfectionEquiv_symm (v : FinitePrimePlace 2 7) :
    letI := psiTildeLogTopology v
    Continuous ((sourceUnitPerfectionEquiv (QPlace v)).symm :
      SourceAlgebraicClosure (QPlace v) → PsiTilde v) := by
  letI := psiTildeLogTopology v
  have hInd : Topology.IsInducing (sourceUnitPerfectionEquiv (QPlace v)) :=
    Topology.IsInducing.induced _
  rw [hInd.continuous_iff]
  have hcomp : ((sourceUnitPerfectionEquiv (QPlace v)) ∘
      (sourceUnitPerfectionEquiv (QPlace v)).symm :
      SourceAlgebraicClosure (QPlace v) → SourceAlgebraicClosure (QPlace v)) = id := by
    funext x
    exact (sourceUnitPerfectionEquiv (QPlace v)).apply_symm_apply x
  rw [hcomp]
  exact continuous_id

/-- **The logarithmic homeomorphism** between `Ψ~` carrying the paper's
topology and the actual algebraic closure carrying the MLF norm topology. -/
noncomputable def psiTildeLogHomeomorph (v : FinitePrimePlace 2 7) :
    letI := psiTildeLogTopology v
    PsiTilde v ≃ₜ SourceAlgebraicClosure (QPlace v) := by
  letI := psiTildeLogTopology v
  exact { (sourceUnitPerfectionEquiv (QPlace v)).toEquiv with
    continuous_toFun := continuous_sourceUnitPerfectionEquiv v
    continuous_invFun := continuous_sourceUnitPerfectionEquiv_symm v }

@[simp]
theorem psiTildeLogHomeomorph_apply (v : FinitePrimePlace 2 7) (x : PsiTilde v) :
    letI := psiTildeLogTopology v
    psiTildeLogHomeomorph v x = sourceUnitPerfectionEquiv (QPlace v) x := rfl

/-! ## 3. The paper's R1 structure -/

/-- **The paper's own R1 structure**: `Ψ~` with the field structure transported
along `log_k` and with the log-transported MLF topology is a topological
division ring. -/
theorem psiTildeLogTopology_isTopologicalDivisionRing (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeLogTopology v
    IsTopologicalDivisionRing (PsiTilde v) := by
  letI := psiTildeField v
  letI := psiTildeLogTopology v
  letI := psiTildeAdd v
  letI := psiTildeMul v
  have hcont : Continuous (⇑(psiTildeRingEquiv v)) := by
    change Continuous (⇑((sourceUnitPerfectionEquiv (QPlace v)).symm) :
      SourceAlgebraicClosure (QPlace v) → PsiTilde v)
    exact continuous_sourceUnitPerfectionEquiv_symm v
  have hcont' : Continuous (⇑((psiTildeRingEquiv v).symm)) := by
    change Continuous (⇑(sourceUnitPerfectionEquiv (QPlace v)) :
      PsiTilde v → SourceAlgebraicClosure (QPlace v))
    exact continuous_sourceUnitPerfectionEquiv v
  exact isTopologicalDivisionRing_transfer (psiTildeRingEquiv v) hcont hcont'

/-- The topological-ring part of the paper's R1 structure. -/
theorem psiTildeLogTopology_isTopologicalRing (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeLogTopology v
    IsTopologicalRing (PsiTilde v) :=
  (psiTildeLogTopology_isTopologicalDivisionRing v).toIsTopologicalRing

/-- Continuity of inversion at nonzero points for the paper's topology.  The
transported `Zero` is registered explicitly for the same coherence reason as
`psiTildeAdd`: the direct `OreLocalization.instZero` would otherwise be
selected by type-class search. -/
theorem psiTildeLogTopology_continuousInv₀ (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeLogTopology v
    letI := psiTildeZero v
    ContinuousInv₀ (PsiTilde v) :=
  (psiTildeLogTopology_isTopologicalDivisionRing v).toContinuousInv₀

/-- Joint continuity of the paper's field addition (transported along `log_k`). -/
theorem psiTildeLogTopology_continuousAdd (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeLogTopology v
    letI := psiTildeAdd v
    ContinuousAdd (PsiTilde v) :=
  (psiTildeLogTopology_isTopologicalDivisionRing v).toIsTopologicalRing.toContinuousAdd

/-- Joint continuity of the paper's field multiplication (transported along
`log_k`). -/
theorem psiTildeLogTopology_continuousMul (v : FinitePrimePlace 2 7) :
    letI := psiTildeField v
    letI := psiTildeLogTopology v
    letI := psiTildeMul v
    ContinuousMul (PsiTilde v) :=
  (psiTildeLogTopology_isTopologicalDivisionRing v).toIsTopologicalRing.toContinuousMul

/-- The paper's R1 structure in propositional form. -/
def PaperR1Structure (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiTildeField v
  letI := psiTildeLogTopology v
  IsTopologicalDivisionRing (PsiTilde v)

/-- **The paper's R1 structure is available**: `Ψ~`, with the field structure
transported along the actual `p`-adic logarithm and with the log-transported
MLF topology, is an actual topological division ring. -/
theorem paperR1Structure (v : FinitePrimePlace 2 7) : PaperR1Structure v :=
  psiTildeLogTopology_isTopologicalDivisionRing v

/-! ## 4. Relation to S1962's final-topology statement -/

/-! The comparison with the finite-stage final topology is S1974's
`isOpen_of_isOpen_algebraicClosure`: every norm-open subset of the actual
algebraic closure is open in `sourceAlgebraicFieldIndTopology`, i.e. the final
topology refines the norm (MLF) topology at the source level.  Transporting
that refinement through the logarithmic homeomorphism would give
`psiTildeIndTopology v ≤ psiTildeLogTopology v`; this `Ψ~`-level set-theoretic
transport is *not* formalized in this file (the mathematical refinement itself
is already established in S1974).  What is recorded below is the exact logical
consequence for S1962's `R1FirstMissing`: it follows once the two topologies
are identified. -/

/-- **Conditional bridge to S1962's `R1FirstMissing`.**  If the finite-stage
final topology coincides with the paper's log topology, then S1962's
final-topology statement holds.  Without this identification the paper proves
only the coarser log-topology statement above; this is exactly the gap. -/
theorem r1FirstMissing_of_logTopology_eq_indTopology (v : FinitePrimePlace 2 7)
    (h : psiTildeLogTopology v = psiTildeIndTopology v) : R1FirstMissing v := by
  letI := psiTildeField v
  letI := psiTildeIndTopology v
  have hmain := psiTildeLogTopology_isTopologicalDivisionRing v
  rw [h] at hmain
  exact hmain

/-! ## 5. Axiom probes -/

#print axioms psiTildeRingEquiv
#print axioms psiTildeLogHomeomorph
#print axioms psiTildeLogTopology_isTopologicalDivisionRing
#print axioms psiTildeLogTopology_isTopologicalRing
#print axioms psiTildeLogTopology_continuousInv₀
#print axioms psiTildeLogTopology_continuousAdd
#print axioms psiTildeLogTopology_continuousMul
#print axioms paperR1Structure
#print axioms r1FirstMissing_of_logTopology_eq_indTopology

end LeanFormal.IUT.XiFPaper.S1995PsiTildeLogTopFieldActual
