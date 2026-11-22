import tmp.sheaf.xif.paper.S1962R1AbstractActionActual

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

namespace LeanFormal.IUT.XiFPaper.S1974PsiTildeTopFieldActual
/-!
# S1974: the ind-topological division-ring structure on `Ψ~`

Layer **O**.  Consumes S1962 (`R1FirstMissing`) and the actual finite-stage
ind topology of `FinitePlaceSourceIndTopology`.

## What is proved here (no `sorry`, no axiom, no fake topology)

1. **Generic transfer** (`section Transfer`): a ring equivalence `e : R ≃+* S`
   that is a homeomorphism transports `IsTopologicalRing` and
   `IsTopologicalDivisionRing` from `R` to `S`, and `ContinuousInv₀` as well.

2. **The paper's own topology on `Ψ~`.**  [AbsTopIII], Definition 3.1, (i) and
   (iv): the p-adic logarithm identifies `k^∼ = (O_k^×)^pf` with the additive
   topological group of the MLF `k`, and "the field structure of k determines,
   via the inverse morphism to log_k, a structure of *topological field* on the
   topological group k^∼".  On the formal carrier `Ψ~ = SourceUnitPerfection
   (QPlace v)` this topology is `psiTildeLogTopology v`, the topology induced
   along the actual logarithmic equivalence `sourceUnitPerfectionEquiv`.
   `sourceAlgebraicClosure_isTopologicalDivisionRing` records the source
   topological division ring.

3. **The finite-stage final topology refines it.**
   `isOpen_of_isOpen_algebraicClosure` proves that every open set of the actual
   completed algebraic closure is open for the final topology of the actual
   finite local subfields (each stage carries the subspace topology, so the
   stage inclusions are continuous).  Transported through the actual ind
   homeomorphism `sourceUnitPerfectionIndHomeomorph`, the finite-stage final
   topology `sourceUnitPerfectionIndTopology` therefore refines the paper's
   log-transported topology: S1962's `R1FirstMissing` asks for the
   *refinement* of the paper's topological-field structure to the final
   topology, which is strictly more than the paper asserts.

4. **The exact first missing.**  `R1IndTopologyRingMissing v` is
   `IsTopologicalRing` for the transported field structure and the actual
   final topology (joint continuity of `+`, `*`, `-` on the limit);
   `R1IndTopologyInvMissing v` is `ContinuousInv₀` (continuity of inversion at
   nonzero points).  `R1FirstMissing v` is *definitionally* the conjunction of
   these two components (`IsTopologicalDivisionRing = IsTopologicalRing ∧
   `ContinuousInv₀`); the implication from `R1FirstMissing` to the ring part is
   proved.  The exact first missing is `R1IndTopologyRingMissing v`; neither
   component is proved anywhere in the tree.

## Why the final topology is the hard part

The final topology is the supremum of the coinduced topologies of the genuine
finite local subfields; a set is open iff its trace on every finite subfield is
open.  Stagewise continuity of the operations is trivial, but continuity on
the limit is a statement about the *product of the final topologies* with values
in the final topology, and the product of final topologies is finer than the
final topology of the finite-stage products.  The tree records exactly this
phenomenon for the Galois action (`SourceDefinition52LocalJointContinuity`:
"joint continuity on the single limit carrier would require a separate
continuity-with-parameters theorem"), and no such theorem exists for the ring
operations.  Hence the missing input is a genuine continuity theorem, not a
triviality, and it cannot be obtained from the existing finite-stage results.
-/


section Transfer

variable {R S : Type*} [Field R] [TopologicalSpace R] [Field S] [TopologicalSpace S]

lemma map_inv_apply (e : R ≃+* S) (y : S) : e ((e.symm y)⁻¹) = y⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have ha : e.symm y ≠ 0 := fun h => hy (by rw [← e.apply_symm_apply y, h, map_zero])
    have h1 : e ((e.symm y)⁻¹) * e (e.symm y) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    rw [e.apply_symm_apply y] at h1
    exact eq_inv_of_mul_eq_one_left h1

lemma continuous_comp_iff (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous (e.symm : S → R)) {X : Type*} [TopologicalSpace X] (f : X → S) :
    Continuous f ↔ Continuous fun x => e.symm (f x) := by
  constructor
  · intro hf; exact Continuous.comp he' hf
  · intro hf
    have h := Continuous.comp he hf
    simpa [Function.comp_def] using h

theorem continuousInv₀_transfer (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous (e.symm : S → R)) (hR : ContinuousInv₀ R) : ContinuousInv₀ S where
  continuousAt_inv₀ := by
    intro x hx
    have hfun : (fun y : S => e ((e.symm y)⁻¹)) = Inv.inv := by
      funext y; exact map_inv_apply e y
    have hlim : Filter.Tendsto (fun y : S => e ((e.symm y)⁻¹)) (𝓝 x) (𝓝 x⁻¹) := by
      have h1 : Filter.Tendsto (fun y : S => e.symm y) (𝓝 x) (𝓝 (e.symm x)) := he'.continuousAt
      have ha : e.symm x ≠ 0 := fun h => hx (by rw [← e.apply_symm_apply x, h, map_zero])
      have h2 : Filter.Tendsto (Inv.inv : R → R) (𝓝 (e.symm x)) (𝓝 ((e.symm x)⁻¹)) :=
        hR.continuousAt_inv₀ ha
      have h3 : Filter.Tendsto e (𝓝 ((e.symm x)⁻¹)) (𝓝 (e ((e.symm x)⁻¹))) := he.continuousAt
      have h4 := h3.comp (h2.comp h1)
      rw [map_inv_apply e x] at h4
      exact h4
    have hfinal := hlim
    rw [hfun] at hfinal
    simpa [ContinuousAt] using hfinal

theorem isTopologicalRing_transfer (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous (e.symm : S → R)) (hR : IsTopologicalRing R) : IsTopologicalRing S := by
  haveI hAdd : ContinuousAdd S :=
    ⟨(continuous_comp_iff e he he' (fun p : S × S => p.1 + p.2)).mpr <| by
      have h := hR.continuous_add.comp
        ((Continuous.comp he' continuous_fst).prodMk (Continuous.comp he' continuous_snd))
      simpa [map_add, Function.comp_def] using h⟩
  haveI hMul : ContinuousMul S :=
    ⟨(continuous_comp_iff e he he' (fun p : S × S => p.1 * p.2)).mpr <| by
      have h := hR.continuous_mul.comp
        ((Continuous.comp he' continuous_fst).prodMk (Continuous.comp he' continuous_snd))
      simpa [map_mul, Function.comp_def] using h⟩
  haveI hNeg : ContinuousNeg S :=
    ⟨(continuous_comp_iff e he he' (fun x : S => -x)).mpr <| by
      have h := Continuous.comp hR.continuous_neg he'
      simpa [map_neg, Function.comp_def] using h⟩
  haveI hSemiring : IsTopologicalSemiring S := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

theorem isTopologicalDivisionRing_transfer (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous (e.symm : S → R)) [IsTopologicalDivisionRing R] :
    IsTopologicalDivisionRing S := by
  haveI hRing : IsTopologicalRing S :=
    isTopologicalRing_transfer e he he' IsTopologicalDivisionRing.toIsTopologicalRing
  haveI hInv : ContinuousInv₀ S :=
    continuousInv₀_transfer e he he' IsTopologicalDivisionRing.toContinuousInv₀
  exact IsTopologicalDivisionRing.mk

end Transfer

variable (v : FinitePrimePlace 2 7)

@[reducible] def psiTildeLogTopology (v : FinitePrimePlace 2 7) : TopologicalSpace (PsiTilde v) :=
  TopologicalSpace.induced (sourceUnitPerfectionEquiv (QPlace v)) inferInstance

theorem sourceAlgebraicClosure_isTopologicalDivisionRing (v : FinitePrimePlace 2 7) :
    IsTopologicalDivisionRing (SourceAlgebraicClosure (QPlace v)) := inferInstance

theorem isOpen_of_isOpen_algebraicClosure (v : FinitePrimePlace 2 7)
    {s : Set (SourceAlgebraicClosure (QPlace v))} (hs : IsOpen s) :
    @IsOpen _ (sourceAlgebraicFieldIndTopology (QPlace v)) s := by
  rw [isOpen_algebraicFieldIndTopology_iff]
  intro F
  exact hs.preimage continuous_subtype_val

def R1IndTopologyRingMissing (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiTildeField v
  letI := psiTildeIndTopology v
  IsTopologicalRing (PsiTilde v)

def R1IndTopologyInvMissing (v : FinitePrimePlace 2 7) : Prop :=
  letI := psiTildeField v
  letI := psiTildeIndTopology v
  ContinuousInv₀ (PsiTilde v)

theorem r1IndTopologyRingMissing_of_r1FirstMissing (v : FinitePrimePlace 2 7)
    (h : R1FirstMissing v) : R1IndTopologyRingMissing v := by
  letI := psiTildeField v
  letI := psiTildeIndTopology v
  show IsTopologicalRing (PsiTilde v)
  exact h.toIsTopologicalRing

#print axioms isTopologicalDivisionRing_transfer
#print axioms isOpen_of_isOpen_algebraicClosure
#print axioms r1IndTopologyRingMissing_of_r1FirstMissing

end LeanFormal.IUT.XiFPaper.S1974PsiTildeTopFieldActual