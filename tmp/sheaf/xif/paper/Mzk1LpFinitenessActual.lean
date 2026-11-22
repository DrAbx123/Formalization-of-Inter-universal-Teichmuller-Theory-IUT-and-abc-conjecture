/- G-K (route §7.2): bounded-degree local extension finiteness, Krasner
near-root generation, and the compositum step towards the universal local
field `L_p`.

Mathlib-only (per Lead decision, TauCetiPort dropped):

* `PadicAlgCl p = AlgebraicClosure ℚ_[p]` is a normed field
  (`Mathlib.NumberTheory.Padics.Complex`) and carries `IsKrasner ℚ_[p] (PadicAlgCl p)`
  from `Mathlib.Analysis.Normed.Field.Krasner` (see also `S2117TopFGActual.krasner_available`);
* the compositum of finitely many finite intermediate fields is finite
  dimensional and (when the pieces are normal closures) normal
  (`IntermediateField.finiteDimensional_iSup_of_finite`, `normal_iSup`,
  `IntermediateField.normalClosure.is_finiteDimensional`).

Honest status (updated 2): the compositum step (6) is proved unconditionally from the
standard finiteness input `BoundedDegreeFinitelyManyFields` (steps 2/5 of the route,
i.e. Eisenstein coefficient finiteness + Krasner); that finiteness input is
recorded as an explicit Prop, not assumed anywhere else and not faked. -/
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual

open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open IntermediateField Polynomial

universe u

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. Krasner's lemma on the concrete `p`-adic algebraic closure -/

/-- Krasner's lemma is available unconditionally on `PadicAlgCl p`
(Mathlib's norm extension theorem gives the `IsKrasner` instance). -/
theorem padic_krasner_available : IsKrasner ℚ_[p] (PadicAlgCl p) := inferInstance

/-- A near root (closer to `x` than every other conjugate of `x`) generates
a field containing `x`.  This is the usable form of Krasner's lemma used in
route §7.2 step 5. -/
theorem padic_krasner_mem {x y : PadicAlgCl p}
    (hx : IsSeparable ℚ_[p] x) (hy : IsIntegral ℚ_[p] y)
    (hsep : ∀ x' : PadicAlgCl p, IsConjRoot ℚ_[p] x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖) :
    x ∈ IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p)) :=
  IsKrasner.krasner hx (IsAlgClosed.splits ((minpoly ℚ_[p] x).map (algebraMap ℚ_[p] (PadicAlgCl p))))
    hy hsep

/-- **Krasner near-root identity of extensions**: a conjugate `y` of `x` that is
separated from the other conjugates generates the same extension.  This is the
proof device for "same extension type" in route §7.2 step 5. -/
theorem padic_krasner_same_extension {x y : PadicAlgCl p}
    (hsep : ∀ x' : PadicAlgCl p, IsConjRoot ℚ_[p] x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖)
    (hconj : IsConjRoot ℚ_[p] x y) :
    IntermediateField.adjoin ℚ_[p] ({x} : Set (PadicAlgCl p)) =
      IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p)) := by
  have hxint : IsIntegral ℚ_[p] x := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
  have hyint : IsIntegral ℚ_[p] y := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic y)
  have hsep' : IsSeparable ℚ_[p] x := IsSeparable.of_integral (F := ℚ_[p]) (K := PadicAlgCl p) x
  have hmem : x ∈ IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p)) :=
    padic_krasner_mem hsep' hyint hsep
  have hle : IntermediateField.adjoin ℚ_[p] ({x} : Set (PadicAlgCl p)) ≤
      IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p)) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hmem
  have hfin : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p))) :=
    IntermediateField.adjoin.finiteDimensional hyint
  refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
  rw [IntermediateField.adjoin.finrank hxint, IntermediateField.adjoin.finrank hyint,
    show minpoly ℚ_[p] x = minpoly ℚ_[p] y from hconj]

/-! ## 2. The bounded-degree finiteness input (route §7.2 steps 2/5) -/

/-- **Route §7.2 finiteness input**: for fixed `p` and `d` there are only finitely
many `ℚ_p`-extension types of degree at most `d` inside the fixed algebraic
closure.  This is the standard consequence of Eisenstein coefficient
finiteness (route step 2) plus Krasner's lemma (step 5); the detailed
coefficient-class argument is the remaining formalisation. -/
def BoundedDegreeFinitelyManyFields (d : ℕ) : Prop :=
  Finite { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
    FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M ≤ d }

/-- The corresponding "finitely many extensions of a fixed degree" statement. -/
def FinitelyManyExtensionTypes (d : ℕ) : Prop :=
  BoundedDegreeFinitelyManyFields (p := p) d

/-! ## 3. Compositum of finitely many normal closures: route §7.2 step 6 -/

/-- The universal local field constructed from a finite index type: the
supremum of the normal closures of the bounded-degree finite intermediate
fields. -/
noncomputable abbrev universalLocalFieldOfFinite (d : ℕ)
    (I : Type) [Finite I]
    (M : I → IntermediateField ℚ_[p] (PadicAlgCl p))
    [∀ i, FiniteDimensional ℚ_[p] (M i)] :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  ⨆ i : I, IntermediateField.normalClosure ℚ_[p] (M i) (PadicAlgCl p)

/-- The compositum of finitely many normal closures is finite dimensional. -/
theorem universalLocalFieldOfFinite_finiteDimensional (d : ℕ)
    (I : Type) [Finite I]
    (M : I → IntermediateField ℚ_[p] (PadicAlgCl p))
    [∀ i, FiniteDimensional ℚ_[p] (M i)] :
    FiniteDimensional ℚ_[p] (universalLocalFieldOfFinite (p := p) d I M) := by
  letI : ∀ i, FiniteDimensional ℚ_[p]
      (IntermediateField.normalClosure ℚ_[p] (M i) (PadicAlgCl p)) := fun i =>
    normalClosure.is_finiteDimensional ℚ_[p] (M i) (PadicAlgCl p)
  exact inferInstance

/-- The compositum of finitely many normal closures is normal over `ℚ_p`. -/
theorem universalLocalFieldOfFinite_normal (d : ℕ)
    (I : Type) [Finite I]
    (M : I → IntermediateField ℚ_[p] (PadicAlgCl p))
    [∀ i, FiniteDimensional ℚ_[p] (M i)] :
    Normal ℚ_[p] (universalLocalFieldOfFinite (p := p) d I M) := by
  letI : ∀ i, Normal ℚ_[p]
      (IntermediateField.normalClosure ℚ_[p] (M i) (PadicAlgCl p)) := fun i =>
    normalClosure.normal ℚ_[p] (M i) (PadicAlgCl p)
  exact inferInstance

/-- **Route §7.2 step 6 → `UniversalLocalFieldExists`**: the bounded-degree
finiteness input produces the actual finite normal local field containing an
isomorphic copy of every `ℚ_p`-extension of degree at most `d`. -/
theorem universalLocalFieldExists_of_finite
    (d : ℕ) (hfin : BoundedDegreeFinitelyManyFields (p := p) d) :
    UniversalLocalFieldExists (p := p) d := by
  classical
  let I := { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
    FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M ≤ d }
  haveI hI : Finite I := hfin
  let Mof : I → IntermediateField ℚ_[p] (PadicAlgCl p) := fun i => i.val
  letI : ∀ i : I, FiniteDimensional ℚ_[p] (Mof i) := fun i => i.2.1
  let L := universalLocalFieldOfFinite (p := p) d I Mof
  haveI hLfin : FiniteDimensional ℚ_[p] L :=
    universalLocalFieldOfFinite_finiteDimensional (p := p) d I Mof
  haveI hLnormal : Normal ℚ_[p] L :=
    universalLocalFieldOfFinite_normal (p := p) d I Mof
  refine ⟨L, inferInstance, inferInstance, hLfin, hLnormal, ?_⟩
  intro M _ _ hMfin hMle
  let iM : M →ₐ[ℚ_[p]] (PadicAlgCl p) := IsAlgClosed.lift
  let Mrange : IntermediateField ℚ_[p] (PadicAlgCl p) := iM.fieldRange
  have hMrangeFin : FiniteDimensional ℚ_[p] Mrange :=
    LinearMap.finiteDimensional_range (iM : M →ₗ[ℚ_[p]] (PadicAlgCl p))
  have hMrangeRank : Module.finrank ℚ_[p] Mrange ≤ d := by
    have hrank : Module.finrank ℚ_[p] Mrange = Module.finrank ℚ_[p] M := by
      let e : M ≃ₗ[ℚ_[p]] Mrange := LinearEquiv.ofInjective
        (iM : M →ₗ[ℚ_[p]] (PadicAlgCl p)) iM.injective
      exact (LinearEquiv.finrank_eq e).symm
    rw [hrank]
    exact hMle
  let i0 : I := ⟨Mrange, hMrangeFin, hMrangeRank⟩
  have hMrangeLe : Mrange ≤ L := by
    refine le_iSup_of_le i0 ?_
    exact le_normalClosure Mrange
  refine ⟨AlgHom.codRestrict iM L.toSubalgebra (fun x => hMrangeLe ⟨x, rfl⟩), ?_⟩
  intro x y hxy
  apply iM.injective
  exact congrArg Subtype.val hxy

/-- **§7.3 interface (andrew)**: the construction is realized by an explicit
`IntermediateField ℚ_[p] (PadicAlgCl p)`, hence carries an injective `ℚ_p`-embedding
into `PadicAlgCl p` for the local-point/embeddability arguments. -/
theorem universalLocalFieldExists_intermediateField
    (d : ℕ) (hfin : BoundedDegreeFinitelyManyFields (p := p) d) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)),
      FiniteDimensional ℚ_[p] L ∧ Normal ℚ_[p] L ∧
      (∃ φ : L →ₐ[ℚ_[p]] (PadicAlgCl p), Function.Injective φ) ∧
      ContainsBoundedExtensions (p := p) d L := by
  classical
  let I := { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
    FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M ≤ d }
  haveI hI : Finite I := hfin
  let Mof : I → IntermediateField ℚ_[p] (PadicAlgCl p) := fun i => i.val
  letI : ∀ i : I, FiniteDimensional ℚ_[p] (Mof i) := fun i => i.2.1
  let L := universalLocalFieldOfFinite (p := p) d I Mof
  haveI hLfin : FiniteDimensional ℚ_[p] L :=
    universalLocalFieldOfFinite_finiteDimensional (p := p) d I Mof
  haveI hLnormal : Normal ℚ_[p] L :=
    universalLocalFieldOfFinite_normal (p := p) d I Mof
  -- the same argument as in `universalLocalFieldExists_of_finite`, keeping the field explicit
  have hcontains : ContainsBoundedExtensions (p := p) d L := by
    intro M _ _ hMfin hMle
    let iM : M →ₐ[ℚ_[p]] (PadicAlgCl p) := IsAlgClosed.lift
    let Mrange : IntermediateField ℚ_[p] (PadicAlgCl p) := iM.fieldRange
    have hMrangeFin : FiniteDimensional ℚ_[p] Mrange :=
      LinearMap.finiteDimensional_range (iM : M →ₗ[ℚ_[p]] (PadicAlgCl p))
    have hMrangeRank : Module.finrank ℚ_[p] Mrange ≤ d := by
      have hrank : Module.finrank ℚ_[p] Mrange = Module.finrank ℚ_[p] M := by
        let e : M ≃ₗ[ℚ_[p]] Mrange := LinearEquiv.ofInjective
          (iM : M →ₗ[ℚ_[p]] (PadicAlgCl p)) iM.injective
        exact (LinearEquiv.finrank_eq e).symm
      rw [hrank]
      exact hMle
    let i0 : I := ⟨Mrange, hMrangeFin, hMrangeRank⟩
    have hMrangeLe : Mrange ≤ L := by
      refine le_iSup_of_le i0 ?_
      exact le_normalClosure Mrange
    refine ⟨AlgHom.codRestrict iM L.toSubalgebra (fun x => hMrangeLe ⟨x, rfl⟩), ?_⟩
    intro x y hxy
    apply iM.injective
    exact congrArg Subtype.val hxy
  exact ⟨L, hLfin, hLnormal, ⟨L.val, fun x y h => Subtype.ext h⟩, hcontains⟩

/-! ## 4. Fixed-degree finiteness versus bounded-degree finiteness -/

/-- Bounded-degree finiteness follows from finiteness in each fixed degree
(route §7.2 step 2 gives the fixed-degree statement; the closed degree bound is
the easy finite-union step). -/
theorem boundedDegreeFinitelyManyFields_of_fixed_degree (d : ℕ)
    (h : ∀ n, n ≤ d → Finite { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
      FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n }) :
    BoundedDegreeFinitelyManyFields (p := p) d := by
  classical
  let I := { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
    FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M ≤ d }
  have hfin : (Set.univ : Set I).Finite := by
    have hcover : (Set.univ : Set I) =
        ⋃ n : { n : ℕ // n ≤ d },
          { M : I |
            Module.finrank ℚ_[p] (M : IntermediateField ℚ_[p] (PadicAlgCl p)) = n.val } := by
      ext M
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      exact ⟨⟨Module.finrank ℚ_[p] (M : IntermediateField ℚ_[p] (PadicAlgCl p)), M.2.2⟩, rfl⟩
    rw [hcover]
    haveI : Finite { n : ℕ // n ≤ d } := (Set.finite_Iic d).to_subtype
    apply Set.finite_iUnion
    intro n
    have hfib : Finite { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
        FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n.val } := h n.val n.2
    refine Finite.of_injective
      (fun (M : { M : I //
          Module.finrank ℚ_[p] (M : IntermediateField ℚ_[p] (PadicAlgCl p)) = n.val }) =>
        (⟨M.1.1, M.1.2.1, M.2⟩ :
          { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
            FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n.val })) ?_
    intro a b hab
    have h1 : (a.1.1 : IntermediateField ℚ_[p] (PadicAlgCl p)) = b.1.1 :=
      congrArg (fun z : { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
          FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n.val } =>
        (z : IntermediateField ℚ_[p] (PadicAlgCl p))) hab
    exact Subtype.ext (Subtype.ext h1)
  exact Finite.of_finite_univ hfin

/-- Conversely, bounded-degree finiteness gives finiteness in every fixed
degree: the fibre over `n` is a subtype of the bounded-degree type. -/
theorem fixed_degree_finite_of_boundedDegree (d : ℕ)
    (h : BoundedDegreeFinitelyManyFields (p := p) d) (n : ℕ) (hn : n ≤ d) :
    Finite { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
      FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n } := by
  classical
  let I := { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
    FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M ≤ d }
  haveI : Finite I := h
  refine Finite.of_injective
    (fun (M : { M : IntermediateField ℚ_[p] (PadicAlgCl p) //
        FiniteDimensional ℚ_[p] M ∧ Module.finrank ℚ_[p] M = n }) =>
      (⟨M.1, M.2.1, le_trans (le_of_eq M.2.2) hn⟩ : I)) ?_
  intro a b hab
  have h1 : (a.1 : IntermediateField ℚ_[p] (PadicAlgCl p)) = b.1 :=
    congrArg (fun z : I => (z : IntermediateField ℚ_[p] (PadicAlgCl p))) hab
  exact Subtype.ext h1

#print axioms padic_krasner_mem
#print axioms padic_krasner_same_extension
#print axioms universalLocalFieldExists_of_finite
#print axioms universalLocalFieldExists_intermediateField
#print axioms boundedDegreeFinitelyManyFields_of_fixed_degree
#print axioms fixed_degree_finite_of_boundedDegree

end LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual
end