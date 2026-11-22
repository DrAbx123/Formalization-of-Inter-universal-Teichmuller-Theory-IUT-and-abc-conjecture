/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1794 -- the six fields of PreGaloisCategory.FiberFunctor (fiber K Omega)

Target (per the task): for a field K and a geometric point Omega (a separably closed field
extension of K), decide how much of

  PreGaloisCategory.FiberFunctor (CommAlgCat.FiniteEtale.fiber K Omega)

can be proved from the product decomposition of finite etale K-algebras

  Algebra.Etale.iff_exists_algEquiv_prod : Algebra.Etale K A <->
     exists (I : Type) (_ : Finite I) (Ai : I -> Type) (_ : forall i, Field (Ai i))
       (_ : forall i, Algebra K (Ai i)) (e : A =~[K] Prod i, Ai i),
       forall i, Module.Finite K (Ai i) and Algebra.IsSeparable K (Ai i)

(Mathlib/RingTheory/Etale/Field.lean), and in particular report the exact first missing
statement if the decomposition does not suffice.

## Summary of the outcome (honest status)

* Field 1 (preservesTerminalObjects) is proved here, unconditionally and kernel checked
  (no hypotheses beyond K a field, Omega a field with a K-algebra structure).  See
  preservesTerminalObjects below; the key computation is that the fibre of the base field
  F.obj (op K) is the one-point set Hom_K(K, Omega), and that op K is the terminal object of
  (FiniteEtale K)^op.
* The decomposition is restated in the exact form needed downstream (exists_prod_fields),
  kernel checked.
* The algebraic half of Field 3 is proved (HomProdField / homProdField_holds): for a finite
  family of K-algebras A j and a field Omega,
  Hom_K(Prod j, A j, Omega) = Sigma j, Hom_K(A j, Omega).  This is the part of Field 3 that the
  product decomposition does supply; the categorical half (the comparison of colimit cocones)
  is still missing.
* The remaining five fields are NOT proved.  They are recorded below as named Prop-valued
  definitions (PreservesPullbacksField, PreservesFiniteCoproductsField, PreservesEpisField,
  PreservesQuotientsByFiniteGroupsField, ReflectsIsosField) with sorry, each with a docstring
  giving the exact mathematical content and the exact missing input.  The assembly
  fiberFunctorOfFields shows that these five together with field 1 are exactly the contents
  of PreGaloisCategory.FiberFunctor (fiber K Omega); nothing is weakened, added or renamed.

## Why the product decomposition alone does not close the remaining fields

The decomposition A =~[K] Prod i, Ai i with Ai i finite separable fields over K computes the
fibre of an object, and a map out of a finite product of K-algebras into a field Omega factors
through exactly one factor (the idempotent argument behind HomProdField, stated below as an
explicit Prop).  But the remaining fields are not statements about one object:

* preservesPullbacks asks for Hom_K(B (x)_A C, Omega) = Hom_K(B,Omega) x_{Hom_K(A,Omega)}
  Hom_K(C,Omega); the pushout in FiniteEtale K is the tensor product B (x)_A C (S1745), so this
  is the universal property of the tensor product of algebras.  Product decompositions of
  A, B, C do not compute B (x)_A C: the tensor product of two products of fields over a common
  subalgebra is not a product of fields in general.  So the decomposition is not the missing
  input for this field; the missing input is the CommAlgCat-level statement
  Hom(B (x)_A C, Omega) = Hom(B,Omega) x_{Hom(A,Omega)} Hom(C,Omega) together with the
  identification of the pushout cocone in the full subcategory FiniteEtale K.
* preservesFiniteCoproducts asks for Hom_K(Prod j, A j, Omega) = Sigma j, Hom_K(A j, Omega)
  (the finite product in FiniteEtale K is the Pi-algebra, S1745), together with the statement
  that this bijection is the FintypeCat-colimit comparison for the coproduct cocone of the
  opposite category.  The decomposition is the right tool for the algebraic half
  (HomProdField) but not for the categorical half.
* preservesEpis: a monomorphism of (FiniteEtale K)^op is an injective map B -> A of finite etale
  K-algebras; one must show that Hom_K(A, Omega) -> Hom_K(B, Omega) is surjective, i.e. that
  every K-embedding of a finite separable field into Omega extends along an injection of finite
  etale algebras.  This uses that Omega is separably closed and that Omega (x)_K - is exact
  (faithful flatness), which is not a product decomposition statement.
* preservesQuotientsByFiniteGroups: with A^G the fixed point algebra of a finite group action
  (S1770 proves A^G is finite etale and is the limit of the action), the field asks for
  Hom_K(A^G, Omega) = Hom_K(A, Omega)/G.  This needs Omega (x)_K A^G = (Omega (x)_K A)^G
  (fixed points commute with base change to Omega) plus the orbit computation on the Omega-side;
  neither is a product decomposition statement, and neither is in Mathlib.
* reflectsIsos: needs that Omega (x)_K - reflects isomorphisms of finite etale K-algebras
  (descent along the faithfully flat extension K -> Omega), again not a product statement.

So: the exact first missing statement (in the order of the class fields) is
PreservesPullbacksField below.  All five residuals are stated precisely, with the same
quantifiers as the class fields.

## References

* Mathlib, Mathlib/CategoryTheory/Galois/Basic.lean (PreGaloisCategory, FiberFunctor).
* Mathlib, Mathlib/RingTheory/Etale/Finite.lean (CommAlgCat.FiniteEtale.fiber).
* S1745 tmp/sheaf/xif/paper/S1745FiniteEtaleLimitsActual.lean (pullbacks and finite
  coproducts of (FiniteEtale K)^op).
* S1770 tmp/sheaf/xif/paper/S1770FiniteEtaleFixedPointsActual.lean (fixed points, hence
  hasQuotientsByFiniteGroups).
* S1767 tmp/sheaf/xif/paper/S1767FiniteEtaleGaloisNoSorryActual.lean (assembly with the
  six-field residual as an explicit hypothesis).
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.RingTheory.Etale.Field

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1794

variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]

/-! ### 1. The Galois category of finite etale K-algebras and the fibre functor -/

/-- The opposite of the category of finite etale K-algebras: the (pre-)Galois category of
affine finite etale K-schemes.  It is Category.{0, 1}. -/
abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

/-- The geometric fibre functor S |-> Hom_K(S, Omega), Mathlib's
CommAlgCat.FiniteEtale.fiber; no new functor is introduced. -/
abbrev F (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] : C K ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber.{0} K Ω

/-- The base field itself, as an object of the opposite category.  K is initial in
FiniteEtale K, so it is terminal in C K (Lenstra (G1)). -/
abbrev self (K : Type) [Field K] : C K := Opposite.op (CommAlgCat.FiniteEtale.of K K)

section Terminal

/-- Any two morphisms X --> self K agree: after removing the opposites they are two
K-algebra maps out of K. -/
theorem subsingleton_hom_self (X : C K) : Subsingleton (X ⟶ self K) where
  allEq f g := by
    have h : f.unop = g.unop := by
      apply InducedCategory.hom_ext
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _
    exact Quiver.Hom.unop_inj h

instance instSubsingletonHomSelf (X : C K) : Subsingleton (X ⟶ self K) :=
  subsingleton_hom_self K X

/-- The unique morphism X --> self K. -/
instance instUniqueHomSelf (X : C K) : Unique (X ⟶ self K) where
  default := (CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.unop.obj)).op
  uniq f := Subsingleton.allEq f _

/-- K is the terminal object of (FiniteEtale K)^op. -/
def isTerminal_self : IsTerminal (self K) := IsTerminal.ofUnique _

instance instHasTerminal : HasTerminal (C K) := hasTerminal_of_unique (self K)

/-! #### 1.1 Field 1: the fibre functor preserves terminal objects -/

/-- The fibre at the base field is the set of K-algebra maps K --> Omega, a singleton. -/
theorem subsingleton_fiber_self : Subsingleton ↥((F K Ω).obj (self K)) := by
  show Subsingleton ((CommAlgCat.FiniteEtale.of K K).obj →ₐ[K] Ω)
  infer_instance

/-- The fibre at the base field is nonempty: the structure map K --> Omega. -/
theorem nonempty_fiber_self : Nonempty ↥((F K Ω).obj (self K)) := by
  show Nonempty ((CommAlgCat.FiniteEtale.of K K).obj →ₐ[K] Ω)
  exact ⟨Algebra.ofId K Ω⟩

instance instUniqueHomFiberSelf (Y : FintypeCat.{0}) :
    Unique (Y ⟶ (F K Ω).obj (self K)) where
  default := FintypeCat.homMk (fun _ => (nonempty_fiber_self K Ω).some)
  uniq f := by
    ext y
    exact (subsingleton_fiber_self K Ω).allEq _ _

/-- The fibre of the terminal object is a terminal object of FintypeCat. -/
def isTerminal_fiber_self : IsTerminal ((F K Ω).obj (self K)) := IsTerminal.ofUnique _

/-- The same for the chosen terminal object of C K. -/
def isTerminal_fiber_top : IsTerminal ((F K Ω).obj (⊤_ (C K))) :=
  IsTerminal.ofIso (isTerminal_fiber_self K Ω)
    ((F K Ω).mapIso (terminalIsTerminal.uniqueUpToIso (isTerminal_self K)).symm)

/-- **Field 1 of PreGaloisCategory.FiberFunctor (Lenstra (G4), terminal objects).**
The geometric fibre functor preserves terminal objects, hence limits of the empty diagram.

This is unconditional: K is terminal in (FiniteEtale K)^op and Hom_K(K, Omega) is a
singleton. -/
theorem preservesTerminalObjects : PreservesLimit (Functor.empty.{0} (C K)) (F K Ω) :=
  preservesTerminal_of_iso (F K Ω)
    ((isTerminal_fiber_top K Ω).uniqueUpToIso
      (terminalIsTerminal (C := FintypeCat.{0})))

/-- **Field 1, in the shape demanded by the class**: F preserves limits of shape
Discrete PEmpty, i.e. terminal objects. -/
theorem preservesTerminalObjects_pempty :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K Ω) := by
  haveI := preservesTerminalObjects K Ω
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (F K Ω)

end Terminal

/-! ### 2. The product decomposition of finite etale K-algebras -/

/-- **The product decomposition.**  A finite etale K-algebra is the product of finitely many
finite separable field extensions of K.  This is exactly Mathlib's
Algebra.Etale.iff_exists_algEquiv_prod (Mathlib/RingTheory/Etale/Field.lean), with Finite
upgraded to Fintype so that the product can be indexed by a finite type. -/
theorem exists_prod_fields (A : Type) [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.Etale K A] :
    ∃ (I : Type) (_ : Fintype I) (Ai : I → Type) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (e : A ≃ₐ[K] ∀ i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  obtain ⟨I, hI, Ai, hf, hA, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp (inferInstance : Algebra.Etale K A)
  letI : Fintype I := Fintype.ofFinite I
  exact ⟨I, ‹Fintype I›, Ai, hf, hA, e, hsep⟩

/-- The same statement for an object of (FiniteEtale K)^op: its underlying algebra is a
finite product of finite separable fields. -/
theorem exists_prod_fields_obj (X : C K) :
    ∃ (I : Type) (_ : Fintype I) (Ai : I → Type) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (e : X.unop.obj ≃ₐ[K] ∀ i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  exists_prod_fields K X.unop.obj

/-- **The algebraic half of preservesFiniteCoproducts, isolated as an exact Prop.**
For a finite family A : J --> Type of K-algebras and a field Omega, a K-algebra map
Prod j, A j --> Omega factors through exactly one factor: idempotents of a field are 0 or 1
and the images of the orthogonal idempotents Pi.single j 1 sum to 1.

  Hom_K(Prod j, A j, Omega) = Sigma j, Hom_K(A j, Omega).

This is the content of the decomposition for the fibre of one object; it is recorded as a
named Prop because it is not needed for Field 1 and is not by itself one of the six fields
(the categorical comparison for the coproduct cocone is still required). -/
def HomProdField : Prop :=
  ∀ (J : Type) [Fintype J] (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)],
    Nonempty (((∀ j, A j) →ₐ[K] Ω) ≃ (Σ j, (A j →ₐ[K] Ω)))

/-- **Proof of the algebraic half of Field 3 (kernel checked).**  The canonical map
Sigma j, Hom_K(A j, Omega) --> Hom_K(Prod j, A j, Omega) is a bijection, hence
Hom_K(Prod j, A j, Omega) = Sigma j, Hom_K(A j, Omega).

The argument: the images of the orthogonal idempotents Pi.single j 1 in the field Omega are 0
or 1; they sum to 1 and are orthogonal, so exactly one of them is 1; the corresponding
component x |-> phi (Pi.single j x) is a K-algebra homomorphism, and every phi is recovered
from it because phi y = phi y * phi (Pi.single j 1) = phi (Pi.single j (y j)). -/
theorem homProdField_holds : HomProdField K Ω := by
  dsimp only [HomProdField]
  intro J _ A _ _
  classical
  have hidem : ∀ j : J, (Pi.single j (1 : A j) : ∀ i, A i) * Pi.single j (1 : A j)
      = Pi.single j (1 : A j) := by
    intro j
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have horth : ∀ j j' : J, j ≠ j' →
      (Pi.single j (1 : A j) : ∀ i, A i) * Pi.single j' (1 : A j') = 0 := by
    intro j j' hne
    funext i
    by_cases hi : i = j
    · have h2 : Pi.single j' (1 : A j') i = 0 :=
        Pi.single_eq_of_ne (i := j') (i' := i) (fun h => hne (hi.symm.trans h)) (1 : A j')
      simp [hi, h2]
    · have h1 : Pi.single j (1 : A j) i = 0 :=
        Pi.single_eq_of_ne (i := j) (i' := i) hi (1 : A j)
      simp [h1]
  have hsum : (∑ j : J, (Pi.single j (1 : A j) : ∀ i, A i)) = 1 := by
    funext i
    rw [Finset.sum_apply, Pi.one_apply, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      exact Pi.single_eq_of_ne (i := b) (i' := i) (fun h => hb h.symm) (1 : A b)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ φ : (∀ i, A i) →ₐ[K] Ω, ∃! j : J, φ (Pi.single j (1 : A j)) = 1 := by
    intro φ
    have h01 : ∀ j : J, φ (Pi.single j (1 : A j)) = 0 ∨ φ (Pi.single j (1 : A j)) = 1 := by
      intro j
      have hsq : φ (Pi.single j (1 : A j)) * φ (Pi.single j (1 : A j))
          = φ (Pi.single j (1 : A j)) := by
        rw [← map_mul, hidem j]
      have hzero : φ (Pi.single j (1 : A j)) * (φ (Pi.single j (1 : A j)) - 1) = 0 := by
        rw [mul_sub, mul_one, hsq, sub_self]
      rcases mul_eq_zero.mp hzero with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have hsum1 : (∑ j : J, φ (Pi.single j (1 : A j))) = 1 := by
      rw [← map_sum, hsum, map_one]
    have hex : ∃ j : J, φ (Pi.single j (1 : A j)) = 1 := by
      by_contra h
      push Not at h
      have h0 : ∀ j : J, φ (Pi.single j (1 : A j)) = 0 := fun j => (h01 j).resolve_right (h j)
      have : (∑ j : J, φ (Pi.single j (1 : A j))) = 0 := by
        simp only [h0, Finset.sum_const_zero]
      rw [hsum1] at this
      exact one_ne_zero this
    obtain ⟨j₀, hj₀⟩ := hex
    refine ⟨j₀, hj₀, ?_⟩
    intro j hj
    by_contra hne
    have hzero : (Pi.single j (1 : A j) : ∀ i, A i) * Pi.single j₀ (1 : A j₀) = 0 :=
      horth j j₀ hne
    have h1 : φ (Pi.single j (1 : A j)) * φ (Pi.single j₀ (1 : A j₀)) = 0 := by
      rw [← map_mul, hzero, map_zero]
    rw [hj, hj₀, mul_one] at h1
    exact one_ne_zero h1
  -- the index and the component
  let idx : ((∀ i, A i) →ₐ[K] Ω) → J := fun φ => Classical.choose (key φ)
  have idx_spec : ∀ φ : (∀ i, A i) →ₐ[K] Ω,
      φ (Pi.single (idx φ) (1 : A (idx φ))) = 1 := fun φ =>
    (Classical.choose_spec (key φ)).1
  have idx_uniq : ∀ (φ : (∀ i, A i) →ₐ[K] Ω) (j : J),
      φ (Pi.single j (1 : A j)) = 1 → j = idx φ := fun φ j hj =>
    (Classical.choose_spec (key φ)).2 j hj
  let comp : (φ : (∀ i, A i) →ₐ[K] Ω) → (A (idx φ) →ₐ[K] Ω) := fun φ =>
    { toFun := fun x => φ (Pi.single (idx φ) x)
      map_one' := idx_spec φ
      map_mul' := by
        intro x y
        have h : (Pi.single (idx φ) (x * y) : ∀ i, A i)
            = Pi.single (idx φ) x * Pi.single (idx φ) y := by
          funext i
          by_cases hi : i = idx φ
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        rw [h, map_mul]
      map_zero' := by
        have h : (Pi.single (idx φ) (0 : A (idx φ)) : ∀ i, A i) = 0 := by
          funext i
          by_cases hi : i = idx φ
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        rw [h, map_zero]
      map_add' := by
        intro x y
        rw [Pi.single_add, map_add]
      commutes' := by
        intro c
        have h : (Pi.single (idx φ) (algebraMap K (A (idx φ)) c) : ∀ i, A i)
            = Pi.single (idx φ) (1 : A (idx φ)) * algebraMap K (∀ i, A i) c := by
          funext i
          by_cases hi : i = idx φ
          · subst hi; simp
          · simp [Pi.single_eq_of_ne hi]
        rw [h, map_mul, idx_spec φ, one_mul]
        exact φ.commutes c }
  -- the canonical map
  let f : (Σ j, (A j →ₐ[K] Ω)) → ((∀ i, A i) →ₐ[K] Ω) :=
    fun p => p.2.comp (Pi.evalAlgHom K A p.1)
  have hf_inj : Function.Injective f := by
    rintro ⟨j, φ⟩ ⟨j', φ'⟩ h
    have h1 : f ⟨j, φ⟩ (Pi.single j (1 : A j)) = 1 := by
      show φ ((Pi.single j (1 : A j)) j) = 1
      rw [Pi.single_eq_same, map_one]
    have h2 : f ⟨j', φ'⟩ (Pi.single j' (1 : A j')) = 1 := by
      show φ' ((Pi.single j' (1 : A j')) j') = 1
      rw [Pi.single_eq_same, map_one]
    have h3 : f ⟨j', φ'⟩ (Pi.single j (1 : A j)) = 1 := by rw [← h]; exact h1
    have e1 : j = idx (f ⟨j', φ'⟩) := idx_uniq (f ⟨j', φ'⟩) j h3
    have e2 : j' = idx (f ⟨j', φ'⟩) := idx_uniq (f ⟨j', φ'⟩) j' h2
    have hjj : j = j' := e1.trans e2.symm
    subst hjj
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply AlgHom.ext
    intro x
    have hc : φ ((Pi.single j x) j) = φ' ((Pi.single j x) j) :=
      congrArg (fun g => g (Pi.single j x)) h
    simpa using hc
  have hf_surj : Function.Surjective f := by
    intro y
    refine ⟨⟨idx y, comp y⟩, ?_⟩
    apply AlgHom.ext
    intro x
    show (comp y) (x (idx y)) = y x
    have hmul : (x * Pi.single (idx y) (1 : A (idx y)) : ∀ i, A i)
        = Pi.single (idx y) (x (idx y)) := by
      funext i
      by_cases hi : i = idx y
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    calc (comp y) (x (idx y)) = y (Pi.single (idx y) (x (idx y))) := rfl
      _ = y (x * Pi.single (idx y) (1 : A (idx y))) := by rw [hmul]
      _ = y x * y (Pi.single (idx y) (1 : A (idx y))) := by rw [map_mul]
      _ = y x * 1 := by rw [idx_spec y]
      _ = y x := mul_one _
  exact ⟨(Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm⟩

/-! ### 3. The six fields of PreGaloisCategory.FiberFunctor, itemized

Each ...Field below is exactly the corresponding field of
PreGaloisCategory.FiberFunctor (F K Omega) (Mathlib/CategoryTheory/Galois/Basic.lean,
Definition 3.1 of Lenstra's notes), with the same quantifiers.  Field 1 is proved above;
the remaining five are the exact residual. -/

section Fields

variable [hPre : PreGaloisCategory (C K)]

/-- Field 1 (proved, unconditionally): preservation of terminal objects. -/
def PreservesTerminalObjectsField : Prop :=
  PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K Ω)

/-- Field 2 (Lenstra (G4)): preservation of pullbacks. -/
def PreservesPullbacksField : Prop :=
  PreservesLimitsOfShape WalkingCospan (F K Ω)

/-- Field 3 (Lenstra (G5)): preservation of finite coproducts. -/
def PreservesFiniteCoproductsField : Prop :=
  PreservesFiniteCoproducts (F K Ω)

/-- Field 4 (Lenstra (G5)): preservation of epimorphisms. -/
def PreservesEpisField : Prop :=
  Functor.PreservesEpimorphisms (F K Ω)

/-- Field 5 (Lenstra (G5)): preservation of quotients by finite groups. -/
def PreservesQuotientsByFiniteGroupsField : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (F K Ω)

/-- Field 6 (Lenstra (G6)): reflection of isomorphisms. -/
def ReflectsIsosField : Prop :=
  (F K Ω).ReflectsIsomorphisms

/-- Field 1 holds: discharge from the unconditional theorem above. -/
theorem preservesTerminalObjectsField_holds : PreservesTerminalObjectsField K Ω :=
  preservesTerminalObjects_pempty K Ω

/-! #### The five missing fields

These are the exact residuals.  Each is a sorry with the precise statement; the header of
the file explains why the product decomposition does not produce them. -/

/-- **MISSING (first missing).** Field 2: the fibre functor preserves pullbacks.

Concretely, for a cospan B --> A <-- C in FiniteEtale K (i.e. a pullback diagram in
(FiniteEtale K)^op), whose pushout is B (x)_A C (S1745,
S1745.FiniteEtaleClosure.tensorCocone_isColimit), one needs

  Hom_K(B (x)_A C, Omega) = Hom_K(B, Omega) x_{Hom_K(A, Omega)} Hom_K(C, Omega),

the universal property of the tensor product of algebras (Algebra.TensorProduct.liftEquiv),
packaged as preservation of the limit cone under F, together with the identification of the
pushout cocone of the full subcategory FiniteEtale K with the ambient one
(CategoryTheory.Limits.createsColimitFullSubcategoryInclusion').  Nothing here is a product
decomposition statement. -/
theorem preservesPullbacksField_holds : PreservesPullbacksField K Ω := sorry

/-- **MISSING.** Field 3: the fibre functor preserves finite coproducts.

The finite product Prod j, A j in FiniteEtale K is the Pi-algebra (S1745), its opposite is
the coproduct in (FiniteEtale K)^op, and the algebraic input HomProdField K Omega is PROVED in
Section 2 (homProdField_holds).  What is still missing is the categorical half: the bijection
Hom_K(Prod j, A j, Omega) = Sigma j, Hom_K(A j, Omega) must be exhibited as the
FintypeCat-colimit comparison for the coproduct cocone, i.e. one must identify the Pi-cone in
the full subcategory with the ambient product cone and compute its image under the
representable functor A |-> Hom_K(A, Omega).

Note: the empty coproduct (J = Empty) is the initial object of (FiniteEtale K)^op, i.e. the
zero ring; this case is not field 1 (field 1 is the terminal object). -/
theorem preservesFiniteCoproductsField_holds : PreservesFiniteCoproductsField K Ω := sorry

/-- **MISSING.** Field 4: the fibre functor preserves epimorphisms.

A morphism of (FiniteEtale K)^op is an epimorphism iff the corresponding map B --> A of
finite etale K-algebras is a monomorphism, and these are the injective maps.  So one needs:
for B --> A injective, the precomposition map Hom_K(A, Omega) --> Hom_K(B, Omega) is
surjective, i.e. every K-algebra map B --> Omega extends to A --> Omega.  Mathematically this
is: Omega is separably closed and Omega (x)_K - is exact (faithful flatness of the field
extension K --> Omega), so Omega (x)_K B --> Omega (x)_K A is injective and
Hom_K(-, Omega) = PrimeSpectrum(Omega (x)_K -) makes the map surjective on points. -/
theorem preservesEpisField_holds : PreservesEpisField K Ω := sorry

/-- **MISSING.** Field 5: the fibre functor preserves quotients by finite groups.

S1770 proves that for a finite group G acting on a finite etale K-algebra A, the fixed point
algebra A^G is finite etale and the cone with point A^G is the limit of the action diagram in
FiniteEtale K (S1770.invariantsIsLimit), hence the colimit of shape SingleObj G in
(FiniteEtale K)^op.  What is missing is the comparison

  Hom_K(A^G, Omega) = Hom_K(A, Omega)/G  (orbits of the G-action on Omega-points),

which requires Omega (x)_K A^G = (Omega (x)_K A)^G (fixed points commute with base change to
Omega) and the orbit computation for a finite group acting by Omega-algebra automorphisms on
Omega^n.  Neither is in Mathlib, and neither follows from the product decomposition. -/
theorem preservesQuotientsByFiniteGroupsField_holds :
    PreservesQuotientsByFiniteGroupsField K Ω := sorry

/-- **MISSING.** Field 6: the fibre functor reflects isomorphisms.

For f : B --> A in FiniteEtale K such that precomposition Hom_K(A, Omega) --> Hom_K(B, Omega)
is a bijection, one must conclude that f is an isomorphism, i.e. that Omega (x)_K - reflects
isomorphisms of finite etale K-algebras (descent along the faithfully flat extension
K --> Omega).  Not a product decomposition statement. -/
theorem reflectsIsosField_holds : ReflectsIsosField K Ω := sorry

/-! ### 4. Assembly: the five residuals are exactly the class -/

/-- **Assembly.**  The six fields of PreGaloisCategory.FiberFunctor (F K Omega) are precisely
field 1 (proved) plus the five residuals above.  Nothing is weakened, added or renamed: this is
the class with its six fields, in order. -/
theorem fiberFunctorOfFields : PreGaloisCategory.FiberFunctor (F K Ω) where
  preservesTerminalObjects := preservesTerminalObjectsField_holds K Ω
  preservesPullbacks := preservesPullbacksField_holds K Ω
  preservesFiniteCoproducts := preservesFiniteCoproductsField_holds K Ω
  preservesEpis := preservesEpisField_holds K Ω
  preservesQuotientsByFiniteGroups := fun G _ _ =>
    preservesQuotientsByFiniteGroupsField_holds K Ω G
  reflectsIsos := reflectsIsosField_holds K Ω

end Fields

/-! ### 5. Axiom audit

The declarations of Sections 1 and 2 depend only on the three standard axioms.  The five
residual declarations of Section 3 (and hence fiberFunctorOfFields) additionally depend on
sorryAx; this is reported, not hidden. -/

#print axioms S1794.subsingleton_hom_self
#print axioms S1794.isTerminal_self
#print axioms S1794.subsingleton_fiber_self
#print axioms S1794.nonempty_fiber_self
#print axioms S1794.isTerminal_fiber_self
#print axioms S1794.isTerminal_fiber_top
#print axioms S1794.preservesTerminalObjects
#print axioms S1794.preservesTerminalObjects_pempty
#print axioms S1794.exists_prod_fields
#print axioms S1794.exists_prod_fields_obj
#print axioms S1794.homProdField_holds
#print axioms S1794.preservesPullbacksField_holds
#print axioms S1794.preservesFiniteCoproductsField_holds
#print axioms S1794.preservesEpisField_holds
#print axioms S1794.preservesQuotientsByFiniteGroupsField_holds
#print axioms S1794.reflectsIsosField_holds
#print axioms S1794.fiberFunctorOfFields

end S1794