import tmp.sheaf.xif.paper.S1853TraceFormActual
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange

/-!
# S1858: the global trace form of finite etale R'-algebras --- what holds, what is missing

S1853 proved that the trace form of a finite etale algebra over a *local* ring is
nondegenerate (traceForm_nondegenerate_of_isLocalRing) and isolated the global statement
S1853GlobalTracePerfect.  This file settles the global statement.

## The finding

S1853GlobalTracePerfect is *not* the local-to-global assembly that S1853 assumed it to be.
Mathlib's LinearMap.trace is defined as

    if H : exists s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

so Algebra.trace R S --- and hence Algebra.traceForm R S --- is *junk zero* whenever S has no
finite R-basis (section 1).  Consequently:

* over a finite etale A that is not a free R'-module, Algebra.traceForm R' A = 0, and a
  nondegenerate zero form forces Subsingleton A;
* therefore S1853GlobalTracePerfect is *equivalent* to: every finite etale R'-algebra is free
  as an R'-module, or the zero ring (S1853GlobalTracePerfect_iff_free_or_subsingleton);
* and it is *false* as soon as some nontrivial finite etale R'-algebra is not free
  (not_S1853GlobalTracePerfect_of_nonfree).  Only the existence of such an algebra is not
  formalised here: over a curve with nontrivial finite etale covers such algebras exist, e.g.
  O + L for a nontrivial 2-torsion line bundle L, or more generally pushforward of the
  structure sheaf along a nontrivial finite etale cover.

So the missing local-to-global assembly is in fact missing at the level of the *definition* of
the trace, not at the level of a commutative-algebra lemma.

## What is proved here

1. The free case of global trace perfectness (traceForm_nondegenerate_of_free): for a finite
   etale R'-algebra which *is* a free R'-module the trace form is nondegenerate.  The
   local-to-global assembly which S1853 expected to be the hard step is carried out in full:
   localisation compatibility of the trace matrix
   (Algebra.traceMatrix_localizationLocalization), nondegeneracy of the trace form of the
   localised algebra at every maximal ideal (S1853's local theorem, in the unit-determinant
   form isUnit_det_traceMatrix_of_isLocalRing), and the unit criterion
   isUnit_of_forall_isUnit_algebraMap_atPrime.

2. Pointwise (local) perfectness, unconditionally (S1858GlobalTracePerfectLocal): for every
   finite etale R'-algebra A and every maximal ideal p of R', the trace form of the R'_p
   algebra R'_p x A is nondegenerate.  This is the strongest statement about the trace form
   that is true without a projectivity hypothesis on a global form.

3. The exact missing input (S1858ProjectiveTraceGluing): a bilinear form on each finite etale
   R'-algebra whose localisation at every maximal ideal is the trace form of the (free)
   localised algebra --- i.e. a trace form for finite *projective* modules together with its
   localisation compatibility.  It is inhabited in the free case
   (S1858ProjectiveTraceGluing_of_free, via Algebra.trace_localization), so it is not vacuous;
   Mathlib 4.32.2 has no Module.Projective trace, which is exactly why it cannot be discharged
   for non-free A.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.
S1858ProjectiveTraceGluing is a plain Prop definition with no inhabitant, and it is only used
as an explicit hypothesis/interface, never as an assumption in the proof of an unconditional
statement.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 20
set_option linter.unusedSectionVars false
open scoped TensorProduct
open scoped Matrix
open LinearMap

/-! Two Mathlib-side idioms are used below: the R'-algebra structure of a localisation at a
prime (automatic), and the A-algebra structure on Rm x[R] A (rightAlgebra, which Mathlib
deliberately keeps out of the global instance pool). -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace LeanFormal.IUT.XiFPaper.S1858GlobalTraceActual

open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1853TraceFormActual
/-! ## 1. Mathlib's trace is zero on algebras without a finite basis -/

/-- If S has no finite R-basis, Mathlib's trace is junk zero on S. -/
theorem trace_eq_zero_of_not_exists_basis {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : ¬ ∃ s : Finset S, Nonempty (Module.Basis s R S)) : Algebra.trace R S = 0 :=
  Algebra.trace_eq_zero_of_not_exists_basis R h

/-- Hence the trace form is identically zero. -/
theorem traceForm_eq_zero_of_not_exists_basis {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : ¬ ∃ s : Finset S, Nonempty (Module.Basis s R S)) :
    Algebra.traceForm R S = 0 := by
  ext x y
  rw [Algebra.traceForm_apply, trace_eq_zero_of_not_exists_basis h]
  simp

/-- A nondegenerate zero form forces the module to be a subsingleton. -/
theorem subsingleton_of_traceForm_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h0 : Algebra.traceForm R S = 0) (hnd : (Algebra.traceForm R S).Nondegenerate) :
    Subsingleton S := by
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := hnd.1 a fun y => by rw [h0]; simp
  have hb : b = 0 := hnd.1 b fun y => by rw [h0]; simp
  rw [ha, hb]

/-! ## 2. Units are local at the maximal ideals -/

/-- An element of a commutative ring is a unit as soon as its image in every localisation at a
prime ideal is a unit. -/
theorem isUnit_of_forall_isUnit_algebraMap_atPrime {R : Type*} [CommRing R] (x : R)
    (h : ∀ (p : Ideal R) [p.IsPrime], IsUnit (algebraMap R (Localization.AtPrime p) x)) :
    IsUnit x := by
  by_contra hx
  have hne : Ideal.span {x} ≠ ⊤ := Ideal.span_singleton_eq_top.not.mpr hx
  obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal (Ideal.span {x}) hne
  haveI : m.IsMaximal := hm_max
  have hx_mem : x ∈ m := hm_le (Ideal.subset_span rfl)
  have hmem : algebraMap R (Localization.AtPrime m) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m]
    exact Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) hx_mem
  exact (IsLocalRing.notMem_maximalIdeal.mpr (h m)) hmem

/-! ## 3. Unit determinant of the trace matrix over a local ring

This is the carrier of S1853's local theorem: its proof concludes that the determinant of the
trace matrix is a unit, and nondegeneracy is then a matrix-inversion step.  Extracting the unit
statement makes the localisation argument of section 4 possible. -/

theorem isUnit_det_traceMatrix_of_isLocalRing
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing R]
    [Module.Finite R A] [Algebra.Etale R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    IsUnit (Algebra.traceMatrix R b).det := by
  classical
  letI : Module.Free R A := Module.Free.of_basis b
  have hfield : (Algebra.traceForm (R ⧸ IsLocalRing.maximalIdeal R)
      (A ⧸ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R))).Nondegenerate :=
    traceForm_residue_nondegenerate
  have hdet : (Algebra.traceMatrix (R ⧸ IsLocalRing.maximalIdeal R)
      (IsLocalRing.basisQuotient b)).det ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (IsLocalRing.basisQuotient b)).mp hfield
    simpa [Algebra.traceMatrix_of_basis] using this
  have hdet' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) ((Algebra.traceMatrix R b).det) ≠ 0 := by
    rw [traceMatrix_quotient b] at hdet
    simpa [RingHom.map_det] using hdet
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hdet' (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

/-! ## 4. Localisation compatibility of the trace matrix, at a prime of R' -/

/-- The image of the determinant of the trace matrix of A in R'_p is a unit.  This is where the
local-to-global assembly happens: over the local ring R'_p the trace form of the (free) localised
algebra has unit determinant by section 3, and the trace matrix of the localised algebra is the
localisation of the trace matrix of A. -/
theorem isUnit_algebraMap_det_traceMatrix_atPrime
    (A : CommAlgCat.FiniteEtale.{0} S1779R)
    (p : Ideal S1779R) [p.IsPrime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S1779R (A : Type)) :
    IsUnit (algebraMap S1779R (Localization.AtPrime p) (Algebra.traceMatrix S1779R b).det) := by
  haveI : IsLocalRing (Localization.AtPrime p) := inferInstance
  haveI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) :=
    inferInstance
  haveI : Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) :=
    inferInstance
  have hun : IsUnit (Algebra.traceMatrix (Localization.AtPrime p)
      (b.localizationLocalization (Localization.AtPrime p) p.primeCompl
        (Localization.AtPrime p ⊗[S1779R] (A : Type)))).det :=
    isUnit_det_traceMatrix_of_isLocalRing _
  have hmat : Algebra.traceMatrix (Localization.AtPrime p)
      (b.localizationLocalization (Localization.AtPrime p) p.primeCompl
        (Localization.AtPrime p ⊗[S1779R] (A : Type))) =
      (algebraMap S1779R (Localization.AtPrime p)).mapMatrix (Algebra.traceMatrix S1779R b) :=
    Algebra.traceMatrix_localizationLocalization S1779R p.primeCompl
      (Localization.AtPrime p ⊗[S1779R] (A : Type)) b
  rw [hmat, ← RingHom.map_det] at hun
  exact hun

/-! ## 5. Global trace perfectness for free finite etale algebras -/

/-- The local-to-global assembly, in the free case.  For a finite etale R'-algebra which is free
as an R'-module, the trace form is nondegenerate.  (No hypothesis on the localised algebras is
needed: they are free automatically because R'_p is local.) -/
theorem traceForm_nondegenerate_of_free (A : CommAlgCat.FiniteEtale.{0} S1779R)
    [Module.Free S1779R (A : Type)] :
    (Algebra.traceForm S1779R (A : Type)).Nondegenerate := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex S1779R (A : Type)) S1779R (A : Type) :=
    Module.Free.chooseBasis S1779R (A : Type)
  letI : DecidableEq (Module.Free.ChooseBasisIndex S1779R (A : Type)) := Classical.decEq _
  have hunit : IsUnit (Algebra.traceMatrix S1779R b).det := by
    apply isUnit_of_forall_isUnit_algebraMap_atPrime
    intro p hp
    exact isUnit_algebraMap_det_traceMatrix_atPrime A p b
  have hunit' : IsUnit ((LinearMap.BilinForm.toMatrix b) (Algebra.traceForm S1779R (A : Type))).det := by
    simpa [Algebra.traceMatrix_of_basis] using hunit
  exact nondegenerate_of_isUnit_det b (Algebra.traceForm S1779R (A : Type)) hunit'
/-! ## 6. The literal target, characterised -/

/-- Characterisation of the literal target.  S1853GlobalTracePerfect says exactly that every
finite etale R'-algebra is free as an R'-module or is the zero ring; it is a statement about
freeness, not a local-to-global statement about trace forms. -/
theorem S1853GlobalTracePerfect_iff_free_or_subsingleton :
    S1853GlobalTracePerfect ↔ ∀ A : CommAlgCat.FiniteEtale.{0} S1779R,
      (∃ s : Finset (A : Type), Nonempty (Module.Basis s S1779R (A : Type))) ∨
        Subsingleton (A : Type) := by
  constructor
  · intro h A
    by_cases hb : ∃ s : Finset (A : Type), Nonempty (Module.Basis s S1779R (A : Type))
    · exact Or.inl hb
    · exact Or.inr
        (subsingleton_of_traceForm_eq_zero (traceForm_eq_zero_of_not_exists_basis hb) (h A))
  · intro h A
    rcases h A with ⟨s, ⟨b⟩⟩ | hs
    · letI : Module.Free S1779R (A : Type) := Module.Free.of_basis b
      exact traceForm_nondegenerate_of_free A
    · exact ⟨fun x _ => Subsingleton.elim x 0, fun y _ => Subsingleton.elim y 0⟩

/-- The literal target fails as soon as one nontrivial finite etale R'-algebra is not free.
(Whether such an algebra exists over this particular R' is not settled here; over a curve with
nontrivial finite etale covers it does.) -/
theorem not_S1853GlobalTracePerfect_of_nonfree
    (A : CommAlgCat.FiniteEtale.{0} S1779R) (hA : Nontrivial (A : Type))
    (h : ¬ ∃ s : Finset (A : Type), Nonempty (Module.Basis s S1779R (A : Type))) :
    ¬ S1853GlobalTracePerfect := by
  intro hperf
  have hsub : Subsingleton (A : Type) :=
    subsingleton_of_traceForm_eq_zero (traceForm_eq_zero_of_not_exists_basis h) (hperf A)
  obtain ⟨a, b, hab⟩ := hA
  exact hab (Subsingleton.elim a b)

/-- The trace-duality form of the target fails under the same hypothesis. -/
theorem not_S1853GlobalTraceDuality_of_nonfree
    (A : CommAlgCat.FiniteEtale.{0} S1779R) (hA : Nontrivial (A : Type))
    (h : ¬ ∃ s : Finset (A : Type), Nonempty (Module.Basis s S1779R (A : Type))) :
    ¬ S1853GlobalTraceDuality :=
  fun hd => not_S1853GlobalTracePerfect_of_nonfree A hA h (S1853GlobalTracePerfect_of_duality hd)

/-! ## 7. What is true unconditionally: pointwise perfectness -/

/-- Pointwise trace perfectness.  For every finite etale R'-algebra A and every maximal ideal p of
R', the trace form of the R'_p-algebra R'_p x[R'] A is nondegenerate.  This is unconditional and
is the strongest true statement available with Mathlib's trace API: the localised algebra is free
over the local ring R'_p, so S1853's local theorem applies. -/
def S1858GlobalTracePerfectLocal : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R) (p : Ideal S1779R) [p.IsPrime], p.IsMaximal →
    (Algebra.traceForm (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[S1779R] (A : Type))).Nondegenerate

/-- Pointwise trace perfectness holds. -/
theorem S1858GlobalTracePerfectLocal_proof : S1858GlobalTracePerfectLocal := by
  intro A p hp hmax
  haveI : p.IsMaximal := hmax
  haveI : IsLocalRing (Localization.AtPrime p) := inferInstance
  haveI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) :=
    inferInstance
  haveI : Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) :=
    inferInstance
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[S1779R] (A : Type)) :=
    Module.free_of_flat_of_isLocalRing
  exact traceForm_nondegenerate_of_isLocalRing

/-! ## 8. The exact missing input -/

/-- The exact missing input (S1858).  For every finite etale R'-algebra A there is a single
bilinear form on A whose localisation at every maximal ideal p of R' is the trace form of the
(automatically free) R'_p-algebra R'_p x[R'] A.

This is a trace form for finite *projective* modules together with its localisation
compatibility.  It is available for free A (S1858ProjectiveTraceGluing_of_free, where the form is
Algebra.traceForm), but it cannot be instantiated for general A from Mathlib 4.32.2:
Algebra.trace is defined through a basis and is junk zero without one (section 1), and
Algebra.trace_localization requires Module.Free R S.  A genuine Module.Projective trace
(dual-basis trace of an endomorphism) is what is missing. -/
def S1858ProjectiveTraceGluing : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R),
    ∃ T : LinearMap.BilinForm S1779R (A : Type),
      ∀ (p : Ideal S1779R) [p.IsPrime], p.IsMaximal → ∀ x y : (A : Type),
        algebraMap S1779R (Localization.AtPrime p) (T x y) =
          Algebra.traceForm (Localization.AtPrime p)
            (Localization.AtPrime p ⊗[S1779R] (A : Type))
            (1 ⊗ₜ[S1779R] x) (1 ⊗ₜ[S1779R] y)

/-- The missing input is not vacuous: in the free case it is satisfied by Algebra.traceForm, by
localisation compatibility of the trace (Algebra.trace_localization). -/
theorem S1858ProjectiveTraceGluing_of_free (A : CommAlgCat.FiniteEtale.{0} S1779R)
    [Module.Free S1779R (A : Type)] :
    ∃ T : LinearMap.BilinForm S1779R (A : Type),
      ∀ (p : Ideal S1779R) [p.IsPrime], p.IsMaximal → ∀ x y : (A : Type),
        algebraMap S1779R (Localization.AtPrime p) (T x y) =
          Algebra.traceForm (Localization.AtPrime p)
            (Localization.AtPrime p ⊗[S1779R] (A : Type))
            (1 ⊗ₜ[S1779R] x) (1 ⊗ₜ[S1779R] y) := by
  refine ⟨Algebra.traceForm S1779R (A : Type), ?_⟩
  intro p hp hmax x y
  haveI : p.IsMaximal := hmax
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  have h1 : (1 ⊗ₜ[S1779R] x) * (1 ⊗ₜ[S1779R] y) =
      algebraMap (A : Type) (Localization.AtPrime p ⊗[S1779R] (A : Type)) (x * y) := by
    rw [map_mul, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.right_algebraMap_apply]
  rw [h1]
  exact (Algebra.trace_localization S1779R p.primeCompl (x * y)).symm

/-! ## 9. Formal checks -/

#check trace_eq_zero_of_not_exists_basis
#check traceForm_eq_zero_of_not_exists_basis
#check subsingleton_of_traceForm_eq_zero
#check isUnit_of_forall_isUnit_algebraMap_atPrime
#check isUnit_det_traceMatrix_of_isLocalRing
#check isUnit_algebraMap_det_traceMatrix_atPrime
#check traceForm_nondegenerate_of_free
#check S1853GlobalTracePerfect_iff_free_or_subsingleton
#check not_S1853GlobalTracePerfect_of_nonfree
#check not_S1853GlobalTraceDuality_of_nonfree
#check S1858GlobalTracePerfectLocal
#check S1858GlobalTracePerfectLocal_proof
#check S1858ProjectiveTraceGluing
#check S1858ProjectiveTraceGluing_of_free

#print axioms trace_eq_zero_of_not_exists_basis
#print axioms traceForm_eq_zero_of_not_exists_basis
#print axioms subsingleton_of_traceForm_eq_zero
#print axioms isUnit_of_forall_isUnit_algebraMap_atPrime
#print axioms isUnit_det_traceMatrix_of_isLocalRing
#print axioms isUnit_algebraMap_det_traceMatrix_atPrime
#print axioms traceForm_nondegenerate_of_free
#print axioms S1853GlobalTracePerfect_iff_free_or_subsingleton
#print axioms not_S1853GlobalTracePerfect_of_nonfree
#print axioms not_S1853GlobalTraceDuality_of_nonfree
#print axioms S1858GlobalTracePerfectLocal_proof
#print axioms S1858ProjectiveTraceGluing_of_free

end LeanFormal.IUT.XiFPaper.S1858GlobalTraceActual
