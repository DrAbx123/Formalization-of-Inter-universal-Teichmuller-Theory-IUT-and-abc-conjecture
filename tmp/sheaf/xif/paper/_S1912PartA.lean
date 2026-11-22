/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1912

# S1912: the equal-rank inclusion via the trace-dual retraction

S1849 isolated the trace-form input of the S1848 route as

  S1849EqualRankInclusion:
    an injective map of finite etale R'-algebras whose ranks at every prime agree
    is surjective.

S1860 proved trace duality for finite projective etale algebras.  This file gives the
route requested for S1912, which avoids the normal-domain integral-closedness step:

  A --i--> B, equal rank
    => after K = Frac(R'), i_K : A_K --> B_K is an injective map of equidimensional
       finite-dimensional K-vector spaces, hence bijective;
    => Tr_B(i a) = Tr_A(a) for all a : A, by base change to K and invariance of the
       trace under the resulting algebra equivalence A_K = B_K;
    => trace duality on A produces a linear retraction psi : B --> A with
       psi (i a) = a;
    => B = A + ker psi, and ker psi is a direct summand of B, hence finite flat;
    => rank additivity at every prime, together with the equal-rank hypothesis, gives
       rank (ker psi) = 0 at every prime;
    => a finite flat module of rank zero at every prime is subsingleton, so
       ker psi = 0;
    => psi is injective, and psi (i a) = a makes i surjective.

No normal-domain integral closedness is used.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  Everything
asserted as a theorem is proved.  The only external mathematical input is trace duality
S1859ProjectiveTraceDuality_proof, proved in S1860.
-/

import tmp.sheaf.xif.paper.S1860TraceDualityActual
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
open scoped TensorProduct
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual
open LeanFormal.IUT.XiFPaper.S1860TraceDualityActual

set_option autoImplicit false

/-! ## 1. The generic point and its residue field -/

/-- The localisation of R' at the generic point of Spec R'. -/
abbrev S1912K : Type := Localization.AtPrime (⊥ : Ideal S1779R)

instance S1912K_isFractionRing : IsFractionRing S1779R S1912K := by
  simpa [Ideal.primeCompl_bot] using
    (Localization.isLocalization (M := (⊥ : Ideal S1779R).primeCompl))

instance S1912K_field : Field S1912K := by
  haveI : IsDomain S1779R := S1849_isDomain
  exact IsFractionRing.toField S1779R

theorem S1912K_algebraMap_injective : Function.Injective (algebraMap S1779R S1912K) :=
  IsFractionRing.injective S1779R S1912K

theorem S1912K_flat : Module.Flat S1779R S1912K :=
  IsLocalization.flat S1912K (⊥ : Ideal S1779R).primeCompl

/-! ## 2. Trace duality as a linear equivalence -/

/-- Trace duality, bundled as a linear equivalence A ~= A^*. -/
noncomputable def traceDualEquiv (A : CommAlgCat.FiniteEtale.{0} S1779R)
    [Module.Projective S1779R (A : Type)] :
    (A : Type) ≃ₗ[S1779R] ((A : Type) →ₗ[S1779R] S1779R) := by
  refine LinearEquiv.ofBijective
    (projectiveTraceForm (R := S1779R) (A := (A : Type))) ?_
  constructor
  · intro a1 a2 h
    obtain ⟨a, -, huniq⟩ :=
      S1859ProjectiveTraceDuality_proof A inferInstance
        (projectiveTraceForm (R := S1779R) (A := (A : Type)) a1)
    have ha1 : ∀ b : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b =
          projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b :=
      fun _ => rfl
    have ha2 : ∀ b : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) a2 b =
          projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b := by
      intro b
      exact (congrArg (fun φ : (A : Type) →ₗ[S1779R] S1779R => φ b) h).symm
    exact (huniq a1 ha1).trans (huniq a2 ha2).symm
  · intro φ
    obtain ⟨a, ha, -⟩ := S1859ProjectiveTraceDuality_proof A inferInstance φ
    refine ⟨a, ?_⟩
    ext b
    exact ha b

/-! ## 3. The trace functional and the retraction -/

section Retraction

variable {A B : CommAlgCat.FiniteEtale.{0} S1779R}
variable [Module.Projective S1779R (A : Type)] [Module.Projective S1779R (B : Type)]

/-- The functional on A induced by an element of B and an algebra map A -> B. -/
noncomputable def traceFunctional (f : A ⟶ B) :
    (B : Type) →ₗ[S1779R] ((A : Type) →ₗ[S1779R] S1779R) :=
  (LinearMap.lcomp S1779R S1779R f.hom.hom.toLinearMap).comp
    (projectiveTraceForm (R := S1779R) (A := (B : Type)))

@[simp]
lemma traceFunctional_apply (f : A ⟶ B) (b : (B : Type)) (a : (A : Type)) :
    traceFunctional f b a =
      projectiveTraceForm (R := S1779R) (A := (B : Type)) b (f.hom.hom a) := by
  simp [traceFunctional, LinearMap.lcomp_apply]

/-- The trace-dual retraction B -> A. -/
noncomputable def retraction (f : A ⟶ B) : (B : Type) →ₗ[S1779R] (A : Type) :=
  (traceDualEquiv A).symm.toLinearMap.comp (traceFunctional f)

/-- The defining property of the retraction: it represents the functional
a |-> Tr_B (b * f a) with respect to the trace form of A. -/
lemma retraction_spec (f : A ⟶ B) (b : (B : Type)) (a : (A : Type)) :
    projectiveTraceForm (R := S1779R) (A := (A : Type)) (retraction f b) a =
      projectiveTraceForm (R := S1779R) (A := (B : Type)) b (f.hom.hom a) := by

end Retraction

end LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual
