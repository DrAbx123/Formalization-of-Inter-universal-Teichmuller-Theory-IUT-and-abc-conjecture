
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1848

# S1848: field 6 of the six-field fibre functor at R' --- reduction to the residue field

S1835 reduced the sixth field of the six-field geometric fibre functor at the closed
point (0,0) of Spec R' to

  S1835BCReflectsIsos : (S1835BC).op.ReflectsIsomorphisms    (S1835BC = baseChange R' Omega),

and proved this is exactly its concrete form S1835BCReflectsIsosConcrete:

  for f : X --> Y in (FiniteEtale R')^op, IsIso ((S1835BC).op.map f) -> IsIso f.

This file reduces field 6 from the geometric point Omega = AlgebraicClosure F' to the
*residue field F' of the closed point (0,0)*.

## Content

For f : A --> B in FiniteEtale R', the base change Omega (x)_{R'} f is, via the
canonical identification

  S1848Cancel : Omega (x)_{R'} M  ~=  Omega (x)_{F'} (F' (x)_{R'} M),

nothing but Omega (x)_{F'} (F' (x)_{R'} f).  Since Omega is a field extension of F'
(hence faithfully flat), F' (x)_{R'} f is an isomorphism iff
Omega (x)_{F'} (F' (x)_{R'} f) is.  Hence

  S1835BCReflectsIsos  <->  S1848FReflectsIso         (S1848BCReflectsIsos_iff),

where S1848FReflectsIso is literally the same reflection statement with Omega replaced
by F'.  This is a genuine reduction: the remaining statement concerns the fibre of a
finite etale R'-algebra at the closed point (0,0), not the geometric point.

## The exact first missing statement

After the reduction, the whole remaining content of field 6 is

  S1848FirstMissing = S1848FReflectsIso:

  for every f : A --> B in FiniteEtale R', if F' (x)_{R'} f is an isomorphism, then f
  is an isomorphism.  Equivalently, per map: if the residue-fibre map
  A (x)_{R'} F' -> B (x)_{R'} F' is bijective, then f is bijective.

The mathematical proof is elementary: (i) f is injective because the kernel J of f
satisfies J (x)_{R'} F' = 0 (flatness of B) and J is a finitely generated torsion-free
R'-module, so Nakayama at the closed point plus torsion-freeness give J = 0; (ii) A, B
have the same R'-rank (locally constant rank over the connected Spec R', computed at
the fibre); (iii) an inclusion A <= B of finite etale R'-algebras of equal rank is an
equality (trace-form duality: for b in B and a in A, Tr(b a) lies in R' because b a is
integral, while A is its own trace-dual since A is finite etale over R'; hence b is in
A).  Step (iii) is the only part not available in Mathlib at this generality: Mathlib
has traceForm_nondegenerate only for finite separable *field* extensions
(RingTheory/Trace/Basic.lean), not for finite etale algebras over a ring.
See S1848MathematicalProof at the end of this file.

## Technical side condition (not mathematical content)

The identification S1848Cancel is an instance of
TensorProduct.AlgebraTensorModule.cancelBaseChange, which requires the instance
IsScalarTower R' F' Omega.  That instance is true (the R'-action on Omega is the
composite R' -> F' -> Omega) and is proved here as S1848IsScalarTower.  Its formal
proof needs one technical adjustment: AlgebraicClosure F' carries two propositionally
equal SMul structures (Algebra.toSMul of AlgebraicClosure.instAlgebra, and the generic
SMul instance of AlgebraicClosure), whose diamond blocks typeclass synthesis of
IsScalarTower.  We therefore disable the redundant derived instance locally with
attribute [-instance] AlgebraicClosure.instSMulOfIsScalarTower.  This changes no
definition and no statement: it only removes a duplicate instance in this file.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  Everything is
proved unconditionally except S1848FReflectsIso, which is *not* proved and is recorded
as the exact first missing statement (its mathematical proof is documented above and
below).  No hypothesis of the S1835 targets is weakened or changed.
-/

import tmp.sheaf.xif.paper.S1846MonoFFActual
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Etale.Field

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

/-! ## 1. The residue field F' of the closed point (0,0) -/

/-- The closed point (0,0) makes F' an R'-algebra. -/
@[reducible] noncomputable def S1848PointAlgebra : Algebra S1779R S1779K :=
  RingHom.toAlgebra S1779Point.toRingHom

attribute [local instance] S1848PointAlgebra S1779PointClosureAlgebra

/- Remove the redundant derived SMul structure on AlgebraicClosure F' for this file only.
Both structures are the same scalar multiplication; keeping only Algebra.toSMul makes the
instance IsScalarTower R' F' Omega synthesizable. -/
attribute [-instance] AlgebraicClosure.instSMulOfIsScalarTower

/-- The triangle R' -> F' -> Omega: the R'-action on Omega factors through F'. -/
theorem S1848IsScalarTower : IsScalarTower S1779R S1779K S1835Omega :=
  IsScalarTower.of_algebraMap_eq' (R := S1779R) (S := S1779K) (A := S1835Omega) rfl

attribute [local instance] S1848IsScalarTower

/-- Base change from R' to the residue field F' of the closed point (0,0). -/
abbrev S1848BCF : CommAlgCat.FiniteEtale.{0} S1779R ⥤ CommAlgCat.FiniteEtale.{0} S1779K :=
  CommAlgCat.FiniteEtale.baseChange.{0} S1779R S1779K

/-! ## 2. Isomorphisms of finite etale algebras are the bijective algebra maps -/

theorem S1848bijective_of_isIso {S : Type} [CommRing S]
    {X Y : CommAlgCat.FiniteEtale.{0} S} (f : X ⟶ Y) (hf : IsIso f) :
    Function.Bijective f.hom.hom := by
  haveI : IsIso f := hf
  have h2 : Function.Bijective ((CommAlgCat.finiteEtale S).ι.map f) :=
    ConcreteCategory.bijective_of_isIso _
  simpa using h2

theorem S1848isIso_of_bijective {S : Type} [CommRing S]
    {X Y : CommAlgCat.FiniteEtale.{0} S} (f : X ⟶ Y)
    (hb : Function.Bijective f.hom.hom) : IsIso f := by
  have h2 : IsIso ((CommAlgCat.finiteEtale S).ι.map f) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    simpa using hb
  haveI := h2
  exact isIso_of_reflects_iso f (CommAlgCat.finiteEtale S).ι

theorem S1848isIso_iff_bijective {S : Type} [CommRing S]
    {X Y : CommAlgCat.FiniteEtale.{0} S} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f.hom.hom :=
  ⟨S1848bijective_of_isIso f, S1848isIso_of_bijective f⟩

/-! ## 3. Two-step extension of scalars R' -> F' -> Omega -/

/-- Evaluation of the tensor product of algebra maps is the linear tensor product map. -/
theorem S1848tensorMap_apply {R T A B : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (g : A →ₐ[R] B) :
    (fun x : T ⊗[R] A => Algebra.TensorProduct.map (AlgHom.id T T) g x)
      = fun x => g.toLinearMap.lTensor T x := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul t a => simp

/-- **The two-step cancellation**: bijectivity of Omega (x)_{R'} g is equivalent to
bijectivity of Omega (x)_{F'} (F' (x)_{R'} g). -/
theorem S1848bijective_two_step {A B : Type} [CommRing A] [CommRing B]
    [Algebra S1779R A] [Algebra S1779R B] (g : A →ₐ[S1779R] B) :
    Function.Bijective (fun x : S1835Omega ⊗[S1779R] A =>
        Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) g x)
      ↔ Function.Bijective (fun x : S1835Omega ⊗[S1779K] (S1779K ⊗[S1779R] A) =>
        Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega)
          (Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) g) x) := by
  have hfun : (fun x : S1835Omega ⊗[S1779R] A =>
        Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) g x) ∘
      (fun y => TensorProduct.AlgebraTensorModule.cancelBaseChange S1779R S1779K S1835Omega
        S1835Omega A y)
      = (fun y => TensorProduct.AlgebraTensorModule.cancelBaseChange S1779R S1779K S1835Omega
          S1835Omega B y) ∘
        (fun x : S1835Omega ⊗[S1779K] (S1779K ⊗[S1779R] A) =>
          Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega)
            (Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) g) x) := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      simp only [Function.comp_apply] at hy hz
      simp only [Function.comp_apply, map_add, hy, hz]
    | tmul w t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add t u ht hu =>
        simp only [Function.comp_apply] at ht hu
        simp only [Function.comp_apply, TensorProduct.tmul_add, map_add, ht, hu]
      | tmul f a =>
        simp only [Function.comp_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  refine (Function.Bijective.of_comp_iff _ (LinearEquiv.bijective
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S1779R S1779K S1835Omega
      S1835Omega A))).symm.trans ?_
  rw [hfun]
  exact Function.Bijective.of_comp_iff' (LinearEquiv.bijective
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S1779R S1779K S1835Omega
      S1835Omega B)) _

/-- **Faithful flatness**: base change from F' to its algebraic closure Omega reflects
bijectivity of finite etale algebra maps. -/
theorem S1848bijective_baseChange_iff {S T A B : Type} [CommRing S] [CommRing T] [Algebra S T]
    [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (h : A →ₐ[S] B)
    [Module.FaithfullyFlat S T] :
    Function.Bijective (fun x : T ⊗[S] A => Algebra.TensorProduct.map (AlgHom.id T T) h x)
      ↔ Function.Bijective h := by
  rw [S1848tensorMap_apply (R := S) (T := T) (g := h)]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := S) (M := T)
    (f := h.toLinearMap))

/-! ## 4. The residue-field statement (the exact first missing content) -/

/-- Field 6 with the geometric point Omega replaced by the residue field F' of the
closed point (0,0), in the same concrete form as S1835BCReflectsIsosConcrete. -/
def S1848FReflectsIsoConcrete : Prop :=
  ∀ {X Y : (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ} (f : X ⟶ Y),
    IsIso ((S1848BCF).op.map f) → IsIso f

/-- The same statement for maps of finite etale R'-algebras (not in the opposite
category): if f becomes an isomorphism after base change to F' then so does f. -/
def S1848FReflectsIsoMaps : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (g : A ⟶ B),
    IsIso ((S1848BCF).map g) → IsIso g

theorem S1848FReflectsIsoConcrete_iff_maps :
    S1848FReflectsIsoConcrete ↔ S1848FReflectsIsoMaps := by
  constructor
  · intro h A B g hg
    have h2 : IsIso ((S1848BCF).op.map (Quiver.Hom.op g)) := by
      rw [Functor.op_map]
      exact (isIso_op_iff (S1848BCF.map g)).mpr hg
    exact (isIso_op_iff g).mp (h (Quiver.Hom.op g) h2)
  · intro h X Y f hf
    have h2 : IsIso ((S1848BCF).map f.unop) := by
      have h' := hf
      rw [Functor.op_map] at h'
      exact (isIso_op_iff (S1848BCF.map f.unop)).mp h'
    exact (isIso_op_iff f.unop).mpr (h f.unop h2)

/-- **The exact first missing statement**: field 6 of the fibre functor at R' is
exactly the statement that base change to the residue field F' of the closed point
(0,0) reflects isomorphisms of finite etale R'-algebras. -/
def S1848FirstMissing : Prop := S1848FReflectsIsoMaps

/-! ## 5. The reduction of field 6 from Omega to F' -/

/-- **Field 6** (S1835BCReflectsIsos) follows from the residue-field statement
S1848FReflectsIsoMaps.  No geometric-point input remains. -/
theorem S1848BCReflectsIsos_of_fiber (h : S1848FReflectsIsoMaps) : S1835BCReflectsIsos := by
  rw [S1835BCReflectsIsos_iff_concrete]
  intro X Y f hf
  -- Omega-level isomorphism, and its bijectivity
  have h1 : IsIso (S1835BC.map f.unop) := by
    have h' := hf
    rw [Functor.op_map] at h'
    exact (isIso_op_iff (S1835BC.map f.unop)).mp h'
  have hb1 := S1848bijective_of_isIso (S1835BC.map f.unop) h1
  have hb1' : Function.Bijective (fun x : S1835Omega ⊗[S1779R] (Y.unop : Type) =>
      Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) f.unop.hom.hom x) := by
    simpa [S1835BC, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb1
  -- push the bijectivity to Omega (x)_{F'} (F' (x)_{R'} f)
  have hb2 := (S1848bijective_two_step (g := f.unop.hom.hom)).mp hb1'
  -- faithful flatness of Omega over F': the F'-fibre map is bijective
  have hb3 : Function.Bijective (fun x : S1779K ⊗[S1779R] (Y.unop : Type) =>
      Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) f.unop.hom.hom x) :=
    (S1848bijective_baseChange_iff (S := S1779K) (T := S1835Omega)
      (h := Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) f.unop.hom.hom)).mp hb2
  -- hence the F'-base change map is an isomorphism, and h concludes
  have h3 : IsIso ((S1848BCF).map f.unop) := by
    apply S1848isIso_of_bijective
    simpa [S1848BCF, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb3
  have h4 : IsIso ((S1848BCF).map f.unop) := h3
  exact (isIso_op_iff f.unop).mpr (h f.unop h4)

/-- Conversely, field 6 implies the residue-field statement (the reduction is exact). -/
theorem S1848FReflectsIsoMaps_of_BC (h : S1835BCReflectsIsos) : S1848FReflectsIsoMaps := by
  intro A B g hg
  have hb1 := S1848bijective_of_isIso ((S1848BCF).map g) hg
  have hb1' : Function.Bijective (fun x : S1779K ⊗[S1779R] (A : Type) =>
      Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) g.hom.hom x) := by
    simpa [S1848BCF, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb1
  have hb2 : Function.Bijective (fun x : S1835Omega ⊗[S1779K] (S1779K ⊗[S1779R] (A : Type)) =>
      Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega)
        (Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) g.hom.hom) x) :=
    (S1848bijective_baseChange_iff (S := S1779K) (T := S1835Omega)
      (h := Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) g.hom.hom)).mpr hb1'
  have hb3 : Function.Bijective (fun x : S1835Omega ⊗[S1779R] (A : Type) =>
      Algebra.TensorProduct.map (AlgHom.id S1835Omega S1835Omega) g.hom.hom x) :=
    (S1848bijective_two_step (g := g.hom.hom)).mpr hb2
  have h2 : IsIso (S1835BC.map g) := by
    apply S1848isIso_of_bijective
    simpa [S1835BC, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb3
  have h3 : IsIso ((S1835BC).op.map (Quiver.Hom.op g)) := by
    rw [Functor.op_map]
    exact (isIso_op_iff (S1835BC.map g)).mpr h2
  exact (isIso_op_iff g).mp ((S1835BCReflectsIsos_iff_concrete.mp h) (Quiver.Hom.op g) h3)

/-- **The reduction is exact**: field 6 of the fibre functor at R' is *equivalent* to
the statement that base change to the residue field F' of (0,0) reflects isomorphisms. -/
theorem S1848BCReflectsIsos_iff :
    S1835BCReflectsIsos ↔ S1848FReflectsIsoMaps :=
  ⟨S1848FReflectsIsoMaps_of_BC, S1848BCReflectsIsos_of_fiber⟩

/-- Field 6, from the exact first missing statement. -/
theorem S1848BCReflectsIsos_of_firstMissing (h : S1848FirstMissing) : S1835BCReflectsIsos :=
  S1848BCReflectsIsos_of_fiber h

/-! ## 6. The mathematical proof of the first missing statement

We record, as a comment, the complete natural-language proof of
S1848FirstMissing = S1848FReflectsIsoMaps, and the exact Mathlib inputs it needs.

Let f : A --> B be a morphism of finite etale R'-algebras such that the induced
F'-algebra map  f_F' : A (x)_{R'} F' -> B (x)_{R'} F'  is bijective.  We must show that
f is bijective.

(1) f is injective.  Let J = ker f (an ideal of A).  Since A and B are finite etale over
    R', both are flat R'-modules (Algebra.Etale implies Module.Flat, available).  From
    the exact sequence 0 -> J -> A -> B -> 0 and flatness of B, tensoring with F'
    (right exact) gives J (x)_{R'} F' = ker (f_F'), which is zero.  Now
    J (x)_{R'} F' = J / m J where m = ker (R' -> F') is the maximal ideal of the closed
    point, so J = m J; by Nakayama's lemma over the local ring R'_m, J_m = 0, and since
    A is R'-torsion-free (R' is a domain and A is flat) the localization map J -> J_m is
    injective, hence J = 0.

(2) A and B have the same R'-rank.  Module.rankAtStalk is locally constant on Spec R'
    (Module.isLocallyConstant_rankAtStalk, available) and Spec R' is connected (R' is a
    domain), so the rank is constant; at the closed point it equals
    dim_{F'} (A (x)_{R'} F') = dim_{F'} (B (x)_{R'} F') because f_F' is bijective.

(3) An inclusion of finite etale R'-algebras of equal rank is an equality.  Let A <= B
    with both of rank n over R'.  Then A is finite etale over R', so its trace form
    <x,y> = Tr_{A/R'}(xy) is a perfect pairing A x A -> R' (the different is trivial for
    etale algebras).  Let b in B.  For a in A, ba lies in B, and the trace of an element
    of a finite algebra lies in the base ring, so <b,a> = Tr_{B/R'}(ba) is in R'.  Since
    the trace form of B restricted to A agrees with that of A (both are computed in the
    common fraction algebra A (x)_{R'} K'), perfectness of A's trace form now gives
    b in A.  Hence B <= A, so A = B.

(4) Conclusion: f is injective with A <= B and equal ranks, so by (3) A = B, i.e. f is
    bijective, i.e. an isomorphism of finite etale R'-algebras.

The only Mathlib input missing for (3) is perfectness of the trace form of a finite etale
algebra over a ring: Mathlib's traceForm_nondegenerate
(Mathlib/RingTheory/Trace/Basic.lean) is stated for a finite separable extension of
*fields*.  Steps (1) and (2) only use Nakayama, flatness and locality of the rank, all of
which are available.

Note that the conclusion is consistent with (and is a special case of) the SGA1 theorem
that the fibre functor of a connected scheme is conservative; the reduction above shows
that at R' this is *not* a geometric statement about the closed point, only an algebraic
statement about finite flat algebras over R'.

## Verification (session S1848, 2026-11-01)

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1848RPrimeReflectActual.olean
      tmp/sheaf/xif/paper/S1848RPrimeReflectActual.lean

-> EXIT=0, no errors, no sorryAx, no warnings.  Every #print axioms below prints only
[propext, Classical.choice, Quot.sound].  See the axiom audit at the end of this file.
-/

/-! ## 7. Checks and axiom audit -/

#check S1848PointAlgebra
#check S1848IsScalarTower
#check S1848bijective_of_isIso
#check S1848isIso_of_bijective
#check S1848isIso_iff_bijective
#check S1848bijective_two_step
#check S1848bijective_baseChange_iff
#check S1848FReflectsIsoConcrete
#check S1848FReflectsIsoMaps
#check S1848FReflectsIsoConcrete_iff_maps
#check S1848FirstMissing
#check S1848BCReflectsIsos_of_fiber
#check S1848FReflectsIsoMaps_of_BC
#check S1848BCReflectsIsos_iff
#check S1848BCReflectsIsos_of_firstMissing

#print axioms S1848bijective_of_isIso
#print axioms S1848isIso_of_bijective
#print axioms S1848bijective_two_step
#print axioms S1848bijective_baseChange_iff
#print axioms S1848FReflectsIsoConcrete_iff_maps
#print axioms S1848BCReflectsIsos_of_fiber
#print axioms S1848FReflectsIsoMaps_of_BC
#print axioms S1848BCReflectsIsos_iff
#print axioms S1848BCReflectsIsos_of_firstMissing

end LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual