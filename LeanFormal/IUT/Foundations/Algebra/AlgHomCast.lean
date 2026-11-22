import Mathlib.Algebra.Algebra.Hom

/-!
# Explicit casts for algebra homomorphisms over dependent families

This file provides reducible domain/codomain casts for `AlgHom` when the
source or target family is indexed by a type with an equality of indices.
The point is to avoid the opaque `AlgEquiv.cast` path in dependent contexts:
the definition is an explicit `cast` of the function type, and the `_apply`
lemmas reduce an application to the expected coerced argument/value by
`cases h; rfl`.  These are the utilities used to prove identity laws for the
orbit fixed-field maps in the IUT Example 3.6 assembly.
-/

universe u v

namespace AlgHom

variable {R : Type u} [CommSemiring R]

section Domain

variable {ι : Type v} {A : ι → Type u}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  {F : Type u} [Semiring F] [Algebra R F]

/-- Cast the domain of an `AlgHom` along an equality of indices.  The
definition is an explicit `cast` of the function type (reducible), so that
`castDomain_apply` can reduce it by `cases h`. -/
abbrev castDomain {i j : ι} (h : i = j) (f : A i →ₐ[R] F) : A j →ₐ[R] F :=
  cast (congrArg (fun k => A k →ₐ[R] F) h) f

@[simp] theorem castDomain_rfl {i : ι} (f : A i →ₐ[R] F) :
    castDomain (A := A) (F := F) rfl f = f := rfl

/-- Application lemma for `castDomain`: the transported map applies the
original map to the argument cast back along `h.symm`. -/
@[simp] theorem castDomain_apply {i j : ι} (h : i = j) (f : A i →ₐ[R] F)
    (a : A j) :
    castDomain (A := A) (F := F) h f a =
      f (cast (congrArg A h.symm) a) := by
  cases h
  rfl

end Domain

section Codomain

variable {ι : Type v} {A : ι → Type u}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  {G : Type u} [Semiring G] [Algebra R G]

/-- Cast the codomain of an `AlgHom` along an equality of indices. -/
abbrev castCodomain {i j : ι} (h : i = j) (f : G →ₐ[R] A i) : G →ₐ[R] A j :=
  cast (congrArg (fun k => G →ₐ[R] A k) h) f

@[simp] theorem castCodomain_rfl {i : ι} (f : G →ₐ[R] A i) :
    castCodomain (A := A) (G := G) rfl f = f := rfl

/-- Application lemma for `castCodomain`: the transported map applies the
original map and casts the resulting value. -/
@[simp] theorem castCodomain_apply {i j : ι} (h : i = j) (f : G →ₐ[R] A i)
    (a : G) :
    castCodomain (A := A) (G := G) h f a =
      cast (congrArg A h) (f a) := by
  cases h
  rfl

end Codomain

end AlgHom
