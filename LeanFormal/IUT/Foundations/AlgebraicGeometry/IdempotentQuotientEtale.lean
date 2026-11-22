import Mathlib

/-!
# Idempotent quotient is finite etale

For an idempotent e : S, the quotient S / (1 - e) is the away localization S_e,
hence finite etale over S.  This is the per-corner finite-etale fact used by M2.
-/

open Polynomial

universe u

namespace IdempotentQuotientEtale

variable {S : Type u} [CommRing S] {e : S} (he : IsIdempotentElem e)

/-- The idempotent quotient S / (1 - e). -/
abbrev quotient : Type u := S ⧸ Ideal.span ({1 - e} : Set S)

/-- The quotient by (1 - e) is the away localization at the idempotent e. -/
theorem isLocalizationAway (he : IsIdempotentElem e) :
    IsLocalization.Away e (quotient (e := e)) :=
  IsLocalization.away_of_isIdempotentElem he
    (by
      change RingHom.ker (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set S))) =
        Ideal.span ({1 - e} : Set S)
      exact Ideal.mk_ker)
    (by
      change Function.Surjective ⇑(Ideal.Quotient.mk (Ideal.span ({1 - e} : Set S)))
      exact Ideal.Quotient.mk_surjective)

/-- The idempotent quotient is finite over S. -/
theorem moduleFinite : Module.Finite S (quotient (e := e)) :=
  Module.Finite.quotient S (Ideal.span ({1 - e} : Set S) : Submodule S S)

/-- The idempotent quotient is projective over S. -/
theorem moduleProjective (he : IsIdempotentElem e) :
    Module.Projective S (quotient (e := e)) := by
  let I : Ideal S := Ideal.span ({1 - e} : Set S)
  have hker : (I : Submodule S S) ≤ (LinearMap.mulLeft S e).ker := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change e * (1 - e) = 0
    exact he.mul_one_sub_self
  let i : quotient (e := e) →ₗ[S] S :=
    Submodule.liftQ (I : Submodule S S) (LinearMap.mulLeft S e) hker
  let s : S →ₗ[S] quotient (e := e) := Submodule.mkQ (I : Submodule S S)
  refine Module.Projective.of_split i s ?_
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I : Submodule S S) q
  show s (i (Submodule.mkQ (I : Submodule S S) x)) =
    Submodule.mkQ (I : Submodule S S) x
  have hi : i (Submodule.mkQ (I : Submodule S S) x) = e * x := by
    change (Submodule.liftQ (I : Submodule S S) (LinearMap.mulLeft S e) hker)
      (Submodule.mkQ (I : Submodule S S) x) = e * x
    exact LinearMap.congr_fun
      (Submodule.liftQ_mkQ (I : Submodule S S) (LinearMap.mulLeft S e) hker) x
  rw [hi]
  have hmem : e * x - x ∈ (I : Submodule S S) := by
    have h1 : (1 - e) * x ∈ (I : Submodule S S) := by
      have hmem1 : (1 - e) ∈ I := by
        exact Ideal.subset_span (by simp)
      exact Ideal.mul_mem_right x I hmem1
    have hsub : e * x - x = -((1 - e) * x) := by ring
    rw [hsub]
    exact neg_mem h1
  have hq :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) (x := e * x) (y := x)).mpr hmem
  simpa [s, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk] using hq

/-- The idempotent quotient is finite etale over S. -/
theorem etale (he : IsIdempotentElem e) :
    Algebra.Etale S (quotient (e := e)) := by
  letI := isLocalizationAway (S := S) he
  exact Algebra.Etale.of_isLocalizationAway e


/-- Packaged per-corner fact: the quotient by (1 - e) is finite, projective and
finite etale over S. -/
theorem finiteProjectiveEtale (he : IsIdempotentElem e) :
    Module.Finite S (quotient (e := e)) ∧
      Module.Projective S (quotient (e := e)) ∧
        Algebra.Etale S (quotient (e := e)) :=
  ⟨moduleFinite (e := e), moduleProjective (e := e) he, etale (e := e) he⟩

end IdempotentQuotientEtale
