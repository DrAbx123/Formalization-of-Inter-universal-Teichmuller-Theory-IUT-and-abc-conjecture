/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueFieldEquivActual
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! # C17: residue-field equivalence from inertia degree one (converse direction) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivConstructActual

open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {p : Ideal R} {P : Ideal S} [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]

/-- If the residual degree is one, the residue fields are equivalent over `R ⧸ p`. -/
theorem residueFieldEquiv_of_inertiaDeg_eq_one
    (h : Ideal.inertiaDeg' p P = 1) :
    ResidueFieldEquiv (p := p) (P := P) := by
  rw [ResidueFieldEquiv]
  haveI : Field (R ⧸ p) := Ideal.Quotient.field p
  haveI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hleA : p ≤ P.comap (algebraMap R S) := by
    rw [Ideal.over_def P p]
  letI : Algebra (R ⧸ p) (S ⧸ P) :=
    ((Ideal.quotientMapₐ (I := p) P (Algebra.ofId R S) hleA).toRingHom).toAlgebra
  letI : Module (R ⧸ p) (S ⧸ P) := Algebra.toModule
  have hfin : Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg'_algebraMap (p := p) (P := P)]
    exact h
  have hle : p ≤ P.comap (algebraMap R S) := by
    rw [Ideal.over_def P p]
  let phi : (R ⧸ p) →ₐ[R ⧸ p] (S ⧸ P) :=
    Ideal.quotientMapₐ (I := p) P (Algebra.ofId R S) hle
  have hphi_inj : Function.Injective phi := by
    -- the source is a field and the target is a field, so the algebra map is injective
    intro x y hxy
    have := congrArg (fun f => f) hxy
    -- use that phi is a field hom: x = y from phi x = phi y
    exact phi.injective hxy
  have hphi_surj : Function.Surjective phi := by
    intro x
    have h1 : (1 : S ⧸ P) ≠ 0 := one_ne_zero
    have hsp : ∀ y : S ⧸ P, ∃ c : R ⧸ p, c • (1 : S ⧸ P) = y :=
      (finrank_eq_one_iff_of_nonzero' (K := R ⧸ p)
        (V := S ⧸ P) (1 : S ⧸ P) h1).mp hfin
    obtain ⟨c, hc⟩ := hsp x
    refine ⟨c, ?_⟩
    rw [← hc]
    simpa [Algebra.algebraMap_eq_smul_one] using AlgHom.commutes phi c
  exact ⟨(AlgEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩).symm⟩

def residueConstructRows : List (String × String × String) :=
  [ ("residueFieldEquiv_of_inertiaDeg_eq_one", "inertiaDeg'=1 => residue field equiv", "PROVED") ]

theorem residueConstructRows_length : residueConstructRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivConstructActual

end