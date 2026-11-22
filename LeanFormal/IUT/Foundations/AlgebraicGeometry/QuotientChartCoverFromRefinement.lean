import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteGStableAffineRefinement
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Quotient chart cover from the finite refinement

Let A be a commutative ring with a finite group G acting by ring automorphisms,
and let A^G be the fixed-point subalgebra.  Apply the finite G-stable principal
refinement theorem to W = Spec A with the trivial one-element open cover.  The
images of the principal G-stable opens D(H_x) under q : Spec A -> Spec(A^G) are
the basic opens D(H_x) in Spec(A^G), because H_x is G-invariant.  The quotient
map is surjective by the going-up theorem for the integral extension A^G -> A.
Hence the finite family of quotient opens covers Spec(A^G).  Affineness of the
quotient opens is not claimed here.
-/

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientChartCoverFromRefinement

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteGStableAffineRefinement

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {G : Type u} [Group G] [MulSemiringAction G A] [SMulCommClass G R A] [Fintype G]

/-- The quotient map on prime spectra induced by A^G -> A. -/
noncomputable def qPoint (p : PrimeSpectrum A) :
    PrimeSpectrum (FixedPoints.subalgebra R A G) :=
  ⟨p.asIdeal.comap (algebraMap (FixedPoints.subalgebra R A G) A),
    Ideal.comap_isPrime (algebraMap (FixedPoints.subalgebra R A G) A) p.asIdeal⟩

/-- The underlying set of a principal open in Spec(A^G). -/
abbrev basicOpenSet (H : FixedPoints.subalgebra R A G) :
    Set (PrimeSpectrum (FixedPoints.subalgebra R A G)) :=
  PrimeSpectrum.basicOpen H

/-- The quotient map is surjective: every prime of A^G lies under a prime of A.
This is the going-up theorem for the integral extension A^G -> A. -/
theorem qPoint_surjective : Function.Surjective (qPoint (R := R) (A := A) (G := G)) := by
  classical
  letI : Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G :=
    ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
    Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R A G) A G
  intro y
  obtain ⟨Q, _, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := FixedPoints.subalgebra R A G) (S := A)
      y.asIdeal (⊥ : Ideal A)
      (Ideal.comap_bot_le_of_injective (algebraMap (FixedPoints.subalgebra R A G) A)
        (fun _ _ h => Subtype.ext h))
  refine ⟨⟨Q, hQprime⟩, ?_⟩
  rw [PrimeSpectrum.ext_iff]
  exact hQcomap

/-- The image of a principal open D(H) under q is the corresponding principal
open D(H) in Spec(A^G), for H in the fixed subalgebra. -/
theorem qPoint_image_basicOpen (H : FixedPoints.subalgebra R A G) :
    qPoint (R := R) (A := A) (G := G) ''
        (PrimeSpectrum.basicOpen (H : A) : Set (PrimeSpectrum A)) =
      (PrimeSpectrum.basicOpen H :
        Set (PrimeSpectrum (FixedPoints.subalgebra R A G))) := by
  classical
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    change H ∉ p.asIdeal.comap (algebraMap (FixedPoints.subalgebra R A G) A)
    intro hmem
    exact hp hmem
  · intro hy
    obtain ⟨p, hp⟩ := qPoint_surjective (R := R) (A := A) (G := G) y
    refine ⟨p, ?_, hp⟩
    intro hmem
    apply hy
    rw [← hp]
    exact hmem

/-- The trivial one-element closed cover: the complement of V(top) is all of
Spec A. -/
theorem zeroLocus_top_complement (x : PrimeSpectrum A) :
    x ∉ PrimeSpectrum.zeroLocus ((⊤ : Ideal A) : Set A) := by
  intro hx
  have htop : (⊤ : Ideal A) ≤ x.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp hx
  exact x.isPrime.ne_top (le_antisymm htop le_top).symm

/-- The finite refinement theorem produces the finite quotient chart cover. -/
theorem quotient_chart_cover_from_refinement :
    ∃ (K : Finset (PrimeSpectrum A)) (Hq : K → FixedPoints.subalgebra R A G),
      (∀ k : K, IsOpen (basicOpenSet (R := R) (A := A) (G := G) (Hq k))) ∧
      (∀ y : PrimeSpectrum (FixedPoints.subalgebra R A G), ∃ k : K,
        y ∈ basicOpenSet (R := R) (A := A) (G := G) (Hq k)) := by
  classical
  obtain ⟨K, H, j, hsub, hstable, hinvariant, hcover⟩ :=
    finite_gStable_principal_refinement (G := G) (B := A)
      (J := PUnit) (fun _ => (⊤ : Ideal A))
      (fun x => ⟨PUnit.unit, zeroLocus_top_complement (A := A) x⟩)
      (fun _ g x _ => zeroLocus_top_complement (A := A) (pointImage (G := G) g x))
  refine ⟨K, fun k : K =>
    (⟨H k.1, by intro g; exact hinvariant k.1 k.2 g⟩ :
      FixedPoints.subalgebra R A G), ?_, ?_⟩
  · intro k
    exact PrimeSpectrum.isOpen_basicOpen
  · intro y
    obtain ⟨p, hp⟩ := qPoint_surjective (R := R) (A := A) (G := G) y
    obtain ⟨k, hkK, hpk⟩ := hcover p
    let Hq : FixedPoints.subalgebra R A G :=
      ⟨H k, by intro g; exact hinvariant k hkK g⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    change y ∈ (PrimeSpectrum.basicOpen Hq :
      Set (PrimeSpectrum (FixedPoints.subalgebra R A G)))
    rw [← qPoint_image_basicOpen (R := R) (A := A) (G := G) Hq]
    rw [← hp]
    exact ⟨p, hpk, rfl⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientChartCoverFromRefinement
