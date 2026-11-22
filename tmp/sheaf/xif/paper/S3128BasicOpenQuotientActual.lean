import tmp.sheaf.xif.paper.S3128LocalAffineQuotientActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SpecActionActual
open LeanFormal.IUT.XiFPaper.S3128LocalAffineQuotientActual

variable {G : Type} [Group G] [Fintype G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

/-- The invariant element N_f = ∏ g, g • f. -/
noncomputable def S3128Nf (f : A) : A :=
  ∏ g : G, g • f

/-- The N_f product is G-invariant. -/
theorem S3128Nf_invariant (f : A) (h : G) :
    h • S3128Nf (G := G) f = S3128Nf (G := G) f := by
  unfold S3128Nf
  rw [Finset.smul_prod']
  apply Finset.prod_bij (fun g _ => h * g)
  · intro g _
    exact Finset.mem_univ _
  · intro g _ g' _ hg
    exact mul_left_cancel hg
  · intro b _
    exact ⟨h⁻¹ * b, Finset.mem_univ _, by simp⟩
  · intro g _
    simp [mul_smul]


/-- The image of N_f in B is a unit when B = A_f. -/
theorem S3128Nf_image_isUnit {f : A} [Algebra A B]
    [IsLocalization.Away f B]
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a)) :
    IsUnit (algebraMap A B (S3128Nf (G := G) f)) := by
  rw [S3128Nf, map_prod]
  refine Finset.prod_induction
    (fun g : G => algebraMap A B (g • f)) (fun x => IsUnit x)
    (fun a b ha hb => ha.mul hb) isUnit_one ?_
  intro g _
  rw [← halg g f]
  exact (IsLocalization.Away.algebraMap_isUnit (R := A) (S := B) f).map
    (MulSemiringAction.toRingHom G B g)


/-- N_f as an element of the fixed subring of A. -/
noncomputable def S3128NfInv (f : A) : S3128FixedSubring G A :=
  ⟨S3128Nf (G := G) f, fun g => S3128Nf_invariant (G := G) f g⟩

/-- Basic-open localization target for fixed subrings:
B^G is the localization of A^G at powers of N_f. -/
def S3128BasicOpenLocalizationTarget
    [Algebra (S3128FixedSubring G A) (S3128FixedSubring G B)]
    (f : A) : Prop :=
  IsLocalization.Away
    (algebraMap (S3128FixedSubring G A) (S3128FixedSubring G B)
      (S3128NfInv (G := G) (A := A) f))
    (S3128FixedSubring G B)

#check S3128Nf
#check S3128Nf_invariant
#check S3128Nf_image_isUnit
#check S3128NfInv
#check S3128BasicOpenLocalizationTarget
#check IsOpenImmersion.of_isLocalization

end LeanFormal.IUT.XiFPaper.S3128BasicOpenQuotientActual
end