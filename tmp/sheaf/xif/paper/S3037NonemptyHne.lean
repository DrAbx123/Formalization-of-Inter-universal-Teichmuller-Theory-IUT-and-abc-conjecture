import tmp.sheaf.xif.paper.S3026NonemptyEtaleSite
import tmp.sheaf.xif.paper.S2976bA6QDescentGluing
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S2976bA6QDescentGluing
namespace LeanFormal.IUT.XiFPaper.S3037NonemptyHne

/-- hne on the nonempty site. -/
def S3037Hne : Prop :=
  ∀ (U : S3026NonemptyScheme) (R : Sieve U),
    R ∈ S3026NonemptySite U → Nonempty R.arrows.category

/-- Every nonempty sieve has a nonempty index category. -/
theorem S3037_nonempty_of_ne_bot
    {U : S3026NonemptyScheme} (R : Sieve U) (h : R ≠ ⊥) :
    Nonempty R.arrows.category := by
  by_contra hne
  apply h
  ext Y f
  constructor
  · intro hf
    exact False.elim (hne ⟨⟨Over.mk f, hf⟩⟩)
  · intro hf
    exact False.elim hf

/-- It suffices that the bottom sieve is not covering on the nonempty site. -/
theorem S3037_hne_of_bottom_not_covering
    (hbot : ∀ U : S3026NonemptyScheme,
      ((⊥ : Sieve U) ∉ S3026NonemptySite U)) :
    S3037Hne := by
  intro U R hR
  by_contra hne
  apply hbot U
  have hRbot : R = ⊥ := by
    ext Y f
    constructor
    · intro hf
      exact False.elim (hne ⟨⟨Over.mk f, hf⟩⟩)
    · intro hf
      exact False.elim hf
  rwa [hRbot] at hR

/-- Effective descent target for the restricted nonempty Q. -/
def S3037QEffectiveDescent : Prop :=
  ∀ (U : S3026NonemptyScheme) (R : Sieve U),
    R ∈ S3026NonemptySite U →
      (S3026Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj

#check S3037Hne
#check S3037_nonempty_of_ne_bot
#check S3037_hne_of_bottom_not_covering
#check S3037QEffectiveDescent
#print axioms S3037_nonempty_of_ne_bot
#print axioms S3037_hne_of_bottom_not_covering

end LeanFormal.IUT.XiFPaper.S3037NonemptyHne