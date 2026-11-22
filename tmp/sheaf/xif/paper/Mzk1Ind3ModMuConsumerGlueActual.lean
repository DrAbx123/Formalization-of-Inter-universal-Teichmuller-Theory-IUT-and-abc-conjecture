import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-! # Mzk1Ind3ModMuConsumerGlueActual — consumer forms of the (Ind3)/root-of-unity objects

Small reference/glue module (no new mathematics): consumes the LANA-latest
`Multiradial/Spec` (Ind3) upper-semi and roots-of-unity (Remark 3.11.4) cards in the
forms used by the Corollary 3.12 route.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind3ModMuConsumerGlueActual

open Iut.Multiradial
open CategoryTheory

universe u v w w'

/-! ## (Ind3): upper semi-compatibility -/

variable {X : Type*}

/-- Membership in the (Ind3)-possible class is upper semi-compatibility. -/
theorem mem_ind3Possible_iff {R S : Set X} :
    S ∈ ind3Possible R ↔ S ⊆ R := Iff.rfl

/-- The coric region itself is (Ind3)-possible. -/
theorem ind3Possible_self (R : Set X) : R ∈ ind3Possible R := subset_refl R

/-- Monotonicity of the (Ind3)-possible class in the coric region. -/
theorem ind3Possible_mono {R R' : Set X} (h : R ⊆ R') :
    ind3Possible R ⊆ ind3Possible R' :=
  fun _ hS => Set.Subset.trans hS h

/-- The union over an upper semi-compatible family is contained in the coric region. -/
theorem upperSemiCompatible_iUnion_subset {img : Int → Set X} {R : Set X}
    (h : UpperSemiCompatible img R) : (⋃ m, img m) ⊆ R :=
  UpperSemiCompatible.iUnion_subset h

/-- The union of the (Ind3)-possible sets is the coric region (consumer form). -/
theorem sUnion_ind3Possible_eq (R : Set X) : ⋃₀ ind3Possible R = R :=
  sUnion_ind3Possible R

/-- (Ind3) inside the possible images: an upper semi-compatible region is contained in the
possible images of the multiradial representation. -/
theorem possibleRegion_of_ind3
    {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
    {R : RawOutput.{u, v, w} G A} {P : G}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) {S : Set X}
    (hS : S ∈ ind3Possible (reg x)) :
    S ⊆ MRRep.possibleRegion reg (MRRep.mk (R := R) x) :=
  MRRep.subset_possibleRegion (R := R) reg x hS

/-! ## Roots of unity (Remark 3.11.4(i)) -/

variable (M : Type*) [CommMonoid M]

/-- Classes modulo roots of unity: the mk equality criterion. -/
theorem modMu_mk_eq_mk_iff {x y : M} :
    ModMu.mk x = ModMu.mk y ↔ ∃ ζ : Mˣ, IsOfFinOrder ζ ∧ (ζ : M) * x = y :=
  ModMu.mk_eq_mk_iff x y

/-- Multiplying by a finite-order unit does not change the class modulo roots of unity. -/
theorem modMu_mk_mul_unit {ζ : Mˣ} (hζ : IsOfFinOrder ζ) (x : M) :
    ModMu.mk ((ζ : M) * x) = ModMu.mk x := by
  refine (ModMu.mk_eq_mk_iff ((ζ : M) * x) x).2 ⟨ζ⁻¹, hζ.inv, ?_⟩
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- A set stable under multiplication by roots of unity is a union of orbits (consumer form). -/
theorem modMu_mem_iff_of_stable {S : Set M}
    (hS : ∀ ζ : Mˣ, IsOfFinOrder ζ → ∀ x ∈ S, (ζ : M) * x ∈ S) {x y : M}
    (h : ModMu.mk x = ModMu.mk y) : x ∈ S ↔ y ∈ S :=
  ModMu.mem_iff_of_stable hS h

#check mem_ind3Possible_iff
#check ind3Possible_self
#check ind3Possible_mono
#check upperSemiCompatible_iUnion_subset
#check possibleRegion_of_ind3
#check modMu_mk_eq_mk_iff
#check modMu_mk_mul_unit

end LeanFormal.IUT.XiFPaper.Mzk1Ind3ModMuConsumerGlueActual
end
