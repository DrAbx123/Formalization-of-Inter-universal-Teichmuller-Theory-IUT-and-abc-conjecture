import tmp.sheaf.xif.paper.GenEll02Prop14Actual
import tmp.sheaf.xif.paper.S3136BDClassChainToolActual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.GenEll02bProofActual

open LeanFormal.IUT.XiFPaper.S3131BDClassCompositionActual
open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual
open LeanFormal.IUT.XiFPaper.GenEll02Prop14Actual

/-- Elementary two-sided form: a pointwise bound f <= g + C on F gives the BD relation
IsBDLe g f F (i.e. f - g bounded above). -/
theorem isBDLe_of_le_add_const {α : Type*} {f g : α → ℝ} {F : Set α}
    (h : ∃ C : ℝ, ∀ x ∈ F, f x ≤ g x + C) :
    LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual.IsBDLe g f F := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro x hx
  linarith [hC x hx]

/-- Prop 1.4(ii) extraction: bounded-below height off the zero locus yields the BD
relation ht_L >= O(1) on that locus (IsBDLe (fun _ => 0) htL). -/
theorem prop14_ii_bounded_below
    {X : Type} {zeroLocus : Set X} {htL : X → Real}
    (h : HeightNonnegOnNonzeroSection X zeroLocus htL) :
    LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual.IsBDLe htL (fun _ : X => 0) (zeroLocusᶜ) := by
  let C := Classical.choose h
  have hC : ∀ x : X, x ∉ zeroLocus → C ≤ htL x := Classical.choose_spec h
  refine ⟨-C, ?_⟩
  intro x hx
  simp only [Set.mem_compl_iff] at hx
  have hx' := hC x hx
  simp only [Pi.zero_apply]
  linarith

/-- Prop 1.4(iv) extraction: finiteness predicate as stated. -/
theorem prop14_iv_extract
    {X : Type} {htL : X → Real} {boundedSet : Set X → Prop} {C : Real}
    (h : HeightBoundedPointsFinite X boundedSet htL C) :
    boundedSet {x | htL x ≤ C} :=
  h

def s3135Prop14ProofCitations : List (String × String) :=
  [ ("Prop 1.4(i)", "corpus 303-310 additivity (elementary from definitions)"),
    ("Prop 1.4(ii)", "corpus 311-316: bounding by a section, ht_L >= -C on nonzero locus; our extraction isBDLe zero ht"),
    ("Prop 1.4(iii)", "corpus 317-322 via (i),(ii)"),
    ("Prop 1.4(iv)", "corpus 323-427 Silv1 Thm 2.1 style finiteness") ]

theorem s3135Prop14ProofCitations_length : s3135Prop14ProofCitations.length = 4 := rfl

#check isBDLe_of_le_add_const
#check prop14_ii_bounded_below
#check prop14_iv_extract
end LeanFormal.IUT.XiFPaper.GenEll02bProofActual
end