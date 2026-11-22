import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Audit.Status

/-! # S3137: model theater-family skeleton (from-scratch model, task-72)

Skeleton for the model SourceHodgeTheaterFamily: index := SourceTheorem311Index
(= Int x Int, universe-lifted to the family index universe), permutation := refl,
refl-compatible link data supplied as a record, and a construction of the full
family GIVEN distinctness (injectivity of the theater map).

FORMAL OBSTRUCTION: a CONSTANT theater cannot be injective when index is
Int x Int (distinctness forces a subsingleton index), so the model theater must
be index-dependent; the skeleton keeps the theater value and links as parameters.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Audit

universe ua uv upi umon ui

/-- Model index = paper source index. -/
abbrev ModelIndex : Type := SourceTheorem311Index

/-- Theater-family skeleton data over the universe-lifted model index. -/
structure ModelTheaterData (l : PrimeGeFive) (V : Type uv) where
  theater : ULift.{ui} ModelIndex → HodgeTheater.{ua, uv, upi, umon} l V
  link : ∀ i j, HodgeTheaterLink (theater i) (theater j)
  link_refl : ∀ i, link i i = HodgeTheaterLink.refl (theater i)
  link_symm : ∀ i j, HodgeTheaterLink.symm (link i j) = link j i
  link_trans : ∀ i j k, HodgeTheaterLink.trans (link i j) (link j k) = link i k
  permutation_naturality : ∀ i j,
    HodgeTheaterLink.trans (link i j) (link j j) =
      HodgeTheaterLink.trans (link i i) (link i j)

/-- Construction of the full model theater family from skeleton data plus the
distinctness hypothesis. -/
def ModelTheaterData.toFamily (M : ModelTheaterData.{ua, uv, upi, umon, ui} l V)
    (hInj : Function.Injective M.theater) :
    SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V where
  index := ULift.{ui} ModelIndex
  theater := M.theater
  distinct := hInj
  link := M.link
  link_refl := M.link_refl
  link_symm := M.link_symm
  link_trans := M.link_trans
  permutation := Equiv.refl _
  permutationLink := fun i => M.link i i
  permutation_naturality := M.permutation_naturality

/-- The source index is not a subsingleton (formal obstruction to constant
theater models). -/
theorem modelIndex_not_subsingleton : ¬ Subsingleton ModelIndex := by
  intro h
  have h01 : ((0 : Int), (0 : Int)) = ((1 : Int), (0 : Int)) := Subsingleton.elim _ _
  have : (0 : Int) = 1 := congrArg Prod.fst h01
  exact absurd this (by norm_num)

end LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual

namespace LeanFormal.IUT.Audit

/-- INDEX: from-scratch model theater skeleton (construction + obstruction). -/
def S3137ModelTheaterSkeletonRecord : Obligation :=
  { id := "INDEX.MODEL.from-scratch-theater-family"
    source := "IUT I Definition 3.1; SourceHodgeTheaterFamily; SourceOriginalInput.family/index_equiv"
    status := VerificationStatus.interface
    note := "SKELETON: ModelTheaterData (theater function over ULift SourceTheorem311Index, link family, link laws, permutation naturality with identity permutation) and ModelTheaterData.toFamily producing the full SourceHodgeTheaterFamily GIVEN injectivity. FORMAL OBSTRUCTION: modelIndex_not_subsingleton shows Int x Int is not a subsingleton, so a CONSTANT theater cannot satisfy distinct; the model theater must be index-dependent (qpilot). Not a residual itself."
    dependsOn := ["S3137ModelTheaterSkeletonActual"] }

end LeanFormal.IUT.Audit
