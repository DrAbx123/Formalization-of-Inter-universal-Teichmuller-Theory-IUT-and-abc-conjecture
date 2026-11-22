import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1Reduction
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2Reduction
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3Reduction
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Ind1/Ind2/Ind3 object bundle (IUT III, Theorem 3.11)

Reference object layer over the existing `Ind1Setoid`/`Ind1DescentData`,
`Ind2AlienLink`, and `PossibleImage`/`lowerClosure` structures.  The bundle
contains the actual quotient class, the alien-link datum, and the possible-image
set; no indeterminacy is replaced by a Prop placeholder. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind123ObjectsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.PossibleImage

universe u v

variable {Label Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

def ind1QuotientObject : Type v := Quotient (Ind1Setoid I)

def ind1ClassOf (c : Choice) : ind1QuotientObject I := Quotient.mk'' c

theorem ind1ClassOf_ind1 (g : Label) (c : Choice) :
    ind1ClassOf I (I.core.ind1 g c) = ind1ClassOf I c :=
  ind1QuotientMap_ind1 I g c

/-- The (Ind2) alien-link object type, exposed with its native/alien cores. -/
abbrev ind2AlienObject
    (LabelNative LabelAlien : Type u) (Native Alien : Type v)
    [AddGroup LabelNative] [AddGroup LabelAlien] : Type (max u v) :=
  Ind2AlienLink LabelNative LabelAlien Native Alien

def ind3PossibleImage (S : Set Choice) : PossibleImage Choice := ⟨S⟩

theorem ind3PossibleImage_carrier (S : Set Choice) :
    (ind3PossibleImage S).carrier = S := rfl

theorem ind3_lowerClosure_idem (S : Set Choice) :
    lowerClosure (lowerClosure S) = lowerClosure S :=
  lowerClosure_idem S

/-- Bundle of the three indeterminacy objects at one stage. -/
structure Ind123Object where
  ind1 : ind1QuotientObject I
  ind2 : Ind2AlienLink Label Label Choice Choice
  ind3 : PossibleImage Choice

def ind123ObjectOf (c : Choice)
    (D : Ind2AlienLink Label Label Choice Choice) (S : Set Choice) :
    Ind123Object I where
  ind1 := ind1ClassOf I c
  ind2 := D
  ind3 := ind3PossibleImage S

theorem ind123ObjectOf_ind1 (c : Choice)
    (D : Ind2AlienLink Label Label Choice Choice) (S : Set Choice) :
    (ind123ObjectOf I c D S).ind1 = ind1ClassOf I c := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ind123ObjectsActual

end
