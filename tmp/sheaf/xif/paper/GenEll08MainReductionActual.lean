import Mathlib
import tmp.sheaf.xif.paper.GenEll05Theorem21Actual

/-! # GenEll08: main reduction assembly (GenEll -> IUT IV §2 consumer interface)

Main reduction (corpus §2-§4): Theorem 2.1 (equivalence) + Theorem 3.8 (general-position
elliptic curves full SL2 Galois action) + Cor 4.3/4.4 (degenerating/compactly bounded)
=> ABC(all) <=> ABC(general position). This file assembles the STATEMENT shape and the
consumer interface for IUT IV §2; deep inputs are named, not proved. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual

universe u

open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual

/-- Main reduction statement shape: from the Theorem 2.1 equivalence and the
§3/§4 input statements, ABC for all hyperbolic curves reduces to ABC for the
general-position/compactly-bounded family. -/
def GenEllMainReductionStatement
    (theorem21Equiv theorem38 cor43 cor44 abcAll abcGeneralPosition : Prop) : Prop :=
  theorem21Equiv → theorem38 → cor43 → cor44 → (abcGeneralPosition ↔ abcAll)

/-- Shape-level assembly theorem (logical skeleton; no geometric content). -/
theorem genEll_mainReduction_shape {theorem21Equiv theorem38 cor43 cor44 abcAll abcGeneralPosition : Prop}
    (h : GenEllMainReductionStatement theorem21Equiv theorem38 cor43 cor44 abcAll abcGeneralPosition)
    (h21 : theorem21Equiv) (h38 : theorem38) (h43 : cor43) (h44 : cor44) :
    abcGeneralPosition ↔ abcAll :=
  h h21 h38 h43 h44

/-- IUT IV §2 consumer interface: Proposition 1.4/1.6/1.7 BD-class data plus the
GenEll reduction supply the ABC height-weight bound input of §2. -/
def GenEllIUTIVSection2Consumer (bdClassData : Prop) (genEllReduction : Prop)
    (abcBound : Prop) : Prop :=
  bdClassData → genEllReduction → abcBound

def S3131GenEllMainReductionCitations : List (String × String) :=
  [ ("§2 lines 606-687", "Theorem 2.1 equivalence"),
    ("§3 lines 738-1199", "Lemma 3.1/3.2, Prop 3.4, Lemma 3.5/3.6/3.7, Theorem 3.8 (general-position full SL2 action)"),
    ("§4 lines 1200-1425", "Lemma 4.1 (GRH condition), Lemma 4.2, Cor 4.3/4.4"),
    ("IUT IV §2", "Section2.lean [machine-gap]: IUT Thm 1.10 + [GenEll] reduction => ABC; consumer interface above") ]

theorem S3131GenEllMainReductionCitations_length : S3131GenEllMainReductionCitations.length = 4 := rfl

#check genEll_mainReduction_shape

end LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual
end