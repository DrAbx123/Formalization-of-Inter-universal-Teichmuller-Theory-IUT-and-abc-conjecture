import tmp.sheaf.xif.paper.S2287StrongCospanRefuteActual
import tmp.sheaf.xif.paper.S2087ToAObstructionActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2290: is S2103 trivially true?

No.  S2103 asks for a strong finite-etale structure on every `g.map`; the
available datum is only the weak `EtaleStackFiniteEtaleMorphism g.map` from
S2087.  A weak-to-strong upgrade would need the full cone essential
surjectivity (S1852/S2100), which is not available for arbitrary `g.map`.

This file proves the exact reduction: S2103 is equivalent (given its weak
part) to the per-morphism upgrade.  No strong structure is constructed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2290StrongCospanActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual
open LeanFormal.IUT.XiFPaper.S2284S2086QuantifierActual
open LeanFormal.IUT.XiFPaper.S2287StrongCospanRefuteActual

universe u

/-- The missing weak-to-strong upgrade, per cospan morphism. -/
def S2290WeakToStrongUpgrade : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism g.map → StrongEtaleStackFiniteEtaleMorphism g.map

/-- The weak part of S2103. -/
def S2290WeakField : Type 1 :=
  S2087CospanGMapFiniteEtaleField

/-- S2103 gives the weak field by forgetting. -/
noncomputable def S2290S2103ToWeak
    (h : S2103StrongCospanGMapFiniteEtale) : S2290WeakField :=
  fun A B C f g => (h A B C f g).toWeak

/-- Conversely, weak field + upgrade gives S2103. -/
noncomputable def S2290S2103_of_weakUpgrade
    (hup : S2290WeakToStrongUpgrade) (hw : S2290WeakField) :
    S2103StrongCospanGMapFiniteEtale :=
  fun A B C f g => hup A B C f g (hw A B C f g)

#check S2290WeakToStrongUpgrade
#check S2290S2103ToWeak
#check S2290S2103_of_weakUpgrade

end LeanFormal.IUT.XiFPaper.S2290StrongCospanActual

end
