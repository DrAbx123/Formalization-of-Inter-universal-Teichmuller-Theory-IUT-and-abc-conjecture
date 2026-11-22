import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual
import tmp.sheaf.xif.paper.S1763CoverQuotientsActual
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2513PreGaloisLimitsActual

/-- The S2482 cover category and its exact PreGalois obligations. -/
abbrev S2513Cover : Type 1 :=
  OrbicurveFiniteEtaleCover S2482Orbicurve

instance S2513Category : Category.{1, 1} S2513Cover :=
  S1736ActualCategory (F := F) (X := S2482Orbicurve)

/-- Exact missing geometric input for the terminal object. -/
def S2513IdentityFiniteEtale : Prop :=
  S1736IdentityFiniteEtale (F := F) (X := S2482Orbicurve)

/-- Conditional actual terminal construction. -/
theorem S2513IdentityFiniteEtale_actual : S2513IdentityFiniteEtale :=
  S2514IdentityFiniteEtaleActual

theorem S2513HasTerminal_of_identity
    (h : S2513IdentityFiniteEtale) :
    @HasTerminal S2513Cover S2513Category :=
  S1736HasTerminal_of_identityFiniteEtale_prop (F := F) (X := S2482Orbicurve) h

theorem S2513HasTerminal : @HasTerminal S2513Cover S2513Category :=
  S2513HasTerminal_of_identity S2513IdentityFiniteEtale_actual

/-- The binary fan with a cover A and the terminal cover. -/
noncomputable def S2513FanTerminal (A : S2513Cover) :
    BinaryFan A S2514TerminalCover :=
  BinaryFan.mk (P := A) (𝟙 A) (S2514TerminalCover_isTerminal.from A)

/-- A is the binary product of A and the terminal cover. -/
noncomputable def S2513FanTerminal_isLimit (A : S2513Cover) :
    IsLimit (S2513FanTerminal A) := by
  have h : IsLimit (BinaryFan.mk (P := A) (𝟙 A)
      (S2514TerminalCover_isTerminal.from A)) :=
    BinaryFan.isLimitMk (W := A) (fst := 𝟙 A)
      (snd := S2514TerminalCover_isTerminal.from A)
      (fun s => s.fst)
      (fun s => by rw [Category.comp_id])
      (fun s => by
        exact S2514TerminalCover_isTerminal.hom_ext _ _)
      (fun s m hm1 hm2 => by
        rw [Category.comp_id] at hm1
        exact hm1)
  simpa [S2513FanTerminal] using h

theorem S2513HasBinaryProductTerminal (A : S2513Cover) :
    HasBinaryProduct A S2514TerminalCover :=
  ⟨_, S2513FanTerminal_isLimit A⟩

/-- The binary fan with the terminal cover on the left and a cover A on the right. -/
noncomputable def S2513FanTerminalRight (A : S2513Cover) :
    BinaryFan S2514TerminalCover A :=
  BinaryFan.mk (P := A) (S2514TerminalCover_isTerminal.from A) (𝟙 A)

noncomputable def S2513FanTerminalRight_isLimit (A : S2513Cover) :
    IsLimit (S2513FanTerminalRight A) := by
  have h : IsLimit (BinaryFan.mk (P := A)
      (S2514TerminalCover_isTerminal.from A) (𝟙 A)) :=
    BinaryFan.isLimitMk (W := A) (fst := S2514TerminalCover_isTerminal.from A)
      (snd := 𝟙 A)
      (fun s => s.snd)
      (fun s => S2514TerminalCover_isTerminal.hom_ext _ _)
      (fun s => by rw [Category.comp_id])
      (fun s m hm1 hm2 => by
        rw [Category.comp_id] at hm2
        exact hm2)
  simpa [S2513FanTerminalRight] using h

theorem S2513HasBinaryProductTerminalRight (A : S2513Cover) :
    HasBinaryProduct S2514TerminalCover A :=
  ⟨_, S2513FanTerminalRight_isLimit A⟩

/-- The trivial action of any finite group on any cover has an actual colimit
(the cover itself): quotient by the trivial action. -/
theorem S2513HasTrivialActionQuotient
    (G : Type 1) [Group G] (A : S2513Cover) :
    HasColimit ((Functor.const (SingleObj G)).obj A) :=
  S1763CoverQuotientsActual.hasColimit_const_singleObj A

/-- Exact finite-limit obligation. -/
def S2513PullbackObligation : Prop :=
  S1736PullbackObligation (F := F) (X := S2482Orbicurve)

def S2513FiniteLimitsObligation : Prop :=
  @HasFiniteLimits S2513Cover S2513Category

/-- Exact finite-coproduct obligation. -/
def S2513FiniteCoproductObligation : Prop :=
  @HasFiniteCoproducts S2513Cover S2513Category

/-- Exact finite-group quotient obligation. -/
def S2513FiniteGroupQuotientObligation : Prop :=
  S1736FiniteGroupQuotientObligation (F := F) (X := S2482Orbicurve)

/-- The exact intersection of the terminal and pullback obligations is finite limits. -/
theorem S2513FiniteLimits_of_terminal_pullbacks
    (ht : @HasTerminal S2513Cover S2513Category)
    (hp : @HasPullbacks S2513Cover S2513Category) :
    S2513FiniteLimitsObligation :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

theorem S2513HasFiniteLimits_of_pullbacks
    (hPull : S2513PullbackObligation) :
    S2513FiniteLimitsObligation :=
  S1736HasFiniteLimits_of_inputs (F := F) (X := S2482Orbicurve)
    S2514IdentityFiniteEtaleActual hPull

/-- Conditional assembly of the actual PreGaloisCategory from the four remaining fields. -/
theorem S2513PreGaloisCategoryOfRemainingInputs
    (hPull : S2513PullbackObligation)
    (hCoprod : S2513FiniteCoproductObligation)
    (hQuot : S2513FiniteGroupQuotientObligation)
    (hMono : S1736MonoDirectSummandObligation (F := F) (X := S2482Orbicurve)) :
    S1736ActualPreGaloisObligation (F := F) (X := S2482Orbicurve) :=
  S1736PreGaloisCategoryOfInputs (F := F) (X := S2482Orbicurve)
    S2514IdentityFiniteEtaleActual hPull hCoprod hQuot hMono

#check S2513IdentityFiniteEtale
#check S2513HasTerminal_of_identity
#check S2513FiniteLimits_of_terminal_pullbacks
#check S2513HasFiniteLimits_of_pullbacks
#check S2513PreGaloisCategoryOfRemainingInputs
#print axioms S2513HasTerminal_of_identity
#print axioms S2513FiniteLimits_of_terminal_pullbacks

end LeanFormal.IUT.XiFPaper.S2513PreGaloisLimitsActual
end
