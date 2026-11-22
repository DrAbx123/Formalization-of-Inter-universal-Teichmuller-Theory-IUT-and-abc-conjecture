import tmp.sheaf.xif.paper.S2138H1MLActual
import Iut.Foundations.ContinuousH1
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2138H1MLActual
namespace LeanFormal.IUT.XiFPaper.S2142ActualH1TowerActual
/-- The missing actual arithmetic H^1 tower: coefficient groups, continuous
actions of the local absolute Galois group, finite level H^1, and surjective
transition maps.  This is the exact structure required by S2138; no
inhabitant is asserted. -/
structure S2142ActualMuH1Tower where
  p : Nat
  hprime : Fact (Nat.Prime p)
  coeff : ℕ → Type
  [commGroupCoeff : ∀ n, CommGroup (coeff n)]
  [topCoeff : ∀ n, TopologicalSpace (coeff n)]
  [discreteCoeff : ∀ n, DiscreteTopology (coeff n)]
  [topGroupCoeff : ∀ n, IsTopologicalGroup (coeff n)]
  actn : ∀ n, Iut.ContinuousGroupAction
    (LocalAbsoluteGalois p) (coeff n)
  finiteH1 : ∀ n, Finite (Iut.ContinuousH1 (actn n))
  proj : ∀ n, Iut.ContinuousH1 (actn (n+1)) →*
    Iut.ContinuousH1 (actn n)
  proj_surjective : ∀ n, Function.Surjective (proj n)
attribute [instance] S2142ActualMuH1Tower.commGroupCoeff
  S2142ActualMuH1Tower.topCoeff S2142ActualMuH1Tower.discreteCoeff
  S2142ActualMuH1Tower.topGroupCoeff
variable (A : S2142ActualMuH1Tower)
/-- The actual tower supplies the abstract S2138 H^1 tower. -/
noncomputable def S2142ToS2138Tower : S2138H1Tower where
  H1 := fun n => Iut.ContinuousH1 (A.actn n)
  commGroup := fun n => inferInstance
  finite := A.finiteH1
  proj := A.proj
/-- Consequently the actual tower satisfies the abstract Mittag-Leffler
condition once its surjectivity field is supplied. -/
theorem S2142MittagLeffler :
    S2138MittagLeffler (S2142ToS2138Tower A) :=
  S2138MittagLeffler_of_surjective (S2142ToS2138Tower A) A.proj_surjective
/-- Exact first missing: an inhabitant of the actual Mu_n H^1 tower. -/
abbrev S2142ActualMuH1TowerRequired : Type 1 := S2142ActualMuH1Tower
#check S2142ActualMuH1Tower
#check S2142ToS2138Tower
#check S2142MittagLeffler
#check S2142ActualMuH1TowerRequired
end LeanFormal.IUT.XiFPaper.S2142ActualH1TowerActual
end
