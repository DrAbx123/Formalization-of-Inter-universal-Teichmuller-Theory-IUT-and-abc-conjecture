import tmp.sheaf.xif.paper.S1836CoverPullbackStackActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1836ConsumerCheck

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual

/-- The identity-right datum is an actual inhabitant. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    Nonempty (S1836PseudopullbackStackDatum f (S1641CoverMapId C)) :=
  ⟨S1836PseudopullbackStackDatum_id_right f⟩

/-- Its source is the actual cover source. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    (S1836PseudopullbackStackDatum_id_right f).stack = A.source :=
  S1836Datum_id_right_stack f

/-- Its structure map is the actual finite-etale cover map. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    (S1836PseudopullbackStackDatum_id_right f).structureMap = A.map :=
  S1836Datum_id_right_structureMap f

/-- The identity-right datum has an actual IsStack proof. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    (S1836PseudopullbackStackDatum_id_right f).stack.fiber.IsStack
      (SchemeOverField.etaleTopology S1726K) :=
  (S1836PseudopullbackStackDatum_id_right f).stack_isStack

/-- The identity-right datum has a representably finite-etale structure map. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    EtaleStackFiniteEtaleMorphism
      (S1836PseudopullbackStackDatum_id_right f).structureMap :=
  (S1836PseudopullbackStackDatum_id_right f).structureMap_finiteEtale

/-- The identity-right datum gives a genuine pullback. -/
example {A C : S1728Cover} (f : S1728CoverMap A C) :
    HasPullback (S1832Q f) (S1832Q (S1641CoverMapId C)) :=
  (S1836PseudopullbackStackDatum_id_right f).hasPullback

/-- The exact missing statement implies the S1832 statement. -/
example (h : S1836FirstMissingPseudopullbackStack) : S1832FirstMissingPullback :=
  S1836FirstMissing_to_S1832 h

end LeanFormal.IUT.XiFPaper.S1836ConsumerCheck
