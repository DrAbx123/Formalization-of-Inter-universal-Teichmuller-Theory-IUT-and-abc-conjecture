import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe10

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

example {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g g' : OrbicurveFiniteEtaleCoverMap B C)
    (eg : g.map ≅ g'.map) :
    Pseudofunctor.StrongTrans.vcomp f.map g.map ≅
      Pseudofunctor.StrongTrans.vcomp f.map g'.map :=
  Bicategory.whiskerLeftIso f.map eg

example {A B C : OrbicurveFiniteEtaleCover X}
    (f f' : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (ef : f.map ≅ f'.map) :
    Pseudofunctor.StrongTrans.vcomp f.map g.map ≅
      Pseudofunctor.StrongTrans.vcomp f'.map g.map :=
  Bicategory.whiskerRightIso ef g.map

example {A B C D : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D) :
    Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) h.map ≅
      Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map h.map) :=
  Bicategory.associator f.map g.map h.map

example {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id A.source.fiber) f.map ≅ f.map :=
  Bicategory.leftUnitor f.map

example {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.id B.source.fiber) ≅ f.map :=
  Bicategory.rightUnitor f.map

end Probe10
