import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe6

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
    f.map ≫ g.map ≅ f.map ≫ g'.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target f.map g.map g'.map eg

example {A B C : OrbicurveFiniteEtaleCover X}
    (f f' : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (ef : f.map ≅ f'.map) :
    f.map ≫ g.map ≅ f'.map ≫ g.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  exact @Bicategory.whiskerRightIso Bicat _ source mid target f.map f'.map g.map ef

end Probe6
