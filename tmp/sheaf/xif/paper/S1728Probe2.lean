import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
namespace Probe3
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut

#check @Quot.map₂
#check @Quot.mk
#check @Quot.sound
#check @Quot.lift

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {A B : OrbicurveFiniteEtaleCover X}

#check (fun (f g : OrbicurveFiniteEtaleCoverMap A B) => f.map ≅ g.map)
#check (fun (f g : OrbicurveFiniteEtaleCoverMap A B) => Nonempty (f.map ≅ g.map))

end Probe3
