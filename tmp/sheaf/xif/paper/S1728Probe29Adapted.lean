import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ProbeSmall

open CategoryTheory
open Iut

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

structure SmallRaw (A B : OrbicurveFiniteEtaleCover X) where
  Carrier : Type u
  equiv : Carrier ≃ OrbicurveFiniteEtaleCoverMap A B

example (data : OrbicurveEtaleFundamentalGroup X G)
    (A B : OrbicurveFiniteEtaleCover X) : SmallRaw (F := F) (X := X) A B := by
  letI := data.coverCategory
  exact
    { Carrier := (A ⟶ B)
      equiv := Equiv.ofBijective
        (fun map : A ⟶ B =>
          ({ map := data.coverMorphism map,
             commutes := data.coverMorphism_over map } :
            OrbicurveFiniteEtaleCoverMap A B))
        (data.coverMorphism_bijective (source := A) (target := B)) }

end ProbeSmall
