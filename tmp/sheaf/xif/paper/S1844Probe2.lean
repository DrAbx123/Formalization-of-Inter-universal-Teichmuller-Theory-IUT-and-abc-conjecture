import tmp.sheaf.xif.paper.S1843SourceAllPointsActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Probe2

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual

/-- Two-cells in Cat between functors into a discrete category are unique. -/
instance ProbHom₂Discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Two-cells between strong transformations into a representable etale stack are unique. -/
theorem ProbSubsingletonMod {W : EtaleStackPseudofunctor S1726K}
    {Q : SchemeOverField S1726K}
    (a b : Pseudofunctor.StrongTrans W (S1743Y Q)) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (ProbHom₂Discrete (a.app U) (b.app U)).elim _ _

/-- The composite of two representable strong transformations. -/
noncomputable def ProbYComp {S T U : SchemeOverField S1726K}
    (f : S ⟶ T) (g : T ⟶ U) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) f)
        (S1742StrongTransOfHom (F := S1726K) g))
      (S1742StrongTransOfHom (F := S1726K) (f ≫ g)) := by
  have h1 : Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) f)
      (S1742StrongTransOfHom (F := S1726K) g))
      (S1742StrongTransOfHom (F := S1726K)
        (S1743YonedaEval S U (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1726K) f)
          (S1742StrongTransOfHom (F := S1726K) g)))) :=
    (S1742StrongTransIsoOfHom (F := S1726K) _).symm
  have h2 : S1743YonedaEval S U (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) f)
      (S1742StrongTransOfHom (F := S1726K) g)) = f ≫ g := by
    rw [S1743YonedaEval_vcomp,
      show S1743YonedaEval S T (S1742StrongTransOfHom (F := S1726K) f) = f from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) f,
      show S1743YonedaEval T U (S1742StrongTransOfHom (F := S1726K) g) = g from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) g]
  exact h1.trans (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) h2))

/-- The representable strong transformation of an identity is 2-isomorphic to the identity. -/
noncomputable def ProbYId (S : SchemeOverField S1726K) :
    Iso (S1742StrongTransOfHom (F := S1726K) (𝟙 S))
      (Pseudofunctor.StrongTrans.id (S1743Y S)) :=
  S1742StrongTransIsoOfHom (F := S1726K) (Pseudofunctor.StrongTrans.id (S1743Y S))

end Probe2
