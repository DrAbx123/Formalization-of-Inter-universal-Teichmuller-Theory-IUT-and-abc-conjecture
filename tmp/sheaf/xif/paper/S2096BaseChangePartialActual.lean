import tmp.sheaf.xif.paper.S2096StackMorphismActual

/-! # S2096BaseChangePartial: scheme pullback part of M2 -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S2096BaseChangePartialActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)

section

variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def pullbackScheme : SchemeOverField S1726K :=
  Limits.pullback Q.projection s

noncomputable def projection : pullbackScheme (m := m) s vy Q ⟶ T :=
  Limits.pullback.snd Q.projection s

noncomputable def projectionMap :
    SchemeRepresentableMap (projection (m := m) s vy Q) where
  transformation := S1742StrongTransOfHom
    (Limits.pullback.snd Q.projection s)
  app_eq := fun _ => rfl

noncomputable def basePoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy

noncomputable def toSource :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K
        (pullbackScheme (m := m) s vy Q)) X.fiber :=
  Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (Limits.pullback.fst Q.projection s))
    Q.toSource

structure PartialPresentation
    (m : X.Hom Y)
    (pt : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber) where
  pullbackScheme : SchemeOverField S1726K
  projection : pullbackScheme ⟶ T
  projectionMap : SchemeRepresentableMap projection
  toSource : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K pullbackScheme) X.fiber
  commutes : Iso
    (Pseudofunctor.StrongTrans.vcomp toSource m)
    (Pseudofunctor.StrongTrans.vcomp projectionMap.transformation pt)

noncomputable def partialPresentation
    (hc : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (toSource (m := m) s vy Q) m)
      (Pseudofunctor.StrongTrans.vcomp
        (projectionMap (m := m) s vy Q).transformation
        (basePoint s vy))) :
    PartialPresentation (m := m) (pt := basePoint s vy) where
  pullbackScheme := pullbackScheme (m := m) s vy Q
  projection := projection (m := m) s vy Q
  projectionMap := projectionMap (m := m) s vy Q
  toSource := toSource (m := m) s vy Q
  commutes := hc

#check PartialPresentation
#check partialPresentation
#check pullbackScheme
#check projection
#check toSource

end

end LeanFormal.IUT.XiFPaper.S2096BaseChangePartialActual
end
