import tmp.sheaf.xif.paper.S2161BaseChangeAPIActual
import tmp.sheaf.xif.paper.S2096StackMorphismActual
import tmp.sheaf.xif.paper.S1943AssembleEssSurjActual

/-! # S2165: scheme-side base-changed presentation data for S2096BaseChangeStatement

Given a presentation Q of m at vy over A and a finite-etale s : T -> A, this
file constructs the base-change apex and its two Over-projections, and the
scheme-representable base-changed projection.  The commutes 2-cell and the
weak witness transport are recorded separately; no witness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual

open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2161BaseChangeAPIActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- The base-change apex: pullback of `Q`'s apex along `s`, as an object over
`Spec F`. -/
noncomputable def S2165Apex : SchemeOverField S1726K :=
  Over.mk (Limits.pullback.fst (f := Q.projection.left) (g := s.left) ≫
    Q.pullbackScheme.hom)

/-- First projection to `Q`'s apex. -/
noncomputable def S2165Fst : S2165Apex (m := m) (s := s) (vy := vy) (Q := Q) ⟶ Q.pullbackScheme :=
  Over.homMk (Limits.pullback.fst (f := Q.projection.left) (g := s.left)) rfl

/-- Second projection to the test scheme `T`. -/
noncomputable def S2165Snd : S2165Apex (m := m) (s := s) (vy := vy) (Q := Q) ⟶ T :=
  Over.homMk (Limits.pullback.snd (f := Q.projection.left) (g := s.left)) (by
    show Limits.pullback.snd (f := Q.projection.left) (g := s.left) ≫ T.hom =
      Limits.pullback.fst (f := Q.projection.left) (g := s.left) ≫
        Q.pullbackScheme.hom
    rw [← s.w, ← Category.assoc, ← Limits.pullback.condition, Category.assoc,
      Q.projection.w])

theorem S2165Square :
    S2165Fst (m := m) (s := s) (vy := vy) (Q := Q) ≫ Q.projection = S2165Snd (m := m) (s := s) (vy := vy) (Q := Q) ≫ s := by
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

/-- The base-changed projection is scheme-representable (S2161). -/
noncomputable def S2165ProjectionMap
    (hs : IsFinite s.left) (hse : Etale s.left)
    (hq : IsFinite (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)
    (hqe : Etale (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left) :
    SchemeRepresentableMap (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)) :=
  S2161SchemeRepresentableMapBaseChange
    (g := Q.projection) (s := s)
    (R := S2165Apex (m := m) (s := s) (vy := vy) (Q := Q))
    (q := S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
    (r := S2165Fst (m := m) (s := s) (vy := vy) (Q := Q))
    (_hsq := S2165Square (m := m) (s := s) (vy := vy) (Q := Q))
    Q.projectionMap hs hse hq hqe
#print axioms S2165Square
#check S2165Apex
#check S2165ProjectionMap

end LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual

end
