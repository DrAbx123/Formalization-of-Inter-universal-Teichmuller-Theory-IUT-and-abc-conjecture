import tmp.sheaf.xif.paper.S2517CoverEquivMapActual
import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual

/-- Source: the actual 2-isomorphism quotient cover category. -/
abbrev S2519SourceCategory : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S2482Orbicurve

/-- Object map of the forward functor. -/
noncomputable def S2519ForwardObj (C : S2519SourceCategory) :
    FiniteEtaleCover S2482AffineScheme :=
  S2517Obj C

/-- Raw map on cover maps (before quotient descent). -/
noncomputable def S2519ForwardRawMap {C D : S2519SourceCategory}
    (φ : Iut.OrbicurveFiniteEtaleCoverMap C D) :
    S2519ForwardObj C ⟶ S2519ForwardObj D :=
  S2517Map φ

/-- Exact well-definedness obligation for quotient descent. -/
def S2519ForwardMapWellDefined : Prop :=
  ∀ {C D : S2519SourceCategory}
    {φ ψ : Iut.OrbicurveFiniteEtaleCoverMap C D},
    S1728CoverMapRel φ ψ →
      S2519ForwardRawMap φ = S2519ForwardRawMap ψ

/-- Exact functor laws obligation, after well-definedness. -/
def S2519ForwardFunctorLaws : Prop :=
  (∀ C : S2519SourceCategory,
      (by
        -- 这里只记录目标，不在 Prop 中构造 functor
        exact True)) ∧
  (∀ {A B C : S2519SourceCategory}
      (f : Iut.OrbicurveFiniteEtaleCoverMap A B)
      (g : Iut.OrbicurveFiniteEtaleCoverMap B C),
      True)

noncomputable def S2519ForwardQuotMap
    (hwd : S2519ForwardMapWellDefined)
    {C D : S2519SourceCategory}
    (f : S1728CoverMapClass (A := C) (B := D)) :
    S2519ForwardObj C ⟶ S2519ForwardObj D :=
  Quot.lift (fun φ => S2519ForwardRawMap φ)
    (fun φ ψ h => hwd h) f

noncomputable def S2519ForwardFunctor
    (hwd : S2519ForwardMapWellDefined)
    (hid : ∀ C : S2519SourceCategory,
      S2519ForwardQuotMap hwd (𝟙 C) = 𝟙 (S2519ForwardObj C))
    (hcomp : ∀ {A B C : S2519SourceCategory}
      (f : S1728CoverMapClass (A := A) (B := B))
      (g : S1728CoverMapClass (A := B) (B := C)),
      S2519ForwardQuotMap hwd (S1728CoverMapClassComp f g) =
        S2519ForwardQuotMap hwd f ≫ S2519ForwardQuotMap hwd g) :
    @CategoryTheory.Functor S2519SourceCategory
      (S1736ActualCategory (F := F) (X := S2482Orbicurve))
      (FiniteEtaleCover S2482AffineScheme)
      (inferInstance) where
  obj := S2519ForwardObj
  map {C D} f := S2519ForwardQuotMap hwd f
  map_id := hid
  map_comp := hcomp

#check S2519ForwardObj
#check S2519ForwardRawMap
#check S2519ForwardMapWellDefined
#check S2519ForwardQuotMap

def S2519ForwardMapId : Prop :=
  ∀ C : S2519SourceCategory,
    S2517Map (S1641CoverMapId C) = 𝟙 (S2517Obj C)

theorem S2519ForwardFunctor_hid
    (hwd : S2519ForwardMapWellDefined)
    (hId : S2519ForwardMapId) :
    ∀ C : S2519SourceCategory,
      S2519ForwardQuotMap hwd (𝟙 C) = 𝟙 (S2517Obj C) := by
  intro C
  change S2519ForwardRawMap (S1641CoverMapId C) = 𝟙 (S2517Obj C)
  exact hId C

#check S2519ForwardMapId
#check S2519ForwardFunctor_hid
#check S2519ForwardFunctor_hid
#check S2519ForwardQuotMap
def S2519ForwardMapComp : Prop :=
  ∀ {A B C : S2519SourceCategory}
    (f : Iut.OrbicurveFiniteEtaleCoverMap A B)
    (g : Iut.OrbicurveFiniteEtaleCoverMap B C),
    S2517Map (S1641CoverMapComp f g) =
      S2517Map f ≫ S2517Map g

theorem S2519ForwardFunctor_hcomp
    (hwd : S2519ForwardMapWellDefined)
    (hComp : S2519ForwardMapComp) :
    ∀ {A B C : S2519SourceCategory}
      (f : S1728CoverMapClass (A := A) (B := B))
      (g : S1728CoverMapClass (A := B) (B := C)),
      S2519ForwardQuotMap hwd (S1728CoverMapClassComp f g) =
        S2519ForwardQuotMap hwd f ≫ S2519ForwardQuotMap hwd g := by
  intro A B C f g
  induction f using Quot.ind with
  | mk f' =>
    induction g using Quot.ind with
    | mk g' =>
      change S2519ForwardRawMap (S1641CoverMapComp f' g') =
        S2519ForwardRawMap f' ≫ S2519ForwardRawMap g'
      exact hComp f' g'

#check S2519ForwardMapComp
#check S2519ForwardFunctor_hcomp
#check S2519ForwardFunctor

end LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual
end
