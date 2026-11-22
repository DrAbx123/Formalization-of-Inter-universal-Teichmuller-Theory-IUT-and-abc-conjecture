import tmp.sheaf.xif.paper.S2519ForwardFunctorActualMap
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2519ForwardFunctorPartialActual
open LeanFormal.IUT.XiFPaper.S2519ForwardFunctorActualMap
open LeanFormal.IUT.XiFPaper.S2523MapHomEqActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
example (C : S2519SourceCategory) :
    S2519ForwardQuotMapActual (𝟙 C) = 𝟙 (S2519ForwardObj C) := by
  change S2519ForwardQuotMap S2523ForwardMapWellDefined
      (S1728CoverMapClassId C) = 𝟙 (S2519ForwardObj C)
  dsimp [S1728CoverMapClassId, S2519ForwardQuotMap]
  change S2517Map (S1641CoverMapId C) = 𝟙 (S2517Obj C)
  dsimp [S2517Map, S2517Obj, S1641CoverMapId, S2517MapHom]
  trace_state
  sorry
