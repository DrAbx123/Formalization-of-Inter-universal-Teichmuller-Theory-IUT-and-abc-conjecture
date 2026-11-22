/-
# S2563: coherent-cover restriction of S2559HasLiftUnique and EssSurj

`S2563CoherentCover X` is exactly the concrete-witness hypothesis
`S2559HasLiftUnique X.finiteEtale`.  It holds for every cover in the image of
`S2517InvObj` (S2561S2517HasLiftUnique) and for the terminal identity cover
(S2560S2514TerminalCoverLiftUnique).  Essential surjectivity is then restricted
to representable coherent covers; the all-cover form is false by the S2541
audit.
-/
import tmp.sheaf.xif.paper.S2560S2514LiftUniqueActual
import tmp.sheaf.xif.paper.S2561S2512LiftUniqueActual
import tmp.sheaf.xif.paper.S2562CorrectedEssSurjLiftUniqueActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2555ExtractionTransportActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2561S2512LiftUniqueActual
open LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2563CoherentCoverEssSurjActual

/-- A cover is coherent when its finite-etale structure carries lift
uniqueness (concrete S2512/S2514 witness). -/
def S2563CoherentCover (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) : Prop :=
  S2559HasLiftUnique X.finiteEtale

theorem S2563CoherentCover_S2517InvObj
    (C : FiniteEtaleCover S2482AffineScheme) :
    S2563CoherentCover (S2517InvObj C) :=
  S2561S2517HasLiftUnique C

theorem S2563CoherentCover_terminal :
    S2563CoherentCover S2514TerminalCover :=
  S2562HasLiftUnique_terminalCover

/-- Representable coherent essential surjectivity. -/
def S2563EssSurjOnCoherent : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    S2541Representable X →
      S2563CoherentCover X →
      ∃ C : FiniteEtaleCover S2482AffineScheme,
        Nonempty (S2517InvObj C ≅ X)

theorem S2563EssSurjOnCoherent_of_triangle
    (hRes : S2562ExtractionIsoFromTriangle)
    (hCov : S2562CanonicalCoverIsoFromData) :
    S2563EssSurjOnCoherent := by
  intro X hX hcoh
  obtain ⟨S, hS⟩ := hX
  let I_res := S2562ExtractionIsoFromLiftUnique_of_triangle hRes
  refine ⟨S2562CanonicalCover I_res S hS hcoh,
    hCov X S hS (S2562CanonicalData I_res S hS hcoh)⟩

#check S2563CoherentCover
#check S2563CoherentCover_S2517InvObj
#check S2563CoherentCover_terminal
#check S2563EssSurjOnCoherent
#check S2563EssSurjOnCoherent_of_triangle
#print axioms S2563CoherentCover_S2517InvObj
#print axioms S2563CoherentCover_terminal
#print axioms S2563EssSurjOnCoherent_of_triangle
end LeanFormal.IUT.XiFPaper.S2563CoherentCoverEssSurjActual
end