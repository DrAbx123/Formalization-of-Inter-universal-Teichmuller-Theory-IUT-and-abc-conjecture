import tmp.sheaf.xif.paper.AbsTopIII05RefinedActual
import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-!
# Mzk1AbsTopIII05RefinedConcreteActual — concrete instantiations of the refined D1-D4
interfaces (Prop 5.8(i)/(ii), Cor 5.5, Section-0 oriented graph data)

STEP 0 prior-art: AbsTopIII05RefinedActual (typed D1-D4 interfaces), Mzk1Prop58iConcreteActual
(concrete invariant data, p* formula, preLogShell ⊆ unitLayer), Mzk1Prop58iiDiagramActual
(NonDiagramModel / bridge identification / D^bullet row record),
SourceThetaLinkGraphAutomorphismReduction (Z-graph automorphisms, chainTranslation_graphAut)
-> REUSE; no new deep mathematics.

WHAT: instantiate the four refined deep-input structures with the concrete model content that
is actually available, keeping the genuinely deep anabelian parts as the structures' named
Prop fields:
* D1: Prop58iLocalFieldReconstruction inhabited by the concrete invariant data;
* D2: Prop58iiLogShellReconstruction with gammaXNon/logShell/diagram from the source log-shell
  datum and the PROVED preLogShell ⊆ unitLayer as the functoriality field;
* D3: Cor55LogFrobeniusCompatibility with the two bridge consequences
  (unitLayer ⊆ logShell and logShell = invScaledUnitLayer) as its named compatibility fields
  (proved under the bridge hypothesis h), and the tree calibration anchor;
* D4: OrientedGraphAnabelianData with the PROVED Z-action graph automorphism family as the
  combinatorial-data field and the tree Z-action anchor.
The bundle RefinedDeepInputs is then inhabited concretely for any source datum satisfying the
bridge hypothesis.  This is a CONCRETE INSTANTIATION of the interfaces, not a proof of the
paper's group-theoretic algorithms.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05RefinedConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

/-- Concrete D1: the invariant data of Prop 5.8(i) (inhabits the typed D1 interface). -/
def concreteD1 (D : SourceLogShellDatum.{u}) (f e m : ℕ) :
    Prop58iLocalFieldReconstruction D.K :=
  prop58iD1 D f e m

/-- Concrete D2: the log-shell diagram data of Prop 5.8(ii) with the proved
preLogShell ⊆ unitLayer as the functoriality field. -/
def concreteD2 (D : SourceLogShellDatum.{u}) : Prop58iiLogShellReconstruction D.K where
  gammaXNon := D.Units
  logShell := D.logShell
  diagram := fun _ => D.preLogShell
  functorial := D.preLogShell ⊆ D.unitLayer
  functorial_proof := Mzk1Prop58iConcreteActual.preLogShell_subset_unitLayer D

/-- Concrete D3: the bridge consequences as the global/panalocal compatibility fields, with
the tree calibration anchor (default field of the structure). -/
def concreteD3 (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : Cor55LogFrobeniusCompatibility where
  globalCompatibility := D.unitLayer ⊆ D.logShell
  globalCompatibility_proof := D.codomainKummerContained_of_invariantImageIdentification h
  panalocalCompatibility := D.logShell = D.invScaledUnitLayer
  panalocalCompatibility_proof :=
    D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- Concrete D4: the PROVED Z-action family of oriented-graph automorphisms as the
combinatorial-data field (the general Gamma^x_v combinatorial anabelian data stays named
outside this concrete instantiation). -/
def concreteD4 : OrientedGraphAnabelianData where
  combinatorialData := ∃ k : ℤ, FrobeniusPictureGraphAut (chainTranslation k)
  combinatorialData_proof := ⟨0, chainTranslation_graphAut 0⟩

/-- The concrete bundle: all four refined interfaces instantiated concretely. -/
def refinedDeepInputsConcrete (D : SourceLogShellDatum.{u}) (f e m : ℕ)
    (h : SourceLogShellInvariantImageIdentification D) :
    RefinedDeepInputs D.K D.K where
  d1 := concreteD1 D f e m
  d2 := concreteD2 D
  d3 := concreteD3 D h
  d4 := concreteD4

/-- The concrete D4 combinatorial-data field is exactly the Z-graph automorphism family
(tree Section-0 object). -/
theorem concreteD4_combinatorialData :
    concreteD4.combinatorialData :=
  concreteD4.combinatorialData_proof

/-- The concrete bundle's D2 functoriality field is the proved preLogShell ⊆ unitLayer. -/
theorem refinedDeepInputsConcrete_d2_functorial (D : SourceLogShellDatum.{u}) (f e m : ℕ)
    (h : SourceLogShellInvariantImageIdentification D) :
    (refinedDeepInputsConcrete D f e m h).d2.functorial :=
  (refinedDeepInputsConcrete D f e m h).d2.functorial_proof

/-- The concrete bundle's D3 fields are the two bridge consequences. -/
theorem refinedDeepInputsConcrete_d3_global (D : SourceLogShellDatum.{u}) (f e m : ℕ)
    (h : SourceLogShellInvariantImageIdentification D) :
    (refinedDeepInputsConcrete D f e m h).d3.globalCompatibility :=
  (refinedDeepInputsConcrete D f e m h).d3.globalCompatibility_proof

/-- Calibration-model instance of the concrete refined bundle: the bridge hypothesis holds by
the tree calibration theorem. -/
theorem refinedDeepInputsConcrete_calibration (f e m : ℕ) :
    Nonempty (RefinedDeepInputs sourceLogShellCalibrationDatum.K
      sourceLogShellCalibrationDatum.K) :=
  ⟨refinedDeepInputsConcrete sourceLogShellCalibrationDatum f e m
    sourceLogShellCalibration_invariantImageIdentification⟩

/-- Instantiation rows: (refined interface, concrete content, status). -/
def refinedConcreteRows : List (String × String × String) :=
  [ ("D1 Prop58iLocalFieldReconstruction", "concrete invariants (p,p*,p^f,degree,e,p^m; unit/invariant images)", "CONCRETE INSTANCE (deep algorithm still named)"),
    ("D2 Prop58iiLogShellReconstruction", "gammaXNon=Units, logShell=D.logShell, diagram=preLogShell; functorial := preLogShell⊆unitLayer (proved)", "CONCRETE INSTANCE (functorial algorithm still named)"),
    ("D3 Cor55LogFrobeniusCompatibility", "global := unitLayer⊆logShell; panalocal := logShell=invScaledUnitLayer (both proved under bridge h); tree calibration anchor", "CONCRETE INSTANCE under h (D^bullet diagram still named)"),
    ("D4 OrientedGraphAnabelianData", "combinatorialData := ∃k, FrobeniusPictureGraphAut (chainTranslation k) (proved); tree Z-action anchor", "CONCRETE INSTANCE (general combinatorial anabelian data still named)"),
    ("RefinedDeepInputs bundle", "refinedDeepInputsConcrete D f e m h", "INHABITED concretely for any D + bridge h; calibration instance Nonempty") ]

/-- The refined-concrete row record has five rows. -/
theorem refinedConcreteRows_length : refinedConcreteRows.length = 5 := rfl

#check concreteD1
#check concreteD2
#check concreteD3
#check concreteD4
#check refinedDeepInputsConcrete
#check concreteD4_combinatorialData
#check refinedDeepInputsConcrete_calibration
#check refinedConcreteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05RefinedConcreteActual
end
