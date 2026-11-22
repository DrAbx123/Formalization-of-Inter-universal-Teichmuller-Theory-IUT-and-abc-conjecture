import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1Prop58iiDiagramActual — Prop 5.8(ii) concrete diagram-object layer

STEP 0 prior-art: LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier (SourceLogShellDatum:
p, p*, K, Units, invariants, logMap; preLogShell, logShell, unitLayer, codomainKummerContained),
SourceLogShellAbsTopIIIBridge (SourceLogShellInvariantImageIdentification at :70, calibration
theorem at :178, invScaledUnitLayer at :133, logShell_eq_invScaledUnitLayer at :139,
codomainKummerContained_of_invariantImageIdentification at :98), and the deferred
AbsTopIII05Refined typed interfaces -> REUSE; no new deep mathematics and no high-level wiring.

WHAT THIS FILE DOES (Prop 5.8(ii), corpus l.8059-8160):
* builds the CONCRETE model of the Gamma^x_non diagram vertices on a SourceLogShellDatum:
  O^◇/k^×/k^~/(k^×)^pf are represented by the datum's Units/invariants/log coordinates, the
  log-shell I(G) by D.logShell, and the concrete unit image (p*_v)^{-1} log_k(O^×_k) by
  D.invScaledUnitLayer;
* PROVES the model-level inclusion preLogShell ⊆ unitLayer, and re-exports the two bridge
  theorems that identify the Kummer/unit image with the log-shell (unitLayer ⊆ logShell) and
  the abstract log-shell with (p*_v)^{-1}·unitLayer under the hypothesis h whose tree content
  is "the invariant image identification on the frozen calibration model";
* the genuinely deep parts stay NAMED, with the exact original object written down:
  (N1) the gamma^x_non-diagram in CMLF_TS^+ (corpus l.8112-8134),
  (N2) the functorial group-theoretic algorithm Ob(TG^+) ∋ G |-> Gamma^x_non(G) (Prop 5.8(ii)),
  (N3) the embedding k^~(G) ↪ (k^×)^pf(G) of the second line of the diagram;
* records the seven rows of the Cor-5.5 diagram D^bullet as data rows with their model anchors.
No axiom/sorry; nothing here is claimed as the paper's diagram (only its concrete reduced model).
Registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

/-- The carrier of the concrete reduced CMLF_TF^+ model at a source log-shell datum: the
log-coordinate field together with the unit group; the paper's CMLF_TF^+ category is NOT
constructed (named N1 below). -/
structure CMLFCarrier (D : SourceLogShellDatum.{u}) where
  logCoordinates : Type u := D.K
  units : Type u := D.Units
  logMap : D.Units →* Multiplicative D.K := D.logMap

/-- The concrete vertex data of the Gamma^x_non diagram model: the unit image, the invariant
(pre-log-shell) image, the log-shell and the concrete (p*_v)^{-1}-scaled unit image, together
with the PROVED model-level inclusion preLogShell ⊆ unitLayer. -/
structure NonDiagramModel (D : SourceLogShellDatum.{u}) where
  unitImage : Set D.K := D.unitLayer
  invariantImage : Set D.K := D.preLogShell
  logShellSet : Set D.K := D.logShell
  invScaledUnitImage : Set D.K := D.invScaledUnitLayer
  preLogShell_le_unitLayer : D.preLogShell ⊆ D.unitLayer := by
    intro a ha
    rcases ha with ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩

/-- The model-level inclusion preLogShell ⊆ unitLayer (standalone form). -/
theorem preLogShell_subset_unitLayer (D : SourceLogShellDatum.{u}) :
    D.preLogShell ⊆ D.unitLayer := by
  intro a ha
  rcases ha with ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

/-- The model-level vertex data exists for every source log-shell datum. -/
def nonDiagramModel (D : SourceLogShellDatum.{u}) : NonDiagramModel D := {}

/-- Under the bridge hypothesis (the invariant image identification, whose tree content is the
frozen calibration model), the concrete unit image lies in the log-shell — the model-level
Kummer inclusion of the Gamma^x_non diagram (corpus l.8123-8134). -/
theorem unitLayer_subset_logShell_of_invariantImageIdentification
    (D : SourceLogShellDatum.{u}) (h : SourceLogShellInvariantImageIdentification D) :
    D.unitLayer ⊆ D.logShell :=
  D.codomainKummerContained_of_invariantImageIdentification h

/-- Under the bridge hypothesis, the abstract log-shell equals the concrete
(p*_v)^{-1}·log_k(O^×_k): model-level identification of the I(G) vertex. -/
theorem logShell_eq_invScaled_of_invariantImageIdentification
    (D : SourceLogShellDatum.{u}) (h : SourceLogShellInvariantImageIdentification D) :
    D.logShell = D.invScaledUnitLayer :=
  D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- NAMED deep inputs of Prop 5.8(ii): the parts of the original statement that are not
constructed here.  Each is an explicit Prop with a proof field, so the object below is
CONDITIONAL on them (never asserted true). -/
structure Prop58iiNamedInput (D : SourceLogShellDatum.{u}) where
  /-- N1: the Gamma^x_non-diagram in CMLF_TF^+ (corpus l.8112-8134). -/
  gammaXNonDiagram : Prop
  gammaXNonDiagram_proof : gammaXNonDiagram
  /-- N2: the functorial group-theoretic algorithm Ob(TG^+) ∋ G |-> Gamma^x_non(G)
  (Prop 5.8(ii), corpus l.8097-8111). -/
  groupTheoreticAlgorithm : Prop
  groupTheoreticAlgorithm_proof : groupTheoreticAlgorithm
  /-- N3: the embedding k^~(G) ↪ (k^×)^pf(G) of the second diagram line
  (corpus l.8135-8160). -/
  simIntoPfEmbedding : Prop
  simIntoPfEmbedding_proof : simIntoPfEmbedding

/-- The conditional Prop 5.8(ii) diagram object: concrete carrier + model vertices + the
bridge identification hypothesis + the three named deep inputs. -/
structure Prop58iiDiagramObject (D : SourceLogShellDatum.{u}) where
  carrier : CMLFCarrier D := {}
  model : NonDiagramModel D := nonDiagramModel D
  invariantImageIdentification : SourceLogShellInvariantImageIdentification D
  named : Prop58iiNamedInput D

/-- The unit/pre-log-shell/log-shell vertex relations extracted from a diagram object: the
proved model-level inclusion, the Kummer inclusion under the bridge hypothesis, and the
log-shell identification. -/
theorem Prop58iiDiagramObject.vertexRelations (D : SourceLogShellDatum.{u})
    (O : Prop58iiDiagramObject D) :
    D.preLogShell ⊆ D.unitLayer ∧ D.unitLayer ⊆ D.logShell ∧
      D.logShell = D.invScaledUnitLayer :=
  ⟨preLogShell_subset_unitLayer D,
    unitLayer_subset_logShell_of_invariantImageIdentification D O.invariantImageIdentification,
    logShell_eq_invScaled_of_invariantImageIdentification D O.invariantImageIdentification⟩

/-- The seven rows of the Cor-5.5 diagram D^bullet as DATA rows: each row is recorded with
its component and the concrete model anchor in this file.  Row indices are the paper's first
seven rows (X, X^log, X^*, the identity functors id_gamma, the N^+_v / lambda^+_v row, the E^*
row, and the An^*[X] row); their actual construction is NOT claimed (named N1). -/
structure Cor55DiagramRow where
  row : Fin 7
  component : String
  modelAnchor : String

/-- The seven-row record of the D^bullet diagram (corpus l.7347-7385). -/
def cor55DiagramRows : List Cor55DiagramRow :=
  [ ⟨⟨0, by omega⟩, "X (first row: sources)", "CMLFCarrier.logCoordinates"⟩
  , ⟨⟨1, by omega⟩, "X^log (log-arrows of Def 5.4(ii))", "SourceLogShellDatum.logMap"⟩
  , ⟨⟨2, by omega⟩, "X^*", "CMLFCarrier.units"⟩
  , ⟨⟨3, by omega⟩, "identity functors id_gamma (gamma in L)", "not modeled (named N1)"⟩
  , ⟨⟨4, by omega⟩, "N^+_v / lambda^+_v (v in V(F_mod))", "D.logShell / D.invScaledUnitLayer"⟩
  , ⟨⟨5, by omega⟩, "E^* (Theta-picture category)", "not modeled (named N1)"⟩
  , ⟨⟨6, by omega⟩, "An^*[X] (fifth-seventh row equivalences)", "not modeled (named N1)"⟩ ]

/-- The D^bullet row record has seven rows. -/
theorem cor55DiagramRows_length : cor55DiagramRows.length = 7 := rfl

/-- Model rows: (component, model anchor, status). -/
def prop58iiModelRows : List (String × String × String) :=
  [ ("O^◇_k / O^×_k (unit layer)", "D.unitLayer = image of logMap on Units", "CONCRETE MODEL (proved definitions)"),
    ("invariant image / pre-log-shell", "D.preLogShell", "CONCRETE MODEL + proved preLogShell ⊆ unitLayer"),
    ("log-shell I(G)", "D.logShell = p*^{-1} preLogShell", "CONCRETE MODEL (proved definitions)"),
    ("(p*_v)^{-1} log_k(O^×_k)", "D.invScaledUnitLayer", "CONCRETE MODEL (proved definition)"),
    ("Kummer inclusion O^×_k -> I", "D.codomainKummerContained under bridge h", "PROVED conditional on h (bridge theorem reused)"),
    ("I(G) = (p*_v)^{-1} log_k(O^×_k)", "logShell_eq_invScaledUnitLayer under bridge h", "PROVED conditional on h (bridge theorem reused)"),
    ("Gamma^x_non diagram in CMLF_TF^+", "Prop58iiNamedInput.gammaXNonDiagram", "NAMED (corpus l.8112-8134)"),
    ("group-theoretic algorithm Ob(TG^+) -> Gamma^x_non(G)", "Prop58iiNamedInput.groupTheoreticAlgorithm", "NAMED (Prop 5.8(ii))"),
    ("k^~(G) -> (k^×)^pf(G) embedding", "Prop58iiNamedInput.simIntoPfEmbedding", "NAMED (corpus l.8135-8160)"),
    ("Cor 5.5 D^bullet seven rows", "cor55DiagramRows", "DATA ROWS (construction named N1)") ]

/-- The model row record has ten rows. -/
theorem prop58iiModelRows_length : prop58iiModelRows.length = 10 := rfl

/-- Calibration model instantiation of the concrete part: the frozen calibration datum
satisfies the bridge hypothesis via the tree's proved calibration theorem, hence the concrete
vertex relations hold there (the named deep inputs stay parameters). -/
theorem calibration_vertexRelations :
    sourceLogShellCalibrationDatum.preLogShell ⊆ sourceLogShellCalibrationDatum.unitLayer ∧
      sourceLogShellCalibrationDatum.unitLayer ⊆ sourceLogShellCalibrationDatum.logShell ∧
      sourceLogShellCalibrationDatum.logShell =
        sourceLogShellCalibrationDatum.invScaledUnitLayer :=
  ⟨preLogShell_subset_unitLayer _,
    unitLayer_subset_logShell_of_invariantImageIdentification _
      sourceLogShellCalibration_invariantImageIdentification,
    logShell_eq_invScaled_of_invariantImageIdentification _
      sourceLogShellCalibration_invariantImageIdentification⟩

#check NonDiagramModel
#check Prop58iiNamedInput
#check Prop58iiDiagramObject
#check Prop58iiDiagramObject.vertexRelations
#check cor55DiagramRows_length
#check prop58iiModelRows_length
#check calibration_vertexRelations

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual
end
