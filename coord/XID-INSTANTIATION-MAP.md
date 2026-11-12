# XID-INSTANTIATION-MAP — instantiate StepXiDData with faithful lana definitions (A1116)

Status: design map; no compile.

## 1. Current target (Mzk1XiDTargetActual.lean)

structure StepXiDData where
  Ω : Type
  logVol : Set Ω -> Real
  qRegion : Set Ω
  thetaRegion : Set Ω
  qPilotLhs : Real
  rhs : Real
  containment : thetaRegion subset qRegion
  logVol_mono : forall S T, S subset T -> logVol T <= logVol S
  q_vol : logVol qRegion = qPilotLhs
  theta_vol : logVol thetaRegion = rhs
  detComparison : Prop

Bridge: target_of_stepXiD : StepXiDData -> qPilotLhs <= rhs (proved by
rw [<- q_vol, <- theta_vol]; exact logVol_mono containment).

The file reserves imports:
tmp.external.ported.lana_core.Iut.WallEquiv.Gap, VcI, Forms,
tmp.external.ported.lana_core.Iut.Concrete.ThetaRegion, LocalTheory,
LocalConstruct.Volume, Packet, ScaleVolume, IndAut.
Current lana_core port does NOT contain Gap/ThetaRegion/VcI sources or oleans
(only 2 oleans); the map below uses tmp/sheaf/lana sources.

## 2. Faithful definitions and signatures

incl (tmp/sheaf/lana/iut/Iut/Concrete/LocalConstruct/Packet.lean:642):
  noncomputable def incl (K) (p) (c) (j) (w) (h : c j = Place.finite w) :
    completionAt K w ->+* Tensor K (.finite p) c.
It is a ring hom (inclusion of the j-th tensor factor); isUnit_incl (Packet:651).

scaleEltAt (tmp/sheaf/lana/iut/Iut/Concrete/ThetaRegion.lean:126):
  noncomputable def scaleEltAt (i : Fin n) (p) (c) (l : Lab n i) :
    Tensor K (.finite p) (tuple ... c) :=
  incl ... (qroot ...) ^ (i.1+1)^2.
scaleElt (ThetaRegion:136):
  scaleElt i p c := scaleEltAt n i p c (distinguished n i).
isUnit_scaleEltAt/isUnit_scaleElt (ThetaRegion:141/146).

leastHull (Gap.lean:87):
  def leastHull (vQ) (c : ι -> Place K) (U : Set (Tensor K vQ c)) :
    Set (Tensor K vQ c) :=
  iInter over b unit with U subset b • integral of b • integral.
Lemmas:
- leastHull_subset (Gap:93).
- leastHull_eq (Gap:97).
- leastHull_smul_integral (Gap:138): leastHull (a • integral) = a • integral.
- leastHull_units_smul (Gap:148):
  leastHull (s • U) = s • leastHull U for IsUnit s and admissible U.
- leastHull_mono (Gap:422):
  U subset V -> leastHull U subset leastHull V.
- componentVol_le_leastHull (Gap:130):
  componentVol X <= componentVol (leastHull U) for X subset U admissible.

thetaFiniteOn (ThetaRegion:170):
  union over phi in indAut of phi '' (union l in S, scaleEltAt l • shell).
thetaComponentOn (ThetaRegion:178) matches finite/infinite.
thetaComponent (ThetaRegion:257):
  thetaComponent i vQ c := thetaComponentOn i (ivLabels) vQ c.
ivLabels (ThetaRegion:237) = {distinguished}; litLabels (:241) = univ.
thetaFinite_eq (ThetaRegion:261):
  thetaFinite i p c = union over phi in indAut, phi '' (scaleElt • shell).
thetaComponentOn_admissible (ThetaRegion:186).

indAut (IndAut.lean:302):
  def indAut (vQ) (c) : Set (Tensor K vQ c -> Tensor K vQ c)
  | .finite p, c => tensorAut p c
  | .infinite, c => archIndAut c.
id_mem_indAut (IndAut:310).

## 3. Field mapping

Local (single capsule i, place vQ, tuple c):

| StepXiDData field | faithful candidate | required lemma/status |
|---|---|---|
| Ω | Tensor K vQ c | type |
| logVol | fun S => - componentVol K vQ c S (negative-log) | componentVol (Volume:196); sign convention |
| qRegion | scaleElt i p c • shell K p (tuple c) (finite p) | scaleElt, shell |
| thetaRegion | thetaComponent i (.finite p) c = thetaFinite i p c | thetaComponent; thetaFinite_eq |
| containment | (scaleElt • shell) subset thetaFinite | thetaFinite_eq + id_mem_indAut + Set.subset_iUnion |
| logVol_mono | monotone under subset from componentVol_le_of_subset, sign reversed | componentVol_le_of_subset (Volume) |
| qPilotLhs | -(qOrder * log p)/(2*l) or -(ordp scaleElt)*log p | qroot/ordp |
| rhs | theta hull volume, -componentVol (leastHull thetaComponent) | componentVol_le_leastHull |
| q_vol | -componentVol(scaleElt • shell) = qPilotLhs | units scaling (ScaleVolume/IdentifiedCopies) |
| theta_vol | -componentVol(leastHull thetaComponent) = rhs | leastHull/theta lemmas |
| detComparison | Form C: globalLogVolume det <= globalLogVolume q | open |

Global (Region D):
- Ω := Region D (dependent forall i, AdmissibleRegion i);
- logVol := Wall.logVol D (LogVolumeData.processionVol);
- qRegion := qRegion D (Iut/Wall/QPilotRegion);
- thetaRegion := hullOf D (D.thetaPilot (nC D)) or thetaPilot region;
- containment := regionwise q/theta inclusion; direction must match paper/A1049;
- logVol_mono := logVol monotonicity from componentVol_le_of_subset;
- qPilotLhs := (concreteVariantData D).qPilot.lhs;
- rhs := (concreteVariantData D).rhsData.rhs; rhs_eq_logVol (Rss:356).

Type mismatch: StepXiDData.logVol : Set Ω -> Real, but faithful logVol is a function
on Region D, not on Set (Region D). Two options:
1. Local instantiation with Ω = Tensor K vQ c and logVol = -componentVol.
2. Global instantiation with Ω = Region D and logVol := Wall.logVol, but then
   qRegion/thetaRegion are single regions, not subsets of Set Ω; replace the
   structure by a region-level version or use singleton sets and a
   Set-lift of logVol (not currently defined).
Option 1 is the honest local bridge; option 2 needs a new structure.

## 4. Lemma checklist

- incl monotonicity: incl is a ring hom; set monotonicity is generic
  Set.image_mono; no special incl-subset lemma in lana. isUnit_incl (Packet:651)
  gives unit of factor.
- leastHull_scaleElt: derive from leastHull_units_smul (Gap:148) +
  isUnit_scaleElt (ThetaRegion:146):
  leastHull (scaleElt • U) = scaleElt • leastHull U.
- thetaComponent containment: from thetaFinite_eq (ThetaRegion:261) and
  id_mem_indAut; the union over indAut contains the identity image.
- q_vol: scaling volume of a • shell = a • integral + shell:
  componentVol_units_smul / componentVol_prod_incl_smul from
  LocalConstruct.ScaleVolume/Volume; ordp scaleElt = (i+1)^2 * ordp qroot.
- theta_vol: componentVol_le_leastHull and leastHull_admissible; the hull value
  is rhs by definition of rhs (Rss:356).
- detComparison: Form C rank-one line-bundle comparison; not yet.

## 5. Verdict

- The faithful local instantiation is feasible in principle:
  Omega = Tensor K vQ c, logVol = -componentVol,
  qRegion = scaleElt • shell, thetaRegion = thetaComponent,
  containment from thetaFinite_eq/id_mem_indAut.
- Missing/needed:
  1. lana_core files Gap/ThetaRegion/VcI/Packet/Volume/ScaleVolume/IndAut must
     be ported or imported from tmp/sheaf/lana and compiled;
  2. the global Region D version needs a new structure (logVol on regions,
     not on Set Omega);
  3. q_vol/theta_vol need the scaling and hull-volume lemmas;
  4. detComparison remains Form C (open).
- The current Mzk1XiDTargetActual imports are reserved and not compilable until
  lana_core is green; no fake inhabitant is provided.
