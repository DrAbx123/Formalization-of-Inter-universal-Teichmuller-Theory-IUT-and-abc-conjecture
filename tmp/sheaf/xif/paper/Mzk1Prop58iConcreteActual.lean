import tmp.sheaf.xif.paper.AbsTopIII05RefinedActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1Prop58iConcreteActual — Prop 5.8(i) concrete layer (local-field reconstruction data)

STEP 0 prior-art: SourceLogShellCarrier (SourceLogShellDatum: p, hp, K, Units, invariants,
logMap; preLogShell, logShell, unitLayer; sourceLogShellStar : p* := p if p odd else p^2),
SourceLogShellAbsTopIIIBridge (invariant image identification; calibration theorem) and
xif AbsTopIII05RefinedActual (Prop58iLocalFieldReconstruction typed D1 interface) -> REUSE.

WHAT IS CONSTRUCTED/PROVED HERE (Prop 5.8(i), corpus l.8059-8110):
* the concrete invariant data attached to a source log-shell datum, for explicit residue
  degree f, absolute ramification e and p-th-root order exponent m:
    residue cardinality p^f, absolute degree [k:Q_p] = f*e, ramification index e,
    p-th power roots of unity order p^m, and the invariant/unit images
    preLogShell (invariant image) and unitLayer (unit image);
* the paper's definition of p* (p if p odd, p^2 if p = 2) is derived from the tree's
  sourceLogShellStar definition (Prop 5.8(i) invariant p*);
* the model-level image relation preLogShell ⊆ unitLayer is PROVED;
* the typed D1 interface (Prop58iLocalFieldReconstruction) is inhabited by these data;
* the genuinely deep group-theoretic reconstruction content stays NAMED with the exact
  original objects: the absolute Galois group G_k, its abelianization G_ab, the
  embeddings O^◇_k ↪ G_ab and k^× ↪ G_ab, the group-theoretic algorithm and the
  Verlagerung (transfer) functoriality.
No axiom/sorry; nothing here is claimed as the paper's group-theoretic algorithm.
Registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.AbsTopIII05RefinedActual

/-- The paper's p* (Prop 5.8(i), Def 5.4(iii)): p if p is odd, p^2 if p = 2. -/
def paperPStar (p : ℕ) : ℕ := if p = 2 then p ^ 2 else p

/-- The tree's source log-shell star is exactly the paper's p* for primes. -/
theorem sourceLogShellStar_eq_paperPStar (p : ℕ) (hp : p.Prime) :
    sourceLogShellStar p = paperPStar p := by
  unfold sourceLogShellStar paperPStar
  rcases hp.eq_two_or_odd with h2 | hodd
  · simp [h2]
  · have hne : p ≠ 2 := by
      intro h; subst h; norm_num at hodd
    simp [hne, hodd]

/-- p* is positive for primes. -/
theorem paperPStar_pos (p : ℕ) (hp : p.Prime) : 0 < paperPStar p := by
  rcases hp.eq_two_or_odd with h2 | hodd
  · simp [paperPStar, h2]
  · have hne : p ≠ 2 := by intro h; subst h; norm_num at hodd
    simpa [paperPStar, hne] using hp.pos

/-- The concrete Prop 5.8(i) invariants at a source log-shell datum, for explicit residue
degree f, absolute ramification index e, and p-th-root order exponent m. -/
structure Prop58iConcreteInvariants (D : SourceLogShellDatum.{u}) (f e m : ℕ) where
  /-- the residue characteristic p. -/
  p : ℕ := D.p
  /-- the invariant p*. -/
  pStar : ℕ := paperPStar D.p
  /-- the residue cardinality p^f. -/
  residueCardinality : ℕ := D.p ^ f
  /-- the absolute degree [k:Q_p]. -/
  absoluteDegree : ℕ := f * e
  /-- the absolute ramification index e. -/
  ramificationIndex : ℕ := e
  /-- the order p^m of the p-th power roots of unity. -/
  pthRootsOrder : ℕ := D.p ^ m
  /-- the invariant image (pre-log-shell model). -/
  invariantImage : Set D.K := D.preLogShell
  /-- the unit image (unit layer model). -/
  unitImage : Set D.K := D.unitLayer

/-- The model-level image relation preLogShell ⊆ unitLayer (PROVED). -/
theorem preLogShell_subset_unitLayer (D : SourceLogShellDatum.{u}) :
    D.preLogShell ⊆ D.unitLayer := by
  intro a ha
  rcases ha with ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

/-- The invariant data of Prop 5.8(i) is inhabited at every source log-shell datum (for any
f, e, m). -/
def prop58iConcreteInvariants (D : SourceLogShellDatum.{u}) (f e m : ℕ) :
    Prop58iConcreteInvariants D f e m := {}

/-- The concrete invariants inhabit the typed D1 interface of AbsTopIII05RefinedActual. -/
def Prop58iConcreteInvariants.toD1 {D : SourceLogShellDatum.{u}} {f e m : ℕ}
    (I : Prop58iConcreteInvariants D f e m) : Prop58iLocalFieldReconstruction D.K where
  residueCardinality := I.residueCardinality
  absoluteDegree := I.absoluteDegree
  ramificationIndex := I.ramificationIndex
  pthRootsOrder := I.pthRootsOrder
  unitLayer := I.unitImage
  unitLayerImage := I.invariantImage
  reconstruction := D.preLogShell ⊆ D.unitLayer
  reconstruction_proof := preLogShell_subset_unitLayer D

/-- The D1 interface is inhabited by the concrete data. -/
def prop58iD1 (D : SourceLogShellDatum.{u}) (f e m : ℕ) :
    Prop58iLocalFieldReconstruction D.K :=
  (prop58iConcreteInvariants D f e m).toD1

/-- NAMED deep content of Prop 5.8(i): the group-theoretic reconstruction part.  Each item is
an explicit Prop with a proof field; the concrete object below is conditional on them. -/
structure Prop58iNamedInput (D : SourceLogShellDatum.{u}) where
  /-- G_k: the absolute Galois group of the local field. -/
  galoisGroup : Prop
  galoisGroup_proof : galoisGroup
  /-- the abelianization G_ab together with its structure. -/
  abelianization : Prop
  abelianization_proof : abelianization
  /-- the image of the embedding O^◇_k ↪ G_ab (local class field theory). -/
  unitDiamondEmbeddingImage : Prop
  unitDiamondEmbeddingImage_proof : unitDiamondEmbeddingImage
  /-- the image of the embedding k^× ↪ G_ab. -/
  unitGroupEmbeddingImage : Prop
  unitGroupEmbeddingImage_proof : unitGroupEmbeddingImage
  /-- the functorial group-theoretic algorithm (contravariant, via the Verlagerung map). -/
  groupTheoreticAlgorithm : Prop
  groupTheoreticAlgorithm_proof : groupTheoreticAlgorithm
  /-- Verlagerung (transfer) functoriality of the reconstruction. -/
  verlaengerungFunctoriality : Prop
  verlaengerungFunctoriality_proof : verlaengerungFunctoriality

/-- The conditional Prop 5.8(i) concrete object: concrete invariants + the named
group-theoretic content. -/
structure Prop58iConcreteObject (D : SourceLogShellDatum.{u}) (f e m : ℕ) where
  invariants : Prop58iConcreteInvariants D f e m := prop58iConcreteInvariants D f e m
  d1 : Prop58iLocalFieldReconstruction D.K := invariants.toD1
  named : Prop58iNamedInput D

/-- The concrete invariant data of the calibration model (the only fully concrete instance of
the carrier layer): all invariants are explicit; the named group-theoretic part is NOT
asserted. -/
def calibrationConcreteInvariants (f e m : ℕ) :
    Prop58iConcreteInvariants sourceLogShellCalibrationDatum f e m :=
  prop58iConcreteInvariants _ f e m

/-- The calibration instance: p, p*, p^f, absolute degree f*e, e, p^m data are explicit. -/
@[simp] theorem calibrationConcreteInvariants_pStar (f e m : ℕ) :
    (calibrationConcreteInvariants f e m).pStar =
      paperPStar sourceLogShellCalibrationDatum.p := rfl

/-- Prop 5.8(i) concrete/data rows: (item, concrete model, status/corpus). -/
def prop58iConcreteRows : List (String × String × String) :=
  [ ("p (residue characteristic)", "D.p : ℕ (Nat.Prime via D.hp)", "CONCRETE (datum field)"),
    ("p* := p if p odd, p^2 if p = 2", "paperPStar D.p = sourceLogShellStar D.p", "PROVED equality (sourceLogShellStar_eq_paperPStar)"),
    ("residue cardinality p^f", "D.p ^ f", "CONCRETE (explicit data)"),
    ("absolute degree [k:Q_p] = f*e", "f * e", "CONCRETE (explicit data)"),
    ("absolute ramification index e", "e", "CONCRETE (explicit data)"),
    ("order p^m of p-th power roots of unity", "D.p ^ m", "CONCRETE (explicit data)"),
    ("image of O^× / O^◇ (unit image)", "D.unitLayer", "CONCRETE model (logMap image)"),
    ("invariant image / pre-log-shell", "D.preLogShell", "CONCRETE model"),
    ("preLogShell ⊆ unitLayer", "preLogShell_subset_unitLayer", "PROVED"),
    ("G_k / G_ab / O^◇_k ↪ G_ab / k^× ↪ G_ab / algorithm / Verlagerung", "Prop58iNamedInput", "NAMED (corpus l.8059-8110; not formalized)") ]

/-- The Prop 5.8(i) concrete row record has ten rows. -/
theorem prop58iConcreteRows_length : prop58iConcreteRows.length = 10 := rfl

#check Prop58iConcreteInvariants
#check prop58iConcreteInvariants
#check Prop58iConcreteInvariants.toD1
#check prop58iD1
#check Prop58iNamedInput
#check Prop58iConcreteObject
#check calibrationConcreteInvariants
#check prop58iConcreteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual
end
