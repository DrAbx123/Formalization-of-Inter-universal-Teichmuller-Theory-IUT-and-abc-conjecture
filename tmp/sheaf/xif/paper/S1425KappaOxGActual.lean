import tmp.sheaf.xif.paper.S1399KappaOxGActual

-- S1425: actual inhabitant of the S1399 first field of the paper O^x(G)
-- module/action, built from actual F-prime-strip data.
--
-- Data used (all actual, no refl/self, no finite model, no axiom):
--   * the actual F-prime-strip Mon unit groups of a second lattice point
--     (1,0) of the same Hodge-theater family (sourceUnits);
--   * the actual product of the local Galois groups Pi v of that strip
--     (the group G);
--   * the actual Hodge-theater link (1,0) -> (0,1), i.e. the actual
--     poly-isomorphism of F-prime-strips, as the identification of G with the
--     middle group and of the units with the middle strip units.
--
-- The two strips are distinct actual F-prime-strips (S1425RefStrip_ne_midStrip),
-- so the construction is not a self-identification of the middle strip: the
-- group and unit identifications are the actual link isomorphisms.
--
-- Not claimed (recorded exactly): the paper's group-theoretic algorithm
-- G |-> O^x(G) of IUT II, Example 1.8, (iii), and the identification of the
-- acting group with Aut(‡A) = G_w of Definition 4.9, (ii).  The S1399
-- first field is inhabited on actual strip data; those two remaining
-- identifications are not constructed.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1425KappaOxGActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual
open LeanFormal.IUT.XiFPaper.S1388KappaSourceUnitsActual
open LeanFormal.IUT.XiFPaper.S1399KappaOxGActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 0. Topological fallback used only to state the S1399 pair-datum link

The S1388/S1399 convention gives each factor of a strip product the indiscrete
topology and the product group the resulting product topology.  Nothing below
depends on this choice; it is needed only to form the type of
`S1399ActualPairDatum I` in `S1425PaperOxGModuleActual_units_target`. -/

local instance s1425TopS01 : ∀ v : V, TopologicalSpace ((S01 (I := I)).Pi v) :=
  fun _ => ⊥

local instance s1425TopMiddle : TopologicalSpace (MiddleGraph (I := I)) :=
  inferInstance

/-! ## 1. The actual reference F-prime-strip at the lattice point (1,0) -/

/-- The actual F-prime-strip at the lattice point (1,0): a second actual
member of the same Hodge-theater family, distinct from the middle strip
`S01 = I.fPrimeStripAt 0 1`. -/
abbrev S1425RefStrip : FPrimeStrip.{umon, uv, upi} V :=
  I.primeStripAt 1 0

/-- The middle actual F-prime-strip `S01 = I.fPrimeStripAt 0 1`, written
through the same lattice-point projection as the reference strip. -/
abbrev S1425MidStrip : FPrimeStrip.{umon, uv, upi} V :=
  I.primeStripAt 0 1

/-- The actual Hodge-theater link `(1,0) -> (0,1)` of the source input,
exposed at the F-prime-strip level.  This is the actual poly-isomorphism used
below; it is not `FPrimeStripEquiv.refl`. -/
noncomputable def S1425RefLink :
    FPrimeStripEquiv (S1425RefStrip I) (S1425MidStrip I) :=
  I.primeStripLinkAt 1 0 0 1

/-- The actual source group: the product of the local groups of the actual
reference strip `S1425RefStrip`. -/
abbrev S1425SourceGroup := GraphGroup (upper := S1425RefStrip I)

/-- The canonical evaluation of the actual product group at a place. -/
noncomputable def S1425RefEval (v : V) :
    S1425SourceGroup I →* (S1425RefStrip I).Pi v :=
  Pi.evalMonoidHom _ v

/-- The actual identification of the reference product group with the middle
group, induced componentwise by the actual link. -/
noncomputable def S1425GroupEquiv :
    S1425SourceGroup I ≃* MiddleGraph (I := I) :=
  MulEquiv.piCongrRight (fun v => (S1425RefLink I).isoPi v)

@[simp] theorem S1425GroupEquiv_apply (v : V) (γ : S1425SourceGroup I) :
    S1425GroupEquiv I γ v = (S1425RefLink I).isoPi v (γ v) := rfl

@[simp] theorem S1425GroupEquiv_symm_apply (v : V)
    (γ : MiddleGraph (I := I)) :
    (S1425GroupEquiv I).symm γ v = ((S1425RefLink I).isoPi v).symm (γ v) := rfl

/-- The `S01`-form of the middle strip: `S01 = I.fPrimeStripAt 0 1`. -/
theorem S1425MidStrip_eq_S01 : S1425MidStrip I = S01 (I := I) := rfl

/-- The two actual strips used are distinct actual F-prime-strips: the
reference strip is not the middle strip.  (With aligned arithmetic, distinct
lattice points give distinct prime strips.) -/
theorem S1425RefStrip_ne_midStrip : S1425RefStrip I ≠ S1425MidStrip I := by
  have h : I.indexOf 1 0 ≠ I.indexOf 0 1 := by
    intro h
    have h' := congrArg I.index_equiv h
    simp [I.indexOf_apply] at h'
  exact primeStrip_ne_of_index_ne_of_arithmetic_eq (F := I.family)
    (A := I.initial.arithmetic) (fun i => I.arithmetic_alignment i) h

/-! ## 2. The actual source units and their actual action -/

/-- The actual source units: the unit group of the reference strip's value
monoid at `v` (actual F-prime-strip units). -/
abbrev S1425SourceUnits (v : V) := ((S1425RefStrip I).Mon v)ˣ

/-- The actual identification of the reference strip units with the middle
strip units, induced by the actual link's `isoMon`. -/
noncomputable def S1425UnitsEquiv (v : V) :
    S1425SourceUnits I v ≃* ((S01 (I := I)).Mon v)ˣ :=
  Units.mapEquiv ((S1425RefLink I).isoMon v)

@[simp] theorem S1425UnitsEquiv_apply (v : V) (u : S1425SourceUnits I v) :
    S1425UnitsEquiv I v u =
      Units.mapEquiv ((S1425RefLink I).isoMon v) u := rfl

/-- The actual action of the reference product group on the reference strip
units: the strip's own units action composed with the evaluation at `v`. -/
noncomputable def S1425SourceAction (v : V) :
    S1425SourceGroup I →* MulAut (S1425SourceUnits I v) :=
  ((S1425RefStrip I).unitsAction v).comp (S1425RefEval I v)

@[simp] theorem S1425SourceAction_apply (v : V) (γ : S1425SourceGroup I)
    (u : S1425SourceUnits I v) :
    S1425SourceAction I v γ u =
      (S1425RefStrip I).unitsAction v (γ v) u := rfl

/-- Units-level equivariance of a strip equivalence: `isoMon` carries the
source strip's units action to the target strip's units action along
`isoPi`.  This is the unit-group form of
`FPrimeStripEquiv.compatAction`. -/
theorem S1425UnitsMapEquiv_unitsAction
    {F F' : FPrimeStrip.{umon, uv, upi} V} (φ : FPrimeStripEquiv F F')
    (v : V) (g : F.toDPrimeStrip.Pi v) (u : (F.Mon v)ˣ) :
    Units.mapEquiv (φ.isoMon v) (FPrimeStrip.unitsAction F v g u) =
      FPrimeStrip.unitsAction F' v (φ.isoPi v g)
        (Units.mapEquiv (φ.isoMon v) u) := by
  ext
  simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val]
  exact φ.compatAction v g (u : F.Mon v)

/-- The action compatibility law of the S1399 first field, for the actual
data above: the actual units equivalence intertwines the reference strip's
actual action with the middle strip's actual action along the actual group
identification. -/
theorem S1425SourceAction_compat (v : V) (γ : S1425SourceGroup I)
    (u : S1425SourceUnits I v) :
    S1425UnitsEquiv I v (S1425SourceAction I v γ u) =
      ((S01 (I := I)).unitsAction v)
        (middleEval (I := I) v (S1425GroupEquiv I γ))
        (S1425UnitsEquiv I v u) := by
  have h := S1425UnitsMapEquiv_unitsAction (F := S1425RefStrip I)
    (F' := S1425MidStrip I) (S1425RefLink I) v (γ v) u
  exact h

/-! ## 3. The actual inhabitant of the S1399 first field -/

/-- The S1399 paper `O^x(G)` module/action, inhabited by actual data: the
actual reference strip units with their actual action, the actual reference
product group, and the actual theater link as the identification with the
middle strip. -/
noncomputable def S1425PaperOxGModuleActual :
    S1399PaperOxGModule (I := I) (G := S1425SourceGroup I) where
  sourceUnits := fun v => S1425SourceUnits I v
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := S1425SourceAction I
  groupEquiv := S1425GroupEquiv I
  unitsEquiv := S1425UnitsEquiv I
  action_compat := S1425SourceAction_compat I

/-! ## 4. First-field projections: the structure's fields are the actual data -/

/-- Exact first field: the constructed module's source units are the actual
reference strip unit group. -/
theorem S1425PaperOxGModuleActual_sourceUnits (v : V) :
    (S1425PaperOxGModuleActual I).sourceUnits v =
      ((S1425RefStrip I).Mon v)ˣ := rfl

/-- Exact first field: the constructed module's source action is the actual
reference strip units action composed with evaluation. -/
theorem S1425PaperOxGModuleActual_sourceAction (v : V) :
    (S1425PaperOxGModuleActual I).sourceAction v =
      ((S1425RefStrip I).unitsAction v).comp (S1425RefEval I v) := rfl

/-- Exact first field: the constructed module's group identification is the
actual link's componentwise `isoPi`. -/
theorem S1425PaperOxGModuleActual_groupEquiv (v : V)
    (γ : S1425SourceGroup I) :
    (S1425PaperOxGModuleActual I).groupEquiv γ v =
      (S1425RefLink I).isoPi v (γ v) := rfl

/-- Exact first field: the constructed module's units identification is the
actual link's `isoMon` on unit groups, hence an identification with the actual
S1388/S1399 middle-strip unit carrier `(S01.Mon v)^x`. -/
theorem S1425PaperOxGModuleActual_unitsEquiv (v : V)
    (u : (S1425PaperOxGModuleActual I).sourceUnits v) :
    (S1425PaperOxGModuleActual I).unitsEquiv v u =
      Units.mapEquiv ((S1425RefLink I).isoMon v) u := rfl

/-- The target carrier of the constructed units equivalence is exactly the
actual source carrier of the S1399 pair datum. -/
theorem S1425PaperOxGModuleActual_units_target (v : V) :
    ((S01 (I := I)).Mon v)ˣ = (S1399ActualPairDatum I).sourceUnits v := rfl

/-- The constructed module's action compatibility law. -/
theorem S1425PaperOxGModuleActual_action_compat (v : V)
    (γ : S1425SourceGroup I)
    (u : (S1425PaperOxGModuleActual I).sourceUnits v) :
    (S1425PaperOxGModuleActual I).unitsEquiv v
        ((S1425PaperOxGModuleActual I).sourceAction v γ u) =
      ((S01 (I := I)).unitsAction v)
        (middleEval (I := I) v ((S1425PaperOxGModuleActual I).groupEquiv γ))
        ((S1425PaperOxGModuleActual I).unitsEquiv v u) :=
  (S1425PaperOxGModuleActual I).action_compat v γ u

/-! ## 5. The construction is not a self-identification -/

/-- The identification is the actual theater link, not a reflexive strip
equivalence. -/
theorem S1425RefLink_eq_actualLink :
    S1425RefLink I = (I.linkAt 1 0 0 1).primeStripEquiv := rfl

/-- The group identification is the actual link's componentwise `isoPi`, and
the unit identification is the actual link's `isoMon`; both act between the
unit groups and local groups of the two distinct actual strips
`S1425RefStrip` and `S01`. -/
theorem S1425PaperOxGModuleActual_not_self :
    S1425RefStrip I ≠ S1425MidStrip I ∧
      S1425RefLink I = (I.linkAt 1 0 0 1).primeStripEquiv :=
  ⟨S1425RefStrip_ne_midStrip I, S1425RefLink_eq_actualLink I⟩

/-! ## Axiom probes -/

#print axioms S1425GroupEquiv
#print axioms S1425UnitsEquiv
#print axioms S1425SourceAction
#print axioms S1425SourceAction_compat
#print axioms S1425PaperOxGModuleActual
#print axioms S1425RefStrip_ne_midStrip
#print axioms S1425PaperOxGModuleActual_action_compat

#check S1425PaperOxGModuleActual
#check S1425GroupEquiv
#check S1425UnitsEquiv
#check S1425SourceAction_compat

end LeanFormal.IUT.XiFPaper.S1425KappaOxGActual

end
