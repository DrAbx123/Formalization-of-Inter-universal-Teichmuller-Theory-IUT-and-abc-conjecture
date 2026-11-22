import tmp.sheaf.xif.paper.S2440H1H2IntegrationActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
open LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
open LeanFormal.IUT.XiFPaper.S2427H2CompatCleanActual
open LeanFormal.IUT.XiFPaper.S2440H1H2IntegrationActual
namespace LeanFormal.IUT.XiFPaper.S2441H2RepresentativeActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual inverse limit of level H^2 classes. -/
noncomputable abbrev S2441LimH2 :=
  S2427ActualLimH2 p
/-- A levelwise continuous 2-cocycle representative of a compatible family of
H^2 classes. -/
noncomputable def S2441LevelRep (y : S2441LimH2 p) (n : ℕ) :
    ContinuousTwoCocycle
      ((S2196MuActionTower p).actn n) :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (coboundarySubgroup
        (action := (S2196MuActionTower p).actn n))
      (y.1 n))
theorem S2441LevelRep_spec (y : S2441LimH2 p) (n : ℕ) :
    QuotientGroup.mk (S2441LevelRep p y n) = y.1 n :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective
      (coboundarySubgroup
        (action := (S2196MuActionTower p).actn n))
      (y.1 n))
/-- Exact missing: a compatible levelwise representative family.  Its
compatibility is equality of continuous 2-cocycles under the level
projection, not merely equality of H^2 classes. -/
structure S2441CompatibleLevelRep (y : S2441LimH2 p) where
  rep : ∀ n, ContinuousTwoCocycle
    ((S2196MuActionTower p).actn n)
  rep_spec : ∀ n, QuotientGroup.mk (rep n) = y.1 n
  compat : ∀ n,
    twoCocycleProj (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat n
      (rep (n+1)) = rep n
/-- Exact missing target: every compatible family of level H^2 classes has
a compatible levelwise continuous 2-cocycle representative. -/
def S2441CompatibleLevelRepRequired : Prop :=
  ∀ y : S2441LimH2 p, Nonempty (S2441CompatibleLevelRep p y)
/-- Exact missing target: the actual S2114 representative lift. -/
def S2441ActualRepresentativeLiftRequired : Prop :=
  Nonempty (S2427ActualCompatibleRepresentativeLift p)
/-- The levelwise representatives are actual; only their compatibility is
missing. -/
theorem S2441LevelRep_nonempty (y : S2441LimH2 p) :
    Nonempty (∀ n, ContinuousTwoCocycle
      ((S2196MuActionTower p).actn n)) := by
  classical
  exact ⟨S2441LevelRep p y⟩
/-- The limit 2-cocycle attached to a compatible levelwise representative family. -/
noncomputable def S2441CocycleOfCompatibleLevelRep {y : S2441LimH2 p}
    (C : S2441CompatibleLevelRep p y) :
    ContinuousTwoCocycle
      (action := limitAction (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn (S2196MuActionTower p).compat) :=
  (twoCocycleExchange (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat).symm
    ⟨fun n => (C.rep n : ContinuousTwoCochain
        (G := LocalAbsoluteGalois p)
        (A := S2145Coeff p n)),
      ⟨fun n => congrArg Subtype.val (C.compat n),
        fun n => (C.rep n).2⟩⟩

/-- The attached limit cocycle projects to the chosen level classes. -/
theorem S2441CocycleOfCompatibleLevelRep_spec
    {y : S2441LimH2 p} (C : S2441CompatibleLevelRep p y) :
    z2ToLimH2 (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat
      (S2441CocycleOfCompatibleLevelRep p C) = y := by
  apply Subtype.ext
  funext n
  rw [z2ToLimH2_apply]
  have hlevel :
      twoCocycleLevel (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn (S2196MuActionTower p).compat n
        (S2441CocycleOfCompatibleLevelRep p C) = C.rep n := by
    let f : twoCocycleLimFamily (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn :=
      ⟨fun n => (C.rep n : ContinuousTwoCochain
          (G := LocalAbsoluteGalois p)
          (A := S2145Coeff p n)),
        ⟨fun n => congrArg Subtype.val (C.compat n),
          fun n => (C.rep n).2⟩⟩
    have h := congrArg
      (fun g : twoCocycleLimFamily (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn => (g.1 n))
      (MulEquiv.apply_symm_apply
        (twoCocycleExchange (S2145Coeff p) (S2145PowMap p)
          (S2196MuActionTower p).actn (S2196MuActionTower p).compat) f)
    apply Subtype.ext
    change (twoCochainLevel (S2145Coeff p) (S2145PowMap p) n
      (↑((twoCocycleExchange (S2145Coeff p) (S2145PowMap p)
        (S2196MuActionTower p).actn
        (S2196MuActionTower p).compat).symm f))) = (f.1 n)
    exact h
  rw [hlevel, C.rep_spec]

/-- A compatible levelwise family gives the actual S2114 lift. -/
noncomputable def S2441LiftOfCompatibleLevelRep
    (H : S2441CompatibleLevelRepRequired p) :
    S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
      (S2196MuActionTower p).actn (S2196MuActionTower p).compat where
  lift y := S2441CocycleOfCompatibleLevelRep p
    (Classical.choice (H y))
  lift_spec y := S2441CocycleOfCompatibleLevelRep_spec p
    (Classical.choice (H y))

/-- The compatible levelwise family is exactly what remains for the actual
representative lift. -/
theorem S2441ActualRepresentativeLiftRequired_of_compatible
    (H : S2441CompatibleLevelRepRequired p) :
    S2441ActualRepresentativeLiftRequired p :=
  ⟨S2441LiftOfCompatibleLevelRep p H⟩

#check S2441LevelRep
#check S2441LevelRep_spec
#check S2441CompatibleLevelRep
#check S2441CompatibleLevelRepRequired
#check S2441ActualRepresentativeLiftRequired
#check S2441LevelRep_nonempty
#check S2441CocycleOfCompatibleLevelRep
#check S2441CocycleOfCompatibleLevelRep_spec
#check S2441LiftOfCompatibleLevelRep
#check S2441ActualRepresentativeLiftRequired_of_compatible
end LeanFormal.IUT.XiFPaper.S2441H2RepresentativeActual
end
