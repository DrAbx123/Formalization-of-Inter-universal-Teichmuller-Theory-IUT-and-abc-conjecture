import Mathlib.Topology.Algebra.MulAction
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S2138H1MLActual
/-- An abstract H^1 tower with finite levels and transition maps. -/
structure S2138H1Tower where
  H1 : ℕ → Type
  [commGroup : ∀ n, CommGroup (H1 n)]
  finite : ∀ n, Finite (H1 n)
  proj : ∀ n, H1 (n+1) →* H1 n
attribute [instance] S2138H1Tower.commGroup S2138H1Tower.finite
variable (T : S2138H1Tower)
/-- The iterated transition map from level n+r to level n. -/
def S2138IterProj : ∀ (n r : ℕ), T.H1 (n+r) →* T.H1 n
  | n, 0 => MonoidHom.id (T.H1 n)
  | n, r+1 => (S2138IterProj n r).comp (T.proj (n+r))
/-- Surjective transitions make every iterated transition surjective. -/
theorem S2138IterProj_surjective
    (h : ∀ n, Function.Surjective (T.proj n)) :
    ∀ n r, Function.Surjective (S2138IterProj T n r) := by
  intro n r
  induction r with
  | zero =>
      exact Function.surjective_id
  | succ r ih =>
      exact ih.comp (h (n+r))
/-- The range-stabilization (Mittag-Leffler) condition for the H^1 tower. -/
def S2138MittagLeffler : Prop :=
  ∀ n, ∃ r, ∀ s,
    Set.range (S2138IterProj T n (r+s)) =
      Set.range (S2138IterProj T n r)
/-- Surjective transitions imply range stabilization. -/
theorem S2138MittagLeffler_of_surjective
    (h : ∀ n, Function.Surjective (T.proj n)) :
    S2138MittagLeffler T := by
  intro n
  refine ⟨0, ?_⟩
  intro s
  have h0 : Function.Surjective (S2138IterProj T n 0) :=
    Function.surjective_id
  have hs : Function.Surjective (S2138IterProj T n (0+s)) :=
    S2138IterProj_surjective T h n (0+s)
  rw [Set.range_eq_univ.mpr h0, Set.range_eq_univ.mpr hs]
/-- Exact actual tower required for the arithmetic application: the level
H^1(G_v, mu_n) with finite levels and surjective transition maps.  No
inhabitant is asserted. -/
structure S2138ActualMuH1Tower extends S2138H1Tower where
  proj_surjective : ∀ n, Function.Surjective (proj n)
/-- The actual arithmetic tower supplies Mittag-Leffler once constructed. -/
theorem S2138ActualMuH1Tower_mittagLeffler
    (A : S2138ActualMuH1Tower) :
    S2138MittagLeffler A.toS2138H1Tower :=
  S2138MittagLeffler_of_surjective A.toS2138H1Tower A.proj_surjective
#check S2138H1Tower
#check S2138MittagLeffler
#check S2138MittagLeffler_of_surjective
#check S2138ActualMuH1Tower
#check S2138ActualMuH1Tower_mittagLeffler
end LeanFormal.IUT.XiFPaper.S2138H1MLActual
end
