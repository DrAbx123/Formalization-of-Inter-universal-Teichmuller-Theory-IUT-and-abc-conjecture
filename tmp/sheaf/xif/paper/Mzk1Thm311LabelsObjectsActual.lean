import tmp.sheaf.lana_latest.Iut.HodgeTheater.Labels

/-! Mainline (A517-6): the Hodge-theater label objects of Theorem 3.11, referenced from the
real LANA-latest `HodgeTheater/Labels.lean` (IUT I combinatorial Teichmüller theory): the
`±`-label quotient `AbsFl` with `card_absFl = ℓ^±`, the geometric symmetry group `FlSemi`
with its transitivity, the `±`-torsors `PmTorsor` and `StarTorsor` with their isomorphism
torsors and cardinalities (`card_iso = 2ℓ`, `2`), and the `ℓ*`-size multiplicative labels
`FlStar`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311LabelsObjectsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u

variable (ℓ : ℕ)

/-! ## 1. Label sets and symmetry groups -/

/-- The `±`-quotient `|F_ℓ|` of the label set. -/
abbrev Thm311AbsFl := Iut.HodgeTheater.AbsFl ℓ

/-- The cardinality `ℓ^± = ℓ* + 1` of the `±`-label set (LANA real theorem). -/
theorem thm311_card_absFl [Iut.HodgeTheater.OddPrime ℓ] : Nat.card (Thm311AbsFl ℓ) = Iut.HodgeTheater.ellPm ℓ :=
  Iut.HodgeTheater.card_absFl ℓ

/-- The `ℓ*`-size multiplicative label set `F_ℓ^⋆`. -/
abbrev Thm311FlStar := Iut.HodgeTheater.FlStar ℓ

theorem thm311_card_flStar [Iut.HodgeTheater.OddPrime ℓ] :
    Nat.card (Thm311FlStar ℓ) = Iut.HodgeTheater.ellStar ℓ :=
  Iut.HodgeTheater.card_flStar ℓ

/-- The geometric symmetry group `F_ℓ^{⋊±}` (order `2ℓ`). -/
abbrev Thm311FlSemi := Iut.HodgeTheater.FlSemi ℓ

theorem thm311_card_flSemi : Nat.card (Thm311FlSemi ℓ) = 2 * ℓ :=
  Iut.HodgeTheater.card_flSemi ℓ

/-- The geometric symmetry group acts transitively on the labels (LANA real theorem). -/
theorem thm311_flSemi_isPretransitive [Iut.HodgeTheater.OddPrime ℓ] :
    MulAction.IsPretransitive (Thm311FlSemi ℓ) (ZMod ℓ) :=
  Iut.HodgeTheater.flSemi_isPretransitive ℓ

/-! ## 2. The `±`-torsors -/

/-- **O3 object**: the `±`-label torsor `LabCusp±(†D^⊚)` (the `D-Θ±ellNF` label layer's
  `lab` field). -/
abbrev Thm311PmTorsor := Iut.HodgeTheater.PmTorsor ℓ

/-- The `±`-torsor group (`PmGroup`). -/
abbrev thm311PmGroup := Iut.HodgeTheater.PmGroup ℓ

/-- Isomorphisms of `±`-torsors are a `ℤˣ × ZMod ℓ`-torsor (LANA real theorem). -/
def thm311PmIsoEquiv (A B : Thm311PmTorsor ℓ) :
    Iut.HodgeTheater.PmTorsor.Iso A B ≃ ℤˣ × ZMod ℓ :=
  Iut.HodgeTheater.PmTorsor.isoEquiv A B

/-- Any two `±`-torsors have exactly `2ℓ` isomorphisms (LANA real theorem). -/
theorem thm311PmIso_card (A B : Thm311PmTorsor ℓ) :
    Nat.card (Iut.HodgeTheater.PmTorsor.Iso A B) = 2 * ℓ :=
  Iut.HodgeTheater.PmTorsor.card_iso A B

/-- **O3 object**: the `ΘNF`-label torsor `LabCusp(†D^⊚)` (the `ν`/`lab` data of the
  `D-ΘNF`-bridge). -/
abbrev Thm311StarTorsor := Iut.HodgeTheater.StarTorsor ℓ

/-- Isomorphisms of `ΘNF`-torsors are a `F_ℓ^⋆`-torsor (LANA real theorem). -/
def thm311StarIsoEquiv (A B : Thm311StarTorsor ℓ) :
    Iut.HodgeTheater.StarTorsor.Iso A B ≃ Iut.HodgeTheater.FlStar ℓ :=
  Iut.HodgeTheater.StarTorsor.isoEquiv A B

/-- Any two `ΘNF`-torsors have exactly `ℓ*` isomorphisms (LANA real theorem). -/
theorem thm311StarIso_card (A B : Thm311StarTorsor ℓ) :
    Nat.card (Iut.HodgeTheater.StarTorsor.Iso A B) = Iut.HodgeTheater.ellStar ℓ :=
  Iut.HodgeTheater.StarTorsor.card_iso A B

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311LabelsObjectsActual