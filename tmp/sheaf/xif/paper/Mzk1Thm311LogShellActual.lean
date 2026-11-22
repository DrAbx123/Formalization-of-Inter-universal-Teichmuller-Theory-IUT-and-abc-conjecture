import tmp.sheaf.xif.paper.RefLANACor312ContainerActual

/-! Mainline (A517-1): Theorem 3.11 tensor-packet / log-shell objects, referenced from the
real LANA-latest `Iut/Cor312/Container.lean` (IUT III, Propositions 3.1-3.3, Remark 3.9.5):
the large volume container `LargeVolumeContainerData` (processions of capsules, tensor packets
as direct sums of local fields, mono-analytic log-shell regions, compactness/finite-support
and integral-containment fields), the restricted-product global container `Container`, the
admissible regions `AdmissibleRegion` with `toSet`, `IsProductFamily`, `IsBorelFamily`,
`integralAdmissible`, and the log-shell admissible region `logShellAdmissible`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311LogShellActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open scoped RestrictedProduct

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}
variable (D : Iut.LargeVolumeContainerData.{u₁, u₂, v} ι V)

/-! ## 1. The container and its tensor packets -/

/-- **O3 object**: the large volume container of Theorem 3.11 (the restricted product of the
  tensor packets; LANA real structure). -/
abbrev Thm311Container := Iut.LargeVolumeContainerData.{u₁, u₂, v} ι V

/-- The fiber of places over a rational place. -/
def thm311Fiber (vQ : Iut.RationalPlace) := Iut.LargeVolumeContainerData.Fiber D vQ

/-- The tensor-packet component index at capsule `i` over `v_Q`. -/
def thm311Components (i : Fin D.proc.length) (vQ : Iut.RationalPlace) :=
  Iut.LargeVolumeContainerData.Components D i vQ

/-- The global container at capsule `i` (restricted product of packet totals). -/
abbrev thm311GlobalContainer (i : Fin D.proc.length) :=
  Iut.LargeVolumeContainerData.Container D i

/-! ## 2. Admissible regions and the log-shell -/

/-- An admissible region of the container at capsule `i`. -/
abbrev thm311AdmissibleRegion (i : Fin D.proc.length) := D.AdmissibleRegion i

/-- The subset of the global container cut out by an admissible region. -/
def thm311AdmissibleRegion_toSet {i : Fin D.proc.length} (R : D.AdmissibleRegion i) :
    Set (D.Container i) :=
  R.toSet

/-- An admissible region is a direct-product family. -/
def thm311IsProductFamily {i : Fin D.proc.length} (R : D.AdmissibleRegion i) : Prop :=
  R.IsProductFamily

/-- An admissible region is a Borel family. -/
def thm311IsBorelFamily {i : Fin D.proc.length} (R : D.AdmissibleRegion i) : Prop :=
  R.IsBorelFamily

/-- **The mono-analytic log-shell of the container** (the region in which the pilot-object
  images are compared in IUT III, Proposition 3.9 and Corollary 3.12). -/
def thm311LogShellAdmissible (i : Fin D.proc.length) : D.AdmissibleRegion i :=
  D.logShellAdmissible i

/-- The log-shell admissible region's packet region is the container log-shell (LANA real
  lemma). -/
theorem thm311LogShellAdmissible_region (i : Fin D.proc.length) (vQ : Iut.RationalPlace) :
    (thm311LogShellAdmissible D i).region vQ = D.logShell i vQ :=
  D.logShellAdmissible_region i vQ

/-- The log-shell admissible region is a direct-product family (LANA real lemma). -/
theorem thm311LogShellAdmissible_isProduct (i : Fin D.proc.length) :
    (thm311LogShellAdmissible D i).IsProductFamily :=
  D.isProductFamily_logShellAdmissible i

/-- The holomorphic integral structure as an admissible region (LANA real def). -/
def thm311IntegralAdmissible (i : Fin D.proc.length) : D.AdmissibleRegion i :=
  D.integralAdmissible i

/-- Pointwise containment of admissible regions (the container log-shell contains the
  integral admissible region at nonarchimedean places; LANA real field). -/
def thm311AdmissibleLE (D : Iut.LargeVolumeContainerData ι V) {i : Fin D.proc.length}
    (R S : D.AdmissibleRegion i) : Prop :=
  R ≤ S

theorem thm311AdmissibleLE_iff (D : Iut.LargeVolumeContainerData ι V)
    {i : Fin D.proc.length} {R S : D.AdmissibleRegion i} :
    thm311AdmissibleLE D R S ↔ ∀ vQ, R.region vQ ⊆ S.region vQ :=
  Iff.rfl

/-- The nonarchimedean integral region is contained in the log-shell (LANA real field
  `integral_subset_logShell_nonarch`). -/
theorem thm311Integral_subset_logShell (i : Fin D.proc.length) (p : Nat.Primes) :
    (D.packet i (.finite p)).integralRegion ⊆ D.logShell i (.finite p) :=
  D.integral_subset_logShell_nonarch i p

/-- The log-shell is relatively compact (LANA real field). -/
theorem thm311LogShell_relCompact (i : Fin D.proc.length) (vQ : Iut.RationalPlace) :
    IsCompact (closure (D.logShell i vQ)) :=
  D.logShell_relCompact i vQ

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311LogShellActual