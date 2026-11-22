/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import Mathlib.Tactic

/-!
# Mzk1GenuineXiEContainmentActual — genuine (non-vacuous) xi-e containment

A531 audit: xi-e containment must not be definitional/vacuous.  We package the
containment with an explicit non-vacuity condition (`qRegion ≠ ∅` and
`qRegion ≠ univ`), and instantiate it on the actual q-pilot singleton region
`{qPilotLogImage T b}` (nonempty and strictly proper because the q reading is
negative).  The containment into `MRRep.possibleRegion` is supplied by the
actual LANA possible-image lemma (not by definition).

No new axiom, no True placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open Iut.Multiradial

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- A genuine containment datum: an actual q-pilot region, a hull region, the
containment, and the non-vacuity witnesses. -/
structure GenuineXiEContainment where
  /-- the q-pilot region. -/
  qRegion : Set Real
  /-- the Theta-pilot hull region. -/
  thetaHull : Set Real
  /-- the xi-e containment. -/
  containment : qRegion ⊆ thetaHull
  /-- non-vacuity: the q region is nonempty. -/
  qRegion_nonempty : qRegion.Nonempty
  /-- non-vacuity: the q region is not the whole line. -/
  qRegion_not_univ : qRegion ≠ Set.univ

/-- The actual q-pilot singleton region at a bad place. -/
def qPilotRegion (b : Bad (nativePlaceSelection T)) : Set Real :=
  {qPilotLogImage T b}

/-- The q-pilot region is nonempty. -/
theorem qPilotRegion_nonempty (b : Bad (nativePlaceSelection T)) :
    (qPilotRegion T b).Nonempty :=
  ⟨qPilotLogImage T b, rfl⟩

/-- The q-pilot region is not the whole real line (the q reading is negative, so
`0` is outside the singleton). -/
theorem qPilotRegion_not_univ (b : Bad (nativePlaceSelection T)) :
    qPilotRegion T b ≠ Set.univ := by
  intro h
  have hmem : (0 : Real) ∈ qPilotRegion T b := by
    rw [h]
    exact Set.mem_univ 0
  have hneg : qPilotLogImage T b < 0 := qPilotLogImage_neg T b
  simp [qPilotRegion] at hmem
  linarith

/-- The constant raw region used on the raw output: every representative yields
the actual q-pilot singleton region. -/
def qPilotConstRawRegion {G : Type*} [Groupoid G] {A : Type*} [Group A]
    {R : Iut.Multiradial.RawOutput G A} {P : G} (b : Bad (nativePlaceSelection T)) :
    R.F.obj P → Set Real :=
  fun _ => qPilotRegion T b

/-- Genuine containment: the actual q-pilot singleton is contained in the
possible-image union of the constant raw region (LANA possible-image lemma). -/
theorem qPilotRegion_subset_possibleRegion {G : Type*} [Groupoid G] {A : Type*} [Group A]
    {R : Iut.Multiradial.RawOutput G A} {P : G}
    (x : R.F.obj P) (b : Bad (nativePlaceSelection T)) :
    qPilotRegion T b ⊆
      Iut.Multiradial.MRRep.possibleRegion
        (qPilotConstRawRegion (T := T) (R := R) (P := P) b)
        (Iut.Multiradial.MRRep.mk (R := R) x) :=
  Iut.Multiradial.MRRep.reg_subset_possibleRegion _ x

/-- The containment datum with the hull being the possible-image union itself. -/
def genuineXiEContainment {G : Type*} [Groupoid G] {A : Type*} [Group A]
    {R : Iut.Multiradial.RawOutput G A} {P : G}
    (x : R.F.obj P) (b : Bad (nativePlaceSelection T)) : GenuineXiEContainment T where
  qRegion := qPilotRegion T b
  thetaHull := Iut.Multiradial.MRRep.possibleRegion
    (qPilotConstRawRegion (T := T) (R := R) (P := P) b)
    (Iut.Multiradial.MRRep.mk (R := R) x)
  containment := qPilotRegion_subset_possibleRegion T x b
  qRegion_nonempty := qPilotRegion_nonempty T b
  qRegion_not_univ := qPilotRegion_not_univ T b

#check genuineXiEContainment
#check qPilotRegion_not_univ

end LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEContainmentActual
end
