import tmp.sheaf.xif.paper.S1880OriginalXiFActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S1903SignedHullActual
import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual

/-!
# S1905: the actual paper signed-hull datum from S1902/S1903 and the exact
# remaining S1904 procession bridge

Layer: **O** (original-text Theta-link / IUT III Corollary 3.12, Step (xi-f)).

## What is assembled here

The paper signed-hull datum consumed by S1880 is

  `OrigXiFPaperSignedHullData X l`

with exactly three fields:

1. `thetaHull : ActualThetaHull X l`, constructed in S1902
   (`s1902ActualThetaHull`) on the actual root-extension product carrier
   `X = S1902Carrier T = RootExtensionProductCarrier T`: the actual finite
   Theta image union, its actual compact minimal product hull, the actual
   product Haar measure normalized so that `logVolume O = 1`, and the
   `lambda = 1` hull containment;
2. `determinant : SignedHullLogActual (SignedLabel l.value)`, constructed in
   S1903 (`s1903ActualDeterminant l`) from the inverse actual theta packet
   and the positive determinant tensor power `M = card ^ 3`; its
   `hullLogVolume` is `-thetaLogVolume l` and its procession average is
   `-thetaLogVolume l / (M * card)`;
3. `hull_logVolume_eq_procession`, the S1904 procession bridge.

This file defines the two actual components

  `S1905ThetaHull T := s1902ActualThetaHull T`,
  `S1905Determinant := s1903ActualDeterminant l`

and the exact remaining datum

  `S1905FirstMissing T := S1904ProcessionBridge (S1905ThetaHull T) (S1905Determinant)`.

## Exact result

* `s1905_firstMissing_iff_exists_datum`: a paper signed-hull datum with these
  two actual projections exists **if and only if** the bridge holds.  So the
  assembly is complete except for exactly the third field.
* `s1905_xiF_abs_of_firstMissing`: given the bridge, S1880 gives
  `-|log q| <= -|log Theta|` at the assembled datum.
* `s1905_unconditional_iff_firstMissing`: the unconditional form of the
  Corollary 3.12 inequality at the actual q is *equivalent* to the bridge.
  Hence the target cannot be obtained without proving exactly this datum.
* `s1905_bridge_not_derivable`: the bridge is not a consequence of the two
  actual structures (S1904): for every actual theta hull there is an actual
  determinant at which it fails.

The bridge is a genuine arithmetic Haar readout on the theta carrier (the
normalized Haar log-volume of the hull against the determinant procession
average), not an algebraic identity of `ActualThetaHull` and
`SignedHullLogActual`.  No `True`, `PUnit`, `sorry`, axiom, fake hull,
fake Haar, or arbitrary datum is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1905Unconditional312Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaperThetaHull
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open MeasureTheory

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

local instance s1905GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1905FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The two actual components -/

/-- The first field: the actual `1,circ U` Theta hull of S1902 on the
root-extension product carrier. -/
abbrev S1905ThetaHull : ActualThetaHull (S1902Carrier T) l :=
  s1902ActualThetaHull T

/-- The second field: the actual signed-hull determinant of S1903. -/
abbrev S1905Determinant : SignedHullLogActual (SignedLabel l.value) :=
  s1903ActualDeterminant l

/-- **The exact first missing datum**: the S1904 procession bridge between the
actual theta-hull Haar readout and the actual determinant procession average,
at the actual S1902/S1903 fields.  This is literally the third field of
`OrigXiFPaperSignedHullData`. -/
def S1905FirstMissing : Prop :=
  S1904ProcessionBridge (S1905ThetaHull T) (S1905Determinant (l := l))

/-- The first missing proposition is the third-field equation. -/
theorem S1905FirstMissing_iff :
    S1905FirstMissing T ↔
      (S1905ThetaHull T).haar.logVolume
          (S1905ThetaHull T).compactHull.hull =
        ENNReal.ofReal (S1905Determinant (l := l)).procession.average :=
  Iff.rfl

/-! ## 2. The assembly of the paper signed-hull datum -/

/-- Assemble the paper signed-hull datum from the two actual S1902/S1903
components and the S1904 bridge. -/
def S1905D (h : S1905FirstMissing T) :
    OrigXiFPaperSignedHullData (S1902Carrier T) l where
  thetaHull := S1905ThetaHull T
  determinant := S1905Determinant (l := l)
  hull_logVolume_eq_procession := h

@[simp] theorem S1905D_thetaHull (h : S1905FirstMissing T) :
    (S1905D T h).thetaHull = S1905ThetaHull T := rfl

@[simp] theorem S1905D_determinant (h : S1905FirstMissing T) :
    (S1905D T h).determinant = S1905Determinant (l := l) := rfl

/-- The assembled datum's third field is the first-missing bridge. -/
theorem S1905D_hull_logVolume_eq_procession (h : S1905FirstMissing T) :
    (S1905D T h).hull_logVolume_eq_procession = h := rfl

/-- **Exact characterization of the assembly.**  A paper signed-hull datum with
the actual S1902 theta hull and the actual S1903 determinant exists if and only
if the S1904 bridge holds.  Hence the third field is the only remaining
datum. -/
theorem s1905_firstMissing_iff_exists_datum :
    S1905FirstMissing T ↔
      ∃ D : OrigXiFPaperSignedHullData (S1902Carrier T) l,
        D.thetaHull = S1905ThetaHull T ∧
          D.determinant = S1905Determinant (l := l) := by
  constructor
  · intro h
    exact ⟨S1905D T h, rfl, rfl⟩
  · rintro ⟨D, hT, hP⟩
    cases D with
    | mk thetaHull determinant hbridge =>
      simp only at hT hP
      subst hT
      subst hP
      exact hbridge

/-- The first missing is not derivable from the two actual components: for
every actual theta hull there is an actual determinant at which the bridge is
false (S1904).  Hence it is genuine additional arithmetic Haar data. -/
theorem s1905_bridge_not_derivable
    (T' : ActualThetaHull (S1902Carrier T) l) :
    ∃ P : SignedHullLogActual (SignedLabel l.value),
      ¬ S1904ProcessionBridge T' P :=
  s1904_bridge_not_derivable T'

/-- Under the bridge the procession average is at most one (the necessary
paper normalization), now at the actual S1903 determinant. -/
theorem s1905_bridge_average_le_one (h : S1905FirstMissing T) :
    (S1905Determinant (l := l)).procession.average ≤ 1 :=
  s1904_bridge_average_le_one (S1905ThetaHull T) (S1905Determinant (l := l)) h

/-! ## 3. The Corollary 3.12 inequality at the actual q -/

/-- **The paper inequality at the assembled datum**: given the procession
bridge, S1880 gives `-|log q| <= -|log Theta|` for the assembled actual paper
signed hull. -/
theorem s1905_xiF_abs_of_firstMissing (h : S1905FirstMissing T) :
    -|Real.log ‖S1487Cand.q‖| ≤
      OrigXiFSignedThetaHullLogVolume (S1905D T h) :=
  s1880_xiF_inequality_abs (S1905D T h)

/-- The same comparison in the paper's `localLogMagnitude` form. -/
theorem s1905_xiF_le_of_firstMissing (h : S1905FirstMissing T) :
    -localLogMagnitude S1487Cand ≤
      OrigXiFSignedThetaHullLogVolume (S1905D T h) :=
  s1880_xiF_inequality (S1905D T h)

/-- The paper ray membership at the assembled datum. -/
theorem s1905_ray_of_firstMissing (h : S1905FirstMissing T) :
    -|Real.log ‖S1487Cand.q‖| ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull (S1905D T h)).signedHullLogVolume :=
  s1880_xiF_paperSignedHullRay (S1905D T h)

/-- **The unconditional form is exactly the first missing.**  The
Corollary 3.12 inequality at the actual q, stated without any datum
hypothesis, is equivalent to the S1904 bridge at the actual S1902/S1903
fields.  This is the precise reduction: the only open datum is
`S1905FirstMissing T`, and the target follows from it by S1880. -/
theorem s1905_unconditional_iff_firstMissing :
    (∃ h : S1905FirstMissing T,
      -|Real.log ‖S1487Cand.q‖| ≤
        OrigXiFSignedThetaHullLogVolume (S1905D T h)) ↔
      S1905FirstMissing T := by
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    exact ⟨h, s1905_xiF_abs_of_firstMissing T h⟩

/-- The signed-scalar face of the same first missing: the bridge is equivalent
to `-|log Theta| = -average` at the actual fields. -/
theorem s1905_firstMissing_iff_signed :
    S1905FirstMissing T ↔
      -((S1905ThetaHull T).haar.logVolume
            (S1905ThetaHull T).compactHull.hull).toReal =
        -(S1905Determinant (l := l)).procession.average := by
  rw [S1905FirstMissing, s1904_bridge_iff_signed]
  rfl

/-! ## 4. Axiom probes -/

#print axioms S1905D
#print axioms s1905_firstMissing_iff_exists_datum
#print axioms s1905_xiF_abs_of_firstMissing
#print axioms s1905_unconditional_iff_firstMissing
#print axioms s1905_firstMissing_iff_signed

end LeanFormal.IUT.XiFPaper.S1905Unconditional312Actual

end
