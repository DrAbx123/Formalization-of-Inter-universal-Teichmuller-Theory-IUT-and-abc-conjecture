/-
  S2972: paper global q-pilot actual normalization (Tate uniformization /
  coricity part).

  This file constructs, from declarations already in the tree, the actual
  normalization data used by the paper's global q-pilot:

  * the local Tate q-pilot normalization at a prime label l: the canonical
    Tate parameter q = l in Q_l, its exact norm, the q-pilot log-volume
    qPilotLogVolume l = -log ||q l|| and the proved identity
    qPilotLogVolume l = Real.log (l.value : Real);
  * the global arithmetic normalization of a finite q-family on an actual
    finite-place selection, including the absolute-degree normalized
    magnitude/signed-log invariance under a finite extension of number
    fields (from ArithmeticQPilotGlobalNormalization);
  * the actual vertical coricity data (the source D-shadow gate and the
    projection coricity gate), with the proved preservation of the q and
    theta-scale data along vertical coricity;
  * the actual signed theta and signed q-pilot carriers of S2951 and S2983,
    together with their exact sources.

  The local Tate q-series model is the actual canonical q-series curve of
  TateJInvariantNorm.  Its curve-indexed Tate uniformization (coordinate
  change, quotient-point uniformization and Galois equivariance) is NOT
  asserted: the honest target is recorded by
  S2972CurveIndexedTateUniformizationTarget, and no inhabitant of that target
  is manufactured.  No sorry, axiom, True, PUnit, fake inequality or arbitrary
  data is used.  No existing file is modified.
-/

import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization
import LeanFormal.IUT.IUTIII.Theorem311.SourceVerticalDThetaProjection
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import tmp.sheaf.xif.paper.S2951ThetaSignedActual
import tmp.sheaf.xif.paper.S2983SignedQPilotActual
import tmp.sheaf.xif.paper.S2974VerticalCoricityGateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.TateCurvePadic
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
open LeanFormal.IUT.XiFPaper.S2983SignedQPilotActual
open LeanFormal.IUT.XiFPaper.S2974VerticalCoricityGateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2972QPilotGlobalNormalizationActual

universe ua uv upi umon ui uk uK

variable {l : PrimeGeFive}
local instance : Fact (Nat.Prime l.value) := ⟨l.prime⟩

/-! ## 1. The actual local Tate q-pilot normalization -/

/-- The actual norm of the canonical Tate q-parameter `q = l` in `Q_l`. -/
noncomputable def S2972TateQNorm (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Real := ‖q l‖

theorem S2972TateQNorm_eq :
    S2972TateQNorm l = (l.value : Real)⁻¹ :=
  q_norm_eq l

theorem S2972TateQNorm_pos : 0 < S2972TateQNorm l :=
  q_norm_pos l

theorem S2972TateQNorm_lt_one : S2972TateQNorm l < 1 :=
  q_norm_lt_one l

/-- The actual local q-pilot log-volume, defined by the canonical Tate
parameter.  This is the paper's `-log ||q||` at the prime label `l`. -/
noncomputable def S2972TateQPilotLogVolume
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  qPilotLogVolume l

theorem S2972TateQPilotLogVolume_eq_qPilotLogVolume :
    S2972TateQPilotLogVolume l = qPilotLogVolume l := rfl

theorem S2972TateQPilotLogVolume_eq_neg_log_qNorm :
    S2972TateQPilotLogVolume l = -Real.log (S2972TateQNorm l) := rfl

/-- **The requested actual relation**: the q-pilot log-volume is the
logarithm of the prime label (read as a real number). -/
theorem S2972_qPilotLogVolume_eq_log :
    S2972TateQPilotLogVolume l = Real.log (l.value : Real) :=
  qPilotLogVolume_eq_log_prime l

/-- The same relation stated directly for the Tate module's
`qPilotLogVolume`. -/
theorem S2972_qPilotLogVolume_eq_log_direct :
    qPilotLogVolume l = Real.log (l.value : Real) :=
  qPilotLogVolume_eq_log_prime l

theorem S2972_qPilotLogVolume_pos : 0 < S2972TateQPilotLogVolume l :=
  qPilotLogVolume_pos l

theorem S2972_qPilotLogVolume_eq_neg_log_inv :
    Real.log ((l.value : Real)⁻¹) = -S2972TateQPilotLogVolume l := by
  rw [S2972_qPilotLogVolume_eq_log, Real.log_inv]

/-- The actual log-norm of the canonical Tate j-invariant. -/
noncomputable def S2972TateJLogVolume
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  tateJInvariantLogVolume l

theorem S2972TateJLogVolume_eq :
    S2972TateJLogVolume l = Real.log ‖tateJInvariant l‖ := rfl

theorem S2972TateJLogVolume_eq_qPilotLogVolume :
    S2972TateJLogVolume l = S2972TateQPilotLogVolume l :=
  tateJInvariantLogVolume_eq_qPilotLogVolume l

theorem S2972TateJLogVolume_eq_log :
    S2972TateJLogVolume l = Real.log (l.value : Real) :=
  tateJInvariantLogVolume_eq_log_prime l

theorem S2972TateJ_norm_mul_qNorm :
    ‖tateJInvariant l‖ * ‖q l‖ = 1 :=
  tateJInvariant_norm_mul_q_norm l

theorem S2972TateJ_norm_eq_qNorm_inv :
    ‖tateJInvariant l‖ = (‖q l‖)⁻¹ :=
  tateJInvariant_norm l

theorem S2972TateJ_norm_eq_prime :
    ‖tateJInvariant l‖ = (l.value : Real) :=
  tateJInvariant_norm_eq_prime l

/-- Consumer-facing actual packet for the local Tate q-pilot normalization:
the exact q-norm, the q-pilot log-volume, its logarithm form, and the
j-invariant norm comparison.  Every field is filled by a proved theorem. -/
structure S2972TateLocalNormalization
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] where
  qNorm : Real
  qNorm_eq : qNorm = ‖q l‖
  qNorm_pos : 0 < qNorm
  qNorm_lt_one : qNorm < 1
  logVolume : Real
  logVolume_eq : logVolume = qPilotLogVolume l
  logVolume_eq_log : logVolume = Real.log (l.value : Real)
  logVolume_pos : 0 < logVolume
  jNorm : Real
  jNorm_eq : jNorm = ‖tateJInvariant l‖
  jNorm_eq_inv_qNorm : jNorm = qNorm⁻¹
  jNorm_mul_qNorm : jNorm * qNorm = 1
  jNorm_eq_prime : jNorm = (l.value : Real)

/-- The actual local Tate normalization packet. -/
noncomputable def S2972TateLocalNormalization.ofPrime
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    S2972TateLocalNormalization l where
  qNorm := ‖q l‖
  qNorm_eq := rfl
  qNorm_pos := q_norm_pos l
  qNorm_lt_one := q_norm_lt_one l
  logVolume := qPilotLogVolume l
  logVolume_eq := rfl
  logVolume_eq_log := qPilotLogVolume_eq_log_prime l
  logVolume_pos := qPilotLogVolume_pos l
  jNorm := ‖tateJInvariant l‖
  jNorm_eq := rfl
  jNorm_eq_inv_qNorm := tateJInvariant_norm l
  jNorm_mul_qNorm := tateJInvariant_norm_mul_q_norm l
  jNorm_eq_prime := tateJInvariant_norm_eq_prime l

theorem S2972TateLocalNormalization_qNorm
    (N : S2972TateLocalNormalization l) : N.qNorm = ‖q l‖ :=
  N.qNorm_eq

theorem S2972TateLocalNormalization_logVolume_eq_log
    (N : S2972TateLocalNormalization l) :
    N.logVolume = Real.log (l.value : Real) :=
  N.logVolume_eq_log

theorem S2972TateLocalNormalization_jNorm_eq_inv_qNorm
    (N : S2972TateLocalNormalization l) :
    N.jNorm = N.qNorm⁻¹ :=
  N.jNorm_eq_inv_qNorm

theorem S2972TateLocalNormalization_jNorm_mul_qNorm
    (N : S2972TateLocalNormalization l) :
    N.jNorm * N.qNorm = 1 :=
  N.jNorm_mul_qNorm

/-! ## 2. Global arithmetic normalization of the q-pilot -/

section GlobalArithmetic

variable {k : Type uk} [Field k] [NumberField k]
variable {K : Type uK} [Field K] [NumberField K] [Algebra k K]

/-- The global lower q-magnitude of an actual finite q-family. -/
noncomputable def S2972GlobalLowerMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  selectedLowerMagnitude selectedLowerPlaces parameters

/-- The global upper q-magnitude over the entire inverse image of the selected
lower places.  Each actual upper place occurs once. -/
noncomputable def S2972GlobalUpperMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  selectedUpperMagnitude (K := K) selectedLowerPlaces parameters

/-- The actual signed lower q-log. -/
noncomputable def S2972GlobalLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  selectedLowerSignedLog selectedLowerPlaces parameters

/-- The actual signed upper q-log on the full inverse image. -/
noncomputable def S2972GlobalUpperSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  selectedUpperSignedLog (K := K) selectedLowerPlaces parameters

theorem S2972GlobalUpperMagnitude_eq_fieldDegree_mul
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972GlobalUpperMagnitude (K := K) selectedLowerPlaces parameters =
      (Module.finrank k K : Real) *
        S2972GlobalLowerMagnitude selectedLowerPlaces parameters :=
  selectedUpperMagnitude_eq_fieldDegree_mul selectedLowerPlaces parameters

theorem S2972GlobalLowerSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972GlobalLowerSignedLog selectedLowerPlaces parameters =
      -S2972GlobalLowerMagnitude selectedLowerPlaces parameters :=
  selectedLowerSignedLog_eq_neg_magnitude selectedLowerPlaces parameters

theorem S2972GlobalUpperSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972GlobalUpperSignedLog (K := K) selectedLowerPlaces parameters =
      -S2972GlobalUpperMagnitude (K := K) selectedLowerPlaces parameters :=
  selectedUpperSignedLog_eq_neg_magnitude selectedLowerPlaces parameters

/-- The absolute-degree normalized lower q-magnitude. -/
noncomputable def S2972NormalizedLowerMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  absoluteDegreeNormalizedLowerMagnitude selectedLowerPlaces parameters

/-- The absolute-degree normalized upper q-magnitude. -/
noncomputable def S2972NormalizedUpperMagnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  absoluteDegreeNormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters

/-- The absolute-degree normalized lower signed q-log. -/
noncomputable def S2972NormalizedLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters

/-- The absolute-degree normalized upper signed q-log. -/
noncomputable def S2972NormalizedUpperSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : Real :=
  absoluteDegreeNormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters

/-- **Actual global normalization invariance**: the upper normalized magnitude
on the full inverse image equals the lower normalized magnitude. -/
theorem S2972NormalizedMagnitude_invariant
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972NormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters =
      S2972NormalizedLowerMagnitude selectedLowerPlaces parameters :=
  absoluteDegreeNormalizedMagnitude_invariant selectedLowerPlaces parameters

/-- The same invariance for the actual signed q-log. -/
theorem S2972NormalizedSignedLog_invariant
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972NormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters =
      S2972NormalizedLowerSignedLog selectedLowerPlaces parameters :=
  absoluteDegreeNormalizedSignedLog_invariant selectedLowerPlaces parameters

theorem S2972NormalizedLowerSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972NormalizedLowerSignedLog selectedLowerPlaces parameters =
      -S2972NormalizedLowerMagnitude selectedLowerPlaces parameters :=
  normalizedLowerSignedLog_eq_neg_magnitude selectedLowerPlaces parameters

theorem S2972NormalizedUpperSignedLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972NormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters =
      -S2972NormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters :=
  normalizedUpperSignedLog_eq_neg_magnitude selectedLowerPlaces parameters

theorem S2972NormalizedLowerMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < S2972NormalizedLowerMagnitude selectedLowerPlaces parameters :=
  absoluteDegreeNormalizedLowerMagnitude_pos
    selectedLowerPlaces parameters selected_nonempty

theorem S2972NormalizedUpperMagnitude_pos
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    0 < S2972NormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters :=
  absoluteDegreeNormalizedUpperMagnitude_pos
    selectedLowerPlaces parameters selected_nonempty

theorem S2972NormalizedLowerSignedLog_neg
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    S2972NormalizedLowerSignedLog selectedLowerPlaces parameters < 0 :=
  normalizedLowerSignedLog_neg
    selectedLowerPlaces parameters selected_nonempty

/-- The global arithmetic normalization of the q-pilot, packaged as an actual
structure.  All fields are the actual values and proofs of
ArithmeticQPilotGlobalNormalization. -/
structure S2972GlobalQPilotArithmeticNormalization
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) where
  lowerMagnitude : Real
  lowerMagnitude_eq :
    lowerMagnitude = S2972GlobalLowerMagnitude selectedLowerPlaces parameters
  upperMagnitude : Real
  upperMagnitude_eq :
    upperMagnitude =
      S2972GlobalUpperMagnitude (K := K) selectedLowerPlaces parameters
  lowerSignedLog : Real
  lowerSignedLog_eq :
    lowerSignedLog = S2972GlobalLowerSignedLog selectedLowerPlaces parameters
  upperSignedLog : Real
  upperSignedLog_eq :
    upperSignedLog =
      S2972GlobalUpperSignedLog (K := K) selectedLowerPlaces parameters
  normalizedLowerMagnitude : Real
  normalizedLowerMagnitude_eq :
    normalizedLowerMagnitude =
      S2972NormalizedLowerMagnitude selectedLowerPlaces parameters
  normalizedUpperMagnitude : Real
  normalizedUpperMagnitude_eq :
    normalizedUpperMagnitude =
      S2972NormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters
  normalizedLowerSignedLog : Real
  normalizedLowerSignedLog_eq :
    normalizedLowerSignedLog =
      S2972NormalizedLowerSignedLog selectedLowerPlaces parameters
  normalizedUpperSignedLog : Real
  normalizedUpperSignedLog_eq :
    normalizedUpperSignedLog =
      S2972NormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters
  upperMagnitude_eq_fieldDegree_mul :
    upperMagnitude = (Module.finrank k K : Real) * lowerMagnitude
  normalizedMagnitude_invariant :
    normalizedUpperMagnitude = normalizedLowerMagnitude
  normalizedSignedLog_invariant :
    normalizedUpperSignedLog = normalizedLowerSignedLog
  normalizedLowerSignedLog_eq_neg_magnitude :
    normalizedLowerSignedLog = -normalizedLowerMagnitude

noncomputable def S2972GlobalQPilotArithmeticNormalization.ofData
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972GlobalQPilotArithmeticNormalization (k := k) (K := K)
      selectedLowerPlaces parameters where
  lowerMagnitude := S2972GlobalLowerMagnitude selectedLowerPlaces parameters
  lowerMagnitude_eq := rfl
  upperMagnitude :=
    S2972GlobalUpperMagnitude (K := K) selectedLowerPlaces parameters
  upperMagnitude_eq := rfl
  lowerSignedLog := S2972GlobalLowerSignedLog selectedLowerPlaces parameters
  lowerSignedLog_eq := rfl
  upperSignedLog :=
    S2972GlobalUpperSignedLog (K := K) selectedLowerPlaces parameters
  upperSignedLog_eq := rfl
  normalizedLowerMagnitude :=
    S2972NormalizedLowerMagnitude selectedLowerPlaces parameters
  normalizedLowerMagnitude_eq := rfl
  normalizedUpperMagnitude :=
    S2972NormalizedUpperMagnitude (K := K) selectedLowerPlaces parameters
  normalizedUpperMagnitude_eq := rfl
  normalizedLowerSignedLog :=
    S2972NormalizedLowerSignedLog selectedLowerPlaces parameters
  normalizedLowerSignedLog_eq := rfl
  normalizedUpperSignedLog :=
    S2972NormalizedUpperSignedLog (K := K) selectedLowerPlaces parameters
  normalizedUpperSignedLog_eq := rfl
  upperMagnitude_eq_fieldDegree_mul :=
    S2972GlobalUpperMagnitude_eq_fieldDegree_mul
      selectedLowerPlaces parameters
  normalizedMagnitude_invariant :=
    S2972NormalizedMagnitude_invariant selectedLowerPlaces parameters
  normalizedSignedLog_invariant :=
    S2972NormalizedSignedLog_invariant selectedLowerPlaces parameters
  normalizedLowerSignedLog_eq_neg_magnitude :=
    S2972NormalizedLowerSignedLog_eq_neg_magnitude
      selectedLowerPlaces parameters

theorem S2972GlobalQPilotArithmeticNormalization_normalizedMagnitude_invariant
    (A : S2972GlobalQPilotArithmeticNormalization (k := k) (K := K)
      selectedLowerPlaces parameters) :
    A.normalizedUpperMagnitude = A.normalizedLowerMagnitude :=
  A.normalizedMagnitude_invariant

theorem S2972GlobalQPilotArithmeticNormalization_normalizedSignedLog_invariant
    (A : S2972GlobalQPilotArithmeticNormalization (k := k) (K := K)
      selectedLowerPlaces parameters) :
    A.normalizedUpperSignedLog = A.normalizedLowerSignedLog :=
  A.normalizedSignedLog_invariant

/-! ## 3. The Tate-normalized local contribution to the global sum -/

/-- If every local q-parameter of the selected lower family has the Tate
q-pilot log-magnitude, the global lower magnitude is the cardinality times the
Tate log-volume.  This is the actual local-to-global normalization step; the
Tate hypothesis is the paper's local normalization, not an extra axiom. -/
theorem S2972GlobalLowerMagnitude_eq_card_mul_tate
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    S2972GlobalLowerMagnitude selectedLowerPlaces parameters =
      (selectedLowerPlaces.card : Real) * qPilotLogVolume l := by
  unfold S2972GlobalLowerMagnitude selectedLowerMagnitude
  calc
    (∑ lowerPlace : selectedLowerPlaces,
        localLogMagnitude (parameters lowerPlace))
        = ∑ _lowerPlace : selectedLowerPlaces, qPilotLogVolume l :=
          Finset.sum_congr rfl (fun lowerPlace _ => hTate lowerPlace)
    _ = (selectedLowerPlaces.card : Real) * qPilotLogVolume l := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The signed global lower q-log under the Tate local normalization. -/
theorem S2972GlobalLowerSignedLog_eq_neg_card_mul_tate
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    S2972GlobalLowerSignedLog selectedLowerPlaces parameters =
      -((selectedLowerPlaces.card : Real) * qPilotLogVolume l) := by
  rw [S2972GlobalLowerSignedLog_eq_neg_magnitude,
    S2972GlobalLowerMagnitude_eq_card_mul_tate
      selectedLowerPlaces parameters hTate]

/-- The upper global magnitude under the Tate local normalization, using the
actual field-degree scaling. -/
theorem S2972GlobalUpperMagnitude_eq_card_mul_tate
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    S2972GlobalUpperMagnitude (K := K) selectedLowerPlaces parameters =
      (Module.finrank k K : Real) *
        ((selectedLowerPlaces.card : Real) * qPilotLogVolume l) := by
  rw [S2972GlobalUpperMagnitude_eq_fieldDegree_mul,
    S2972GlobalLowerMagnitude_eq_card_mul_tate
      selectedLowerPlaces parameters hTate]

/-- The absolute-degree normalized global magnitude under the same Tate local
normalization. -/
theorem S2972NormalizedLowerMagnitude_eq_card_div_degree_mul_tate
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    S2972NormalizedLowerMagnitude selectedLowerPlaces parameters =
      ((selectedLowerPlaces.card : Real) /
        (Module.finrank ℚ k : Real)) * qPilotLogVolume l := by
  have h := S2972GlobalLowerMagnitude_eq_card_mul_tate
    selectedLowerPlaces parameters hTate
  unfold S2972GlobalLowerMagnitude at h
  unfold S2972NormalizedLowerMagnitude absoluteDegreeNormalizedLowerMagnitude
  rw [h]
  ring

/-- The signed form: the globally normalized q-pilot log-volume is minus the
cardinality/degree factor times the local Tate q-pilot log-volume. -/
theorem S2972NormalizedLowerSignedLog_eq_neg_card_div_degree_mul_tate
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    S2972NormalizedLowerSignedLog selectedLowerPlaces parameters =
      -(((selectedLowerPlaces.card : Real) /
        (Module.finrank ℚ k : Real)) * qPilotLogVolume l) := by
  rw [S2972NormalizedLowerSignedLog_eq_neg_magnitude,
    S2972NormalizedLowerMagnitude_eq_card_div_degree_mul_tate
      selectedLowerPlaces parameters hTate]

end GlobalArithmetic

/-! ## 4. The actual canonical Tate q-series model -/

/-- The actual canonical q-series Tate model at the prime label `l`.  This is
the q-series equation itself, not a Tate uniformization of a separate curve. -/
structure S2972TateQSeriesModel
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] where
  curve : WeierstrassCurve ℚ_[l.value]
  curve_eq : curve = canonicalCurve l
  isElliptic : curve.IsElliptic
  delta_ne_zero : curve.Δ ≠ 0
  delta_norm : ‖curve.Δ‖ = ‖q l‖
  c4_norm : ‖curve.c₄‖ = 1
  j_norm : ‖tateJInvariant l‖ = (‖q l‖)⁻¹

noncomputable def S2972TateQSeriesModel.ofPrime
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    S2972TateQSeriesModel l where
  curve := canonicalCurve l
  curve_eq := rfl
  isElliptic := canonicalCurve_is_elliptic l
  delta_ne_zero := canonicalCurve_delta_ne_zero l
  delta_norm := canonicalCurve_delta_norm_eq_q l
  c4_norm := canonicalCurve_c4_norm_for_j l
  j_norm := tateJInvariant_norm l

theorem S2972TateQSeriesModel_curve_isElliptic
    (M : S2972TateQSeriesModel l) : M.curve.IsElliptic :=
  M.isElliptic

theorem S2972TateQSeriesModel_delta_norm
    (M : S2972TateQSeriesModel l) : ‖M.curve.Δ‖ = ‖q l‖ :=
  M.delta_norm

theorem S2972TateQSeriesModel_j_norm
    (M : S2972TateQSeriesModel l) :
    ‖tateJInvariant l‖ = (‖q l‖)⁻¹ :=
  M.j_norm

/-- The exact curve-indexed Tate-uniformization target: an actual coordinate
change, quotient-point uniformization and Galois equivariance.  This is the
missing classical theorem; no inhabitant is constructed here. -/
def S2972CurveIndexedTateUniformizationTarget
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F)
    (parameter : FinitePlaceQCandidate place) : Prop :=
  Nonempty (CurveIndexedTateUniformization X place parameter)

/-! ## 5. Actual vertical coricity normalization -/

section Coricity

variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual q-pilot vertical coricity gate, built from the source D-shadow
D-prime-strip family, its vertical links and the reflexive bridge. -/
noncomputable abbrev S2972VerticalCoricityGate : I.VerticalCoricityGate :=
  S2974VerticalCoricityGate I

/-- The actual induced DTheta realization gate. -/
noncomputable abbrev S2972DThetaRealizationGate : I.DThetaRealizationGate :=
  S2974DThetaRealizationGate I

/-- The actual projection coricity gate, with the genuine vertical D-Theta
links of the source projection ledger (not a reflexive placeholder). -/
noncomputable abbrev S2972ProjectionCoricityGate : I.DThetaCoricityGate :=
  I.projectionCoricityGate

theorem S2972_coricity_dTheater (i : I.family.index) :
    (S2972VerticalCoricityGate (I := I)).dTheater i =
      (I.dThetaShadow).dStrip i :=
  S2974_dTheater I i

theorem S2972_coricity_verticalLink (i j : I.family.index) :
    (S2972VerticalCoricityGate (I := I)).verticalLink i j =
      (I.dThetaShadow).dLink i j :=
  S2974_verticalLink I i j

theorem S2972_coricity_bridge (i : I.family.index) :
    (S2972VerticalCoricityGate (I := I)).bridge i =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) :=
  S2974_bridge I i

theorem S2972_coricity_realization_dTheater (i : I.family.index) :
    (S2972DThetaRealizationGate (I := I)).dTheater i =
      (I.dThetaShadow).dStrip i :=
  S2974_realization_dTheater I i

/-- Vertical coricity preserves the theta q data (actual q-preservation of
the source projection coricity gate). -/
theorem S2972_coricity_projection_q (n m : Int) :
    ((S2972ProjectionCoricityGate (I := I)).theater n m).thetaPacket.q =
      ((S2972ProjectionCoricityGate (I := I)).theater n (m + 1)).thetaPacket.q :=
  I.projectionCoricityGate_vertical_q n m

/-- Vertical coricity preserves every theta scale. -/
theorem S2972_coricity_projection_scale (n m : Int)
    (j : SignedLabel l.value) :
    ((S2972ProjectionCoricityGate (I := I)).theater n m).thetaPacket.scale j =
      ((S2972ProjectionCoricityGate (I := I)).theater n (m + 1)).thetaPacket.scale j :=
  I.projectionCoricityGate_vertical_scale n m j

/-- The actual coricity normalization packet for the q-pilot: both the
D-shadow vertical gate and the projection coricity gate, with the proved
q/scale preservation. -/
structure S2972CoricityNormalization
    {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  verticalGate : I.VerticalCoricityGate
  realizationGate : I.DThetaRealizationGate
  projectionGate : I.DThetaCoricityGate
  q_preserved : forall n m : Int,
    (projectionGate.theater n m).thetaPacket.q =
      (projectionGate.theater n (m + 1)).thetaPacket.q
  scale_preserved : forall (n m : Int) (j : SignedLabel l.value),
    (projectionGate.theater n m).thetaPacket.scale j =
      (projectionGate.theater n (m + 1)).thetaPacket.scale j

noncomputable def S2972CoricityNormalization.ofSource
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    S2972CoricityNormalization I where
  verticalGate := S2972VerticalCoricityGate (I := I)
  realizationGate := S2972DThetaRealizationGate (I := I)
  projectionGate := S2972ProjectionCoricityGate (I := I)
  q_preserved := fun n m => S2972_coricity_projection_q (I := I) n m
  scale_preserved := fun n m j =>
    S2972_coricity_projection_scale (I := I) n m j

theorem S2972CoricityNormalization_q_preserved
    (C : S2972CoricityNormalization I) (n m : Int) :
    (C.projectionGate.theater n m).thetaPacket.q =
      (C.projectionGate.theater n (m + 1)).thetaPacket.q :=
  C.q_preserved n m

theorem S2972CoricityNormalization_scale_preserved
    (C : S2972CoricityNormalization I) (n m : Int)
    (j : SignedLabel l.value) :
    (C.projectionGate.theater n m).thetaPacket.scale j =
      (C.projectionGate.theater n (m + 1)).thetaPacket.scale j :=
  C.scale_preserved n m j

end Coricity

/-! ## 6. The actual signed theta and signed q-pilot carriers -/

section SignedCarriers

variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual signed theta carrier of S2951, definitionally the source
signed hull log-volume. -/
noncomputable def S2972ThetaSigned : Real := S2951ThetaSigned v R n

theorem S2972ThetaSigned_eq_source :
    S2972ThetaSigned v R n = I.sourceSignedHullLogVolume v R n := rfl

theorem S2972ThetaSigned_nonpos : S2972ThetaSigned v R n ≤ 0 :=
  S2951_thetaSigned_nonpos v R n

/-- The actual signed q-pilot carrier of S2983, definitionally minus the
real log-volume of the possible Theta-pilot image union. -/
noncomputable def S2972QSigned : Real :=
  S2983QSigned (I := I) (v := v) (R := R) (n := n)

theorem S2972QSigned_eq_source :
    S2972QSigned (I := I) v R n =
      -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
  S2983_qSigned_eq (I := I) (v := v) (R := R) (n := n)

theorem S2972QSigned_nonpos : S2972QSigned (I := I) v R n ≤ 0 :=
  S2983_qSigned_nonpos (I := I) (v := v) (R := R) (n := n)

/-- The actual corpus signed comparison target at the signed q-pilot. -/
def S2972SignedComparison : Prop :=
  S2983SignedComparison (I := I) (v := v) (R := R) (n := n)

/-- The concrete q-parameter used by the theta side of S2951. -/
noncomputable def S2972ThetaQParameter
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] : Real :=
  S2951QParameter l

theorem S2972ThetaQParameter_eq : S2972ThetaQParameter l = ‖q l‖ := rfl

/-- The theta-side q-parameter has absolute log exactly the Tate q-pilot
log-volume. -/
theorem S2972_abs_log_thetaQParameter_eq_qPilotLogVolume :
    |Real.log (S2972ThetaQParameter l)| = S2972TateQPilotLogVolume l := by
  rw [S2972ThetaQParameter_eq]
  unfold S2972TateQPilotLogVolume qPilotLogVolume
  rw [q_norm_eq, Real.log_inv, abs_neg,
    abs_of_pos (Real.log_pos (by exact_mod_cast l.prime.one_lt))]
  ring

theorem S2972_abs_log_thetaQParameter_eq_log :
    |Real.log (S2972ThetaQParameter l)| = Real.log (l.value : Real) := by
  rw [S2972_abs_log_thetaQParameter_eq_qPilotLogVolume,
    S2972_qPilotLogVolume_eq_log]

end SignedCarriers

/-! ## 7. The paper global q-pilot normalization packet -/

section PaperPacket

variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable {k : Type uk} [Field k] [NumberField k]
variable {K : Type uK} [Field K] [NumberField K] [Algebra k K]
variable (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
variable (parameters : (lowerPlace : selectedLowerPlaces) →
  FinitePlaceQCandidate lowerPlace.val)

/-- The actual paper global q-pilot normalization packet: the local Tate
normalization, the global arithmetic normalization, the actual coricity
normalization, and the two actual signed carriers.  Every field is an actual
value or a proved theorem. -/
structure S2972PaperGlobalQPilotNormalization
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)]
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {k : Type uk} [Field k] [NumberField k]
    {K : Type uK} [Field K] [NumberField K] [Algebra k K]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) where
  tate : S2972TateLocalNormalization l
  tateModel : S2972TateQSeriesModel l
  arithmetic : S2972GlobalQPilotArithmeticNormalization (k := k) (K := K)
    selectedLowerPlaces parameters
  coricity : S2972CoricityNormalization I
  thetaSigned : Real
  thetaSigned_eq : thetaSigned = S2951ThetaSigned v R n
  thetaSigned_nonpos : thetaSigned ≤ 0
  qSigned : Real
  qSigned_eq : qSigned = S2983QSigned I v R n
  qSigned_nonpos : qSigned ≤ 0
  qParameter : Real
  qParameter_eq : qParameter = S2951QParameter l
  qParameter_logVolume : |Real.log qParameter| = tate.logVolume

noncomputable def S2972PaperGlobalQPilotNormalization.ofData
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)]
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {k : Type uk} [Field k] [NumberField k]
    {K : Type uK} [Field K] [NumberField K] [Algebra k K]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    S2972PaperGlobalQPilotNormalization (k := k) (K := K) l v R n
      selectedLowerPlaces parameters where
  tate := S2972TateLocalNormalization.ofPrime l
  tateModel := S2972TateQSeriesModel.ofPrime l
  arithmetic := S2972GlobalQPilotArithmeticNormalization.ofData
    (k := k) (K := K) selectedLowerPlaces parameters
  coricity := S2972CoricityNormalization.ofSource I
  thetaSigned := S2951ThetaSigned v R n
  thetaSigned_eq := rfl
  thetaSigned_nonpos := S2951_thetaSigned_nonpos v R n
  qSigned := S2983QSigned (I := I) (v := v) (R := R) (n := n)
  qSigned_eq := rfl
  qSigned_nonpos := S2983_qSigned_nonpos (I := I) (v := v) (R := R) (n := n)
  qParameter := S2951QParameter l
  qParameter_eq := rfl
  qParameter_logVolume :=
    S2972_abs_log_thetaQParameter_eq_qPilotLogVolume (l := l)

theorem S2972PaperGlobalQPilotNormalization_tateModel_isElliptic
    (N : S2972PaperGlobalQPilotNormalization (k := k) (K := K) l v R n
      selectedLowerPlaces parameters) :
    N.tateModel.curve.IsElliptic :=
  N.tateModel.isElliptic

/-- The complete actual global q-pilot normalization summary. -/
theorem S2972PaperGlobalQPilotNormalization_summary
    (N : S2972PaperGlobalQPilotNormalization (k := k) (K := K) l v R n
      selectedLowerPlaces parameters) :
    N.tate.logVolume = Real.log (l.value : Real) ∧
      N.arithmetic.normalizedUpperMagnitude =
        N.arithmetic.normalizedLowerMagnitude ∧
      N.arithmetic.normalizedUpperSignedLog =
        N.arithmetic.normalizedLowerSignedLog ∧
      N.thetaSigned ≤ 0 ∧ N.qSigned ≤ 0 ∧
      |Real.log N.qParameter| = N.tate.logVolume :=
  ⟨N.tate.logVolume_eq_log,
    N.arithmetic.normalizedMagnitude_invariant,
    N.arithmetic.normalizedSignedLog_invariant,
    N.thetaSigned_nonpos,
    N.qSigned_nonpos,
    N.qParameter_logVolume⟩

/-- Under the paper's local Tate normalization of every selected q-parameter,
the global normalized lower magnitude is the cardinality/absolute-degree
factor times the local Tate q-pilot log-volume. -/
theorem S2972PaperGlobalQPilotNormalization_normalizedLowerMagnitude_eq
    (N : S2972PaperGlobalQPilotNormalization (k := k) (K := K) l v R n
      selectedLowerPlaces parameters)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    N.arithmetic.normalizedLowerMagnitude =
      ((selectedLowerPlaces.card : Real) /
        (Module.finrank ℚ k : Real)) * N.tate.logVolume := by
  rw [N.arithmetic.normalizedLowerMagnitude_eq, N.tate.logVolume_eq]
  exact S2972NormalizedLowerMagnitude_eq_card_div_degree_mul_tate
    selectedLowerPlaces parameters hTate

/-- The signed version of the global Tate normalization formula. -/
theorem S2972PaperGlobalQPilotNormalization_normalizedLowerSignedLog_eq
    (N : S2972PaperGlobalQPilotNormalization (k := k) (K := K) l v R n
      selectedLowerPlaces parameters)
    (hTate : forall lowerPlace : selectedLowerPlaces,
      localLogMagnitude (parameters lowerPlace) = qPilotLogVolume l) :
    N.arithmetic.normalizedLowerSignedLog =
      -(((selectedLowerPlaces.card : Real) /
        (Module.finrank ℚ k : Real)) * N.tate.logVolume) := by
  rw [N.arithmetic.normalizedLowerSignedLog_eq, N.tate.logVolume_eq]
  exact S2972NormalizedLowerSignedLog_eq_neg_card_div_degree_mul_tate
    selectedLowerPlaces parameters hTate

end PaperPacket

/-! ## 8. Axiom and interface audit -/

#check S2972TateLocalNormalization
#check S2972TateLocalNormalization.ofPrime
#check S2972_qPilotLogVolume_eq_log
#check S2972TateQSeriesModel
#check S2972CurveIndexedTateUniformizationTarget
#check S2972GlobalQPilotArithmeticNormalization
#check S2972GlobalQPilotArithmeticNormalization.ofData
#check S2972NormalizedMagnitude_invariant
#check S2972CoricityNormalization
#check S2972CoricityNormalization.ofSource
#check S2972_coricity_projection_q
#check S2972_coricity_projection_scale
#check S2972ThetaSigned
#check S2972QSigned
#check S2972PaperGlobalQPilotNormalization
#check S2972PaperGlobalQPilotNormalization.ofData
#check S2972PaperGlobalQPilotNormalization_tateModel_isElliptic
#check S2972PaperGlobalQPilotNormalization_summary
#check S2972PaperGlobalQPilotNormalization_normalizedLowerMagnitude_eq
#check S2972PaperGlobalQPilotNormalization_normalizedLowerSignedLog_eq
#check S2972_qPilotLogVolume_eq_log_direct
#check S2972GlobalLowerSignedLog_eq_neg_card_mul_tate
#check S2972GlobalUpperMagnitude_eq_card_mul_tate
#print axioms S2972_qPilotLogVolume_eq_log
#print axioms S2972_qPilotLogVolume_eq_log_direct
#print axioms S2972NormalizedMagnitude_invariant
#print axioms S2972CoricityNormalization.ofSource
#print axioms S2972PaperGlobalQPilotNormalization.ofData
#print axioms S2972PaperGlobalQPilotNormalization_summary

end LeanFormal.IUT.XiFPaper.S2972QPilotGlobalNormalizationActual
end
