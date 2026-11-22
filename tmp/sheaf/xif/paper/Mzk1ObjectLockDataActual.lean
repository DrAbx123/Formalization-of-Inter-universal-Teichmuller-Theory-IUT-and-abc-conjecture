/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0FinalS3137DictionaryActual
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsToS3137BridgeActual
import tmp.sheaf.xif.paper.Mzk1RootBaseCompletionGapActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-!
# Object-lock data with independent degrees, relative masses, signed theta

Definitions:
  rootBaseQpDegree = [F_v : Q_p] = e*dBase;
  localCompletionDegree = [K_w : (F_mod)_v] = n;
  kPlaceQpDegree = [K_w : Q_p] = n*dBase;
  s1915LocalDegree = [L_b : Q_p] = m*e*dBase.
F-place and K-place are separately chosen over the same (F_mod)-place; no F_v subset
K_w and no m*dL=n*dF is assumed.

The mainline lock's legacy fields d_L=B*n and thetaNormReadL=-thetaNormReadProduct
are recorded as extra sign/degree obstructions.  The corrected source data uses:
* independent degree factors;
* dimension-normalized relative mass comparison (unitMass != 1, no raw Haar image
  equality between different-dimensional root/completion spaces);
* the signed theta equality without a negative sign.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1RootBaseCompletionGapActual

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Independent degree factors for the two separately chosen places. -/
structure TrueTowerDataSource where
  dBase : Bad (nativePlaceSelection T) -> Nat
  e : Bad (nativePlaceSelection T) -> Nat
  n : Bad (nativePlaceSelection T) -> Nat
  m : Bad (nativePlaceSelection T) -> Nat
  dBase_pos : forall b, 0 < dBase b
  e_pos : forall b, 0 < e b
  n_pos : forall b, 0 < n b
  m_pos : forall b, 0 < m b
  rootBase_eq : forall b, rootBaseQpDegree T b = e b * dBase b
  kPlace_eq : forall b, kPlaceQpDegree T b = n b * dBase b
  s1915_eq : forall b, s1915LocalDegree T b = m b * e b * dBase b
  localDegree_eq : forall b,
    localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = n b

def TrueTowerDataGap : Prop := Nonempty (TrueTowerDataSource (T := T))

/-- The legacy lock d_L = B*n becomes the extra relation m*e*dBase = B*n. -/
theorem mainline_lock_implies_extra_relation
    (L : PaperS3137ObjectLock I place T)
    (D : TrueTowerDataSource (T := T)) :
    forall b, D.m b * D.e b * D.dBase b = L.B b * D.n b := by
  intro b
  have h := L.weight_relation b
  simpa only [D.s1915_eq b, D.localDegree_eq b] using h

/-- Action of an F/Fmod Galois automorphism on a finite F-place, defined by
moving the underlying height-one prime with `HeightOneSpectrum.equivOfRingEquiv`. -/
noncomputable def galoisPlaceMk
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (v : NumberField.FinitePlace T.arithmetic.F) : NumberField.FinitePlace T.arithmetic.F :=
  NumberField.FinitePlace.mk
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) v.maximalIdeal)

theorem galoisPlaceMk_maximalIdeal
    (σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F)
    (v : NumberField.FinitePlace T.arithmetic.F) :
    (galoisPlaceMk (T := T) σ v).maximalIdeal =
      IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) v.maximalIdeal := by
  rw [galoisPlaceMk, NumberField.FinitePlace.maximalIdeal_mk]

/-- Concrete Galois alignment condition: some F/Fmod automorphism moves the chosen
native F-place onto the contraction of the chosen K-place to F. -/
def GaloisFPlaceAlignmentCondition (b : Bad (nativePlaceSelection T)) : Prop :=
  exists σ : T.arithmetic.F ≃ₐ[T.arithmetic.Fmod] T.arithmetic.F,
    galoisPlaceMk (T := T) σ (nativeBadToFPlace T b) =
      LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
        (nativeBadToKPlace T b)

/-- Exact first missing lemma of the Galois route: pointwise existence of the
F/Fmod automorphism with the required alignment. -/
def GaloisFPlaceAlignmentGap : Prop :=
  forall b : Bad (nativePlaceSelection T), GaloisFPlaceAlignmentCondition (T := T) b

/-- Once the alignment holds, the existing completionMap gives the actual embedding
F_v -> K_w (domain rewritten to the native F-place). -/
noncomputable def alignedCompletionMap
    (b : Bad (nativePlaceSelection T))
    (h : LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F)
        (nativeBadToKPlace T b) = nativeBadToFPlace T b) :
    (nativeBadToFPlace T b).maximalIdeal.adicCompletion T.arithmetic.F →+*
      (nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K :=
  h ▸ LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := T.arithmetic.F)
    (nativeBadToKPlace T b)

/-- Half of the Galois route: an actual K-place completion over the (moved)
F-place.  mK = [K_w : F_v].  The F-place may be moved by an F/Fmod Galois
automorphism first; this source records the resulting completion tower. -/
structure KCompletionOverFSource where
  mK : Bad (nativePlaceSelection T) -> Nat
  mK_pos : forall b, 0 < mK b
  rootBase_pos : forall b, 0 < rootBaseQpDegree T b
  kPlace_over_rootBase : forall b,
    kPlaceQpDegree T b = mK b * rootBaseQpDegree T b

/-- RelativeFactorTowerData from the correct completion tower kPlace = mK * rootBase
(mK = [K_w:F_v]).  This is the output of the Galois/prime-transitivity route. -/
theorem relativeFactorTowerData_of_completionTower
    (D : KCompletionOverFSource (T := T)) :
    RelativeFactorTowerData (T := T) := by
  intro b
  exact ⟨rootBaseQpDegree T b, D.mK b, kPlaceQpDegree T b,
    D.rootBase_pos b, rfl, rfl, D.kPlace_over_rootBase b⟩

/-- Exact first missing source of the Galois route: the completion tower
kPlace = mK * rootBase over the moved F-place. -/
def KCompletionOverFSourceGap : Prop :=
  Nonempty (KCompletionOverFSource (T := T))

/-- Dimension-normalized relative unit-mass data.  This is the corrected
replacement for raw actualUnitMassL = s1915UnitMass.toReal: compare relative log
masses divided by the dimensions, so Haar scalar factors cancel. -/
structure ObjectLockRelativeMassDataSource where
  dL : Nat
  dRoot : Nat
  dL_pos : 0 < dL
  dRoot_pos : 0 < dRoot
  referenceLogMassL : Real
  referenceLogMassRoot : Real
  relative_volume_eq :
    (Real.log (actualUnitMassL (I := I) (place := place)) - referenceLogMassL) /
        (dL : Real) =
      (Real.log (s1915UnitMass T).toReal - referenceLogMassRoot) /
        (dRoot : Real)

/-- Corrected signed-theta data: no negative sign between two signed readings.
The nonnegative case is a separate hypothesis, matching the proof split. -/
structure ObjectLockThetaSignedDataSource where
  theta_signed : thetaNormReadL (I := I) (place := place) =
    thetaNormReadProduct (T := T)
  theta_nonneg : 0 <= thetaNormReadProduct (T := T)

/-- Corrected object-lock source data. -/
structure ObjectLockActualDataSource where
  tower : TrueTowerDataSource (T := T)
  relativeMass : ObjectLockRelativeMassDataSource (I := I) (place := place) (T := T)
  thetaSigned : ObjectLockThetaSignedDataSource (I := I) (place := place) (T := T)

def ObjectLockActualDataGap : Prop :=
  Nonempty (ObjectLockActualDataSource I place T)

/-- If the natural signed equality and the legacy negative equality both hold,
both signed readings are zero.  Thus the legacy negative sign is an extra
condition, not a consequence of signed log-volumes. -/
theorem mainline_negative_theta_sign_forces_zero
    (hpos : thetaNormReadL (I := I) (place := place) =
      thetaNormReadProduct (T := T))
    (hneg : thetaNormReadL (I := I) (place := place) =
      -thetaNormReadProduct (T := T)) :
    thetaNormReadProduct (T := T) = 0 := by
  linarith

/-- The legacy raw unit-mass equality is not the corrected relative-mass data. -/
def LegacyUnitMassEquality : Prop :=
  actualUnitMassL (I := I) (place := place) = (s1915UnitMass T).toReal

def objectLockDataRows : List (String × String × String) :=
  [ ("TrueTowerDataSource", "rootBase=e*dBase, kPlace=n*dBase, s1915=m*e*dBase; no m*dL=n*dF", "DEFINED (source data)"),
    ("mainline_lock_implies_extra_relation", "legacy d_L=B*n => m*e*dBase = B*n", "PROVED"),
    ("relativeFactorTowerData_of_completionTower", "kPlace = mK*rootBase (mK=[K_w:F_v]) => RelativeFactorTowerData", "PROVED (conditional)"),
    ("KCompletionOverFSourceGap", "actual completion tower from Galois/prime transitivity", "EXPLICIT SOURCE GAP"),
    ("ObjectLockRelativeMassDataSource", "dimension-normalized relative log mass equality", "DEFINED (source data)"),
    ("ObjectLockThetaSignedDataSource", "signed equality + separate nonneg; no negative sign", "DEFINED (source data)"),
    ("mainline_negative_theta_sign_forces_zero", "natural signed + legacy negative => both zero", "PROVED"),
    ("LegacyUnitMassEquality", "raw actualUnitMassL = s1915UnitMass.toReal", "EXTRA LEGACY CONDITION"),
    ("actual dBase/e/n/m, relative mass, signed theta", "actual source objects", "EXPLICIT SOURCE GAP") ]

theorem objectLockDataRows_length : objectLockDataRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ObjectLockDataActual
end
