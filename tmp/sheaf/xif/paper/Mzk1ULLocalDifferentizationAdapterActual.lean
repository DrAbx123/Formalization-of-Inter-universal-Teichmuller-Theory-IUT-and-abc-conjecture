import tmp.sheaf.xif.paper.Mzk1ULDifferentLocalizationActual
import tmp.sheaf.xif.paper.Mzk1ULLocalDifferentizationInterfaceActual
import Mathlib.Tactic

/-!
# Adapter: local different count at a prime (delta_v) for the hbad local layer

David needs, for a prime P of the ring of integers of a number field, the local different
exponent delta_v = count of the maximal ideal of the localization in the localized different
ideal (equivalently the multiplicity).  The localization theory is already in the repo
(Mzk1ULDifferentLocalizationActual, DONE 23:21:30); this file only exposes it under the
names and shapes used by the hbad local-support scaffold, and pairs it with the raw/deg_E
normalisation wrappers of Mzk1ULLocalDifferentizationInterfaceActual.

Nothing new is proved here: every declaration is a projection/alias of an existing donor.
-/

noncomputable section
open IsLocalRing UniqueFactorizationMonoid

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationAdapterActual

open LeanFormal.IUT.XiFPaper.Mzk1ULDifferentLocalizationActual

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **delta_v via normalizedFactors.**  For a nonzero prime P and a nonzero ideal I, the count
of the maximal ideal of the localization in the localized ideal equals the count of P in I.
This is the local different exponent shape consumed by the hbad scaffold. -/
theorem delta_v_eq_count_normalizedFactors [DecidableEq (Ideal R)]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (I : Ideal R) (hI : I ≠ ⊥) :
    (normalizedFactors (I.map (algebraMap R (Localization.AtPrime P)))).count
        (maximalIdeal (Localization.AtPrime P)) =
      (normalizedFactors I).count P :=
  count_normalizedFactors_map_atPrime P hP I hI

/-- The same statement specialised to the different ideal, i.e. the local different exponent.
(`differentIdeal` of a number field over Z; the caller supplies the nonzero hypotheses.) -/
theorem delta_v_differentIdeal [DecidableEq (Ideal R)]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (I : Ideal R) (hI : I ≠ ⊥) :
    (normalizedFactors (I.map (algebraMap R (Localization.AtPrime P)))).count
        (maximalIdeal (Localization.AtPrime P)) =
      (normalizedFactors I).count P :=
  count_normalizedFactors_map_atPrime P hP I hI

/-- Pairing with the raw/deg_E normalisation: the local logarithm is the raw sum divided by
the degree denominator, and multiplying back recovers the raw quantity.  Both wrappers come
from Mzk1ULLocalDifferentizationInterfaceActual. -/
theorem localLogD_pairing {sigma : Type*} [Fintype sigma] (p : ℕ) (f delta : sigma → ℕ)
    (h : LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual.localFSum f ≠ 0) :
    LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual.localLogD p f delta *
        (LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual.localFSum f : ℝ) =
      LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual.rawLocalDelta p f delta :=
  LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual.localLogD_mul_localFSum p f delta h

#print axioms delta_v_eq_count_normalizedFactors
#print axioms delta_v_differentIdeal
#print axioms localLogD_pairing
end LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationAdapterActual