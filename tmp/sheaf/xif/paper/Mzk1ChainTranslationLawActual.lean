/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-!
# Frobenius-picture translations: group law (IUTI HodgeTheater node)

Declaration-level addendum to `SourceThetaLinkGraphAutomorphismReduction`: the
translations form a group under composition, with addition of the integer parameter;
the zero translation is the identity.  This is the group law used when composing the
theta-link graph automorphisms through the translation identification.

SHEAF node: iuti-ii:HodgeThetaLinkGraph.translationLaw (kind theorem, status
PENDING-VERIFY until the DAG watchdog reports EXIT0).  No new axioms.
-/

namespace LeanFormal.IUT

/-- Translations compose by adding their parameters. -/
theorem chainTranslation_add (k l : Int) :
    chainTranslation (k + l) = chainTranslation k * chainTranslation l := by
  ext n
  simp [chainTranslation_apply]
  omega

/-- Pointwise form of the translation composition law. -/
theorem chainTranslation_add_apply (k l n : Int) :
    chainTranslation (k + l) n = chainTranslation k (chainTranslation l n) := by
  simp [chainTranslation_apply]
  omega

/-- The zero translation is the identity. -/
theorem chainTranslation_zero_eq_one :
    chainTranslation (0 : Int) = (1 : Equiv.Perm Int) := chainTranslation_zero

/-- A translation composed with the identity is itself. -/
theorem chainTranslation_mul_one (k : Int) :
    chainTranslation k * chainTranslation (0 : Int) = chainTranslation k := by
  rw [← chainTranslation_add]
  simp

/-- The zero translation fixes every vertex. -/
theorem chainTranslation_zero_apply (n : Int) :
    chainTranslation (0 : Int) n = n := by
  simp [chainTranslation_apply]

/-- The zero translation is a left unit for composition. -/
theorem chainTranslation_zero_add (l : Int) :
    chainTranslation (0 + l) = chainTranslation l := by
  simp

/-- The zero translation is a right unit for composition. -/
theorem chainTranslation_add_zero (k : Int) :
    chainTranslation (k + 0) = chainTranslation k := by
  simp

end LeanFormal.IUT