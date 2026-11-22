import tmp.sheaf.n8.closure.C9A1A2A3Source
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionFromContract

/-!
# Conditional proxy-inequality diagnostic over reduced `Input`

This is a conditional diagnostic over the complete production `Input` record.  The
input is supplied by the existing conditional constructor
`sourceInputOfDefinition31Data`; no field of `Input` is replaced by a
singleton interface.  The historical name `StrongC1` below denotes only a proxy:
the initial cusp parameter (the source-side `q` proxy) is at most the base
packet log-volume (the signed `h` proxy).  The canonical packet has base
log-volume zero, while every supplied `SourceDefinition31Data` has a positive
cusp parameter, so this law fails although the already-proved A1/A2/A3
certificate is available.

The existing constructor explicitly uses a degenerate identity theater,
q/scale 1/2, zero level and a constant-volume packet.  Its source datum S is
supplied as a parameter; this file constructs no inhabitant of that datum.
Consequently the result is a conditional negation of the proxy inequality,
not an existential countermodel or a logical independence result.  No logical
relation to the original C1 predicate is established.  This file supplies no
new C1 evidence and is not counted as progress on C1.
-/

namespace LeanFormal.IUT.N8Closure.FullInputStrongC1Countermodel

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9A1A2A3Source
open LeanFormal.IUT.SourceProcessionAttack

noncomputable section

/-! The cusp parameter and base packet log-volume are only diagnostic
   proxies.  They are not identified with the paper's q-pilot or signed hull. -/
def StrongC1 (I : Theorem311Source.Input ℤ Nat) : Prop :=
  I.initial.cuspParameter ≤ I.profile.logVolume I.core.base

def canonicalInput {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    Theorem311Source.Input.{0, 0, 0} ℤ Nat :=
  sourceInputOfDefinition31Data (Label := ℤ) (Choice := Nat) S 0

theorem canonicalInput_profile_base_zero {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    (canonicalInput S).profile.logVolume (canonicalInput S).core.base = 0 := by
  rfl

theorem canonicalInput_q_positive {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    0 < (canonicalInput S).initial.cuspParameter := by
  exact (canonicalInput S).initial.cusp_positive

theorem canonicalInput_A1_A2_A3 {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    (A1 (canonicalInput S)).part_i = partI (canonicalInput S) ∧
      Nonempty (A2 (canonicalInput S)) ∧ Nonempty (A3 (canonicalInput S)) := by
  exact A1_A2_A3 (canonicalInput S)

theorem canonicalInput_not_StrongC1 {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    ¬ StrongC1 (canonicalInput S) := by
  intro h
  change (canonicalInput S).initial.cuspParameter ≤
    (canonicalInput S).profile.logVolume (canonicalInput S).core.base at h
  have hq : 0 < (canonicalInput S).initial.cuspParameter :=
    canonicalInput_q_positive S
  have hh : (canonicalInput S).profile.logVolume (canonicalInput S).core.base = 0 :=
    canonicalInput_profile_base_zero S
  rw [hh] at h
  exact (not_le_of_gt hq) h

theorem canonicalInput_A1_A2_A3_but_not_StrongC1 {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    ((A1 (canonicalInput S)).part_i = partI (canonicalInput S) ∧
      Nonempty (A2 (canonicalInput S)) ∧ Nonempty (A3 (canonicalInput S))) ∧
      ¬ StrongC1 (canonicalInput S) := by
  exact ⟨canonicalInput_A1_A2_A3 S, canonicalInput_not_StrongC1 S⟩

#print axioms canonicalInput_A1_A2_A3_but_not_StrongC1

end

end LeanFormal.IUT.N8Closure.FullInputStrongC1Countermodel
