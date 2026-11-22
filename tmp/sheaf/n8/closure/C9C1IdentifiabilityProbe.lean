import tmp.sheaf.n8.closure.C9IUTBridgeOutput

/-!
  Contract-level identifiability probe for C1.

  `C1SourceBridge` records only membership in the declared possible-output
  set.  It does not carry a q-pilot scalar or a log-volume equality.  The
  first theorem shows that the current singleton bridge is inhabited for every
  actual output.  The second theorem gives an abstract exact-attainment
  predicate and a same-signature countermodel: the bridge is inhabited while
  exact attainment fails whenever the output volume differs from `Q`.

  This is a contract diagnosis, not a source-level counterexample to IUT.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9IUTBridgeOutput

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open OriginalInput
open SourceHodgeTheaterBridge

universe u v w uv upi umon ui ux uy

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P)
  (X := X) (Y := Y) W}
variable {B : SourceP1P2Bundle W S}

/-- The current bridge membership is automatic for a singleton possible-output
set: the chosen output itself is a valid `qPilotOutput` witness. -/
theorem c1SourceBridge_singleton_of_output
    (out : ActualOutput R) :
    Nonempty (C1SourceBridge (R := R) (Set.singleton out)) :=
  ⟨{ qPilotOutput := out
     qPilotOutput_mem := Set.mem_singleton out }⟩

/-- Exact C1 attainment, with the missing numerical equality made explicit. -/
def ExactAttainment (possibleOutputs : Set (ActualOutput R))
    (logVol : ActualOutput R → Real) (Q : Real) : Prop :=
  ∃ d, d ∈ possibleOutputs ∧ logVol d = Q

/-- The current membership bridge does not imply exact attainment.  This is a
contract-level model: all existing bridge fields can hold while the hidden
q-pilot/log-volume equation is false. -/
theorem c1SourceBridge_not_exactAttainment
    (out : ActualOutput R) (logVol : ActualOutput R → Real) (Q : Real)
    (hne : logVol out ≠ Q) :
    Nonempty (C1SourceBridge (R := R) (Set.singleton out)) ∧
      ¬ ExactAttainment (R := R) (Set.singleton out) logVol Q := by
  refine ⟨c1SourceBridge_singleton_of_output out, ?_⟩
  intro h
  rcases h with ⟨d, hd, hvol⟩
  have hd' : d = out := Set.mem_singleton_iff.mp hd
  exact hne (by simpa [hd'] using hvol)

end LeanFormal.IUT.N8Closure.C9IUTBridgeOutput

end

#print axioms LeanFormal.IUT.N8Closure.C9IUTBridgeOutput.c1SourceBridge_singleton_of_output
#print axioms LeanFormal.IUT.N8Closure.C9IUTBridgeOutput.c1SourceBridge_not_exactAttainment
