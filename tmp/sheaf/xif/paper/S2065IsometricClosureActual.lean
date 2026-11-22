import tmp.sheaf.xif.paper.S2056IsometricClosureActual
import tmp.sheaf.xif.paper.S2057NormBridgeFromIsometry
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# S2065: an unconditional isometric algebraic-closure equivalence over the
p-adic scalar field

Layer: O (completion integral units / S2046 norm bridge).

## What this file constructs

For every finite place `place` of `Q`, the p-adic scalar field

  `K_place = PadicScalarField place = Q_[p]`,   `p = completionRationalPrime place`,

has two algebraic closures in the tree:

* `SourceAlgebraicClosure place = AlgebraicClosure (NormalizedCompletion place)`,
  the closure of the actual completion, normed by the spectral norm over
  `K_place` (through the composite algebra structure
  `K_place -> NormalizedCompletion place -> SourceAlgebraicClosure place`);
* `AlgebraicClosure Q_[p]`, the Q_p-model closure, normed by the spectral
  norm over `Q_[p]`.

Both are algebraic closures of the *same* base field `K_place` (for the
source this uses `Algebra.IsAlgebraic.trans`, since
`NormalizedCompletion place` is finite-dimensional over `K_place`).  Hence
Mathlib's `IsAlgClosure.equiv` produces a `K_place`-algebra equivalence

  `S2065ClosureAlgEquiv place :
      SourceAlgebraicClosure place ≃ₐ[PadicScalarField place]
        AlgebraicClosure Q_[completionRationalPrime place]`.

## Norm preservation

The spectral norm is invariant under every `K_place`-algebra homomorphism
between algebraic extensions of `K_place`, because the minimal polynomial is
invariant for such a homomorphism and the spectral value only depends on the
minimal polynomial (`Example36.spectralNorm_algHom_eq`, already in the tree).
Consequently

  `S2065ClosureAlgEquiv_norm place x : ‖S2065ClosureAlgEquiv place x‖ = ‖x‖`.

This is an *actual* proof: no norm comparison is assumed and no uniqueness of
extensions of the p-adic absolute value is needed.  The two norms are the
spectral norms over the same base field, which is exactly what the
`change`-reduction in the proof exposes definitionally.

## Consumers

`S2065ClosureIsometry place : S2056ClosureIsometry place` therefore exists
unconditionally.  Feeding it to the earlier conditional reductions gives,
with no hypothesis left:

* `S2065IntegralUnitsEquiv place : S2055CompletionIntegralUnits place ≃*
   S2055QpIntegralUnits place` (and its identification witness);
* for every `v : FinitePrimePlace 2 7`,
  `S2065NormBridgeOf v : S2046NormBridge v`.

In particular `S2057NormBridgeOfIsometry` is no longer conditional, and
`S2056IntegralUnitsIdentification_of_isometry` is discharged for every place.

## Relation to the earlier base-ring-equivalence route

S2035/S2058 build a ring equivalence from `IsAlgClosure.equivOfEquiv` along a
*base-ring* equivalence `Q_[p] ≃+* NormalizedCompletion place`, and record
the norm-preservation of that particular ring equivalence as missing.  The
present construction bypasses that conditional: it uses the common
`K_place`-algebra structure directly.  It does not assert that the two ring
equivalences coincide (both are noncomputable choices of algebraic-closure
equivalence); it produces one ring equivalence together with its isometry
property, which is what `S2056ClosureIsometry` requires.

No `sorry`, `admit`, new axiom, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  Axiom probes are at the end of the file.
-/

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2057NormBridgeFromIsometry
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual

namespace LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual

variable (place : NumberField.FinitePlace ℚ)

/-! ## 1. The common algebraic-closure structure over the p-adic scalar field -/

/-- `SourceAlgebraicClosure place` is an algebraic closure of the p-adic
scalar field `PadicScalarField place`: `NormalizedCompletion place` is a
finite (hence algebraic) extension of that field, and the source closure is an
algebraic closure of `NormalizedCompletion place`. -/
local instance s2065SourceIsAlgClosure :
    IsAlgClosure (PadicScalarField place) (SourceAlgebraicClosure place) where
  isAlgClosed := (sourceAlgebraicClosureIsAlgClosure place).isAlgClosed
  isAlgebraic := sourceAlgebraicClosurePadicAlgebraic place

/-- The actual isometric algebraic-closure equivalence, as a
`PadicScalarField place`-algebra equivalence. -/
noncomputable def S2065ClosureAlgEquiv :
    SourceAlgebraicClosure place ≃ₐ[PadicScalarField place]
      AlgebraicClosure ℚ_[completionRationalPrime place] :=
  IsAlgClosure.equiv (PadicScalarField place)
    (SourceAlgebraicClosure place)
    (AlgebraicClosure ℚ_[completionRationalPrime place])

/-- **Norm preservation of the actual closure equivalence.**  The source and
target norms are the spectral norms over the same p-adic scalar field, and a
`K`-algebra homomorphism between algebraic extensions preserves the minimal
polynomial, hence the spectral norm. -/
theorem S2065ClosureAlgEquiv_norm (x : SourceAlgebraicClosure place) :
    ‖S2065ClosureAlgEquiv place x‖ = ‖x‖ := by
  change spectralNorm (PadicScalarField place)
      (AlgebraicClosure ℚ_[completionRationalPrime place])
      (S2065ClosureAlgEquiv place x) =
    spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) x
  exact LeanFormal.IUT.IUTII.Frobenioid.Example36.spectralNorm_algHom_eq
    (S2065ClosureAlgEquiv place).toAlgHom x

/-- The underlying actual ring equivalence of the closure isometry. -/
noncomputable def S2065ClosureRingEquiv :
    SourceAlgebraicClosure place ≃+*
      AlgebraicClosure ℚ_[completionRationalPrime place] :=
  (S2065ClosureAlgEquiv place).toRingEquiv

/-- **The unconditional S2056 closure isometry.** -/
noncomputable def S2065ClosureIsometry : S2056ClosureIsometry place where
  equiv := S2065ClosureRingEquiv place
  norm_pres := S2065ClosureAlgEquiv_norm place

/-! ## 2. The formerly conditional integral-units identification -/

/-- The actual integral units of the source algebraic closure identified with
the Q_p-model integral units, unconditionally. -/
noncomputable def S2065IntegralUnitsEquiv :
    S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place :=
  S2056IntegralUnitsEquiv place (S2065ClosureIsometry place)

/-- The exact S2055 missing identification now holds for every place. -/
theorem S2065IntegralUnitsIdentification :
    Nonempty (S2055IntegralUnitsIdentificationRequired place) :=
  ⟨S2065IntegralUnitsEquiv place⟩

/-! ## 3. The unconditional S2046 norm bridge -/

variable (v : FinitePrimePlace 2 7)

/-- The S2046 canonical norm/mu bridge at `v`, with no isometry hypothesis. -/
noncomputable def S2065NormBridgeOf : S2046NormBridge v :=
  S2057NormBridgeOfIsometry v (S2065ClosureIsometry (QPlace v))

/-- The availability form of the unconditional norm bridge. -/
theorem S2065NormBridgeOf_available : Nonempty (S2046NormBridge v) :=
  ⟨S2065NormBridgeOf v⟩

/-! ## 4. Axiom probes -/

#print axioms S2065ClosureAlgEquiv
#print axioms S2065ClosureAlgEquiv_norm
#print axioms S2065ClosureRingEquiv
#print axioms S2065ClosureIsometry
#print axioms S2065IntegralUnitsEquiv
#print axioms S2065IntegralUnitsIdentification
#print axioms S2065NormBridgeOf
#print axioms S2065NormBridgeOf_available

end LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual
end
