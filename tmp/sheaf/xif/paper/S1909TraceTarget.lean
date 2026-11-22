/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1909

# S1909: the finite etale integral-closure target and its trace-integrality residual

This helper file records, for the coordinate ring R' = S1726CoordinateRing, the exact
statement of the finite etale integral closure in the generic fibre, together with the
trace-integrality input isolated by the trace-duality route.

The definitions are kept in a separate module because the typeclass search for the tensor
algebra structures is much better behaved here than in the full Weierstrass-import context.
-/

import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
open scoped TensorProduct

namespace LeanFormal.IUT.XiFPaper.S1909TraceTarget

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual

/-- The fraction field of R'. -/
abbrev S1909K : Type := FractionRing S1779R

/-- The exact missing trace-integrality input, for one finite etale R'-algebra A:
the trace over the generic fibre of every integral element is integral over R'. -/
def S1909TraceIntegralFor (A : Type) [CommRing A] [Algebra S1779R A]
    [Module.Finite S1779R A] [Algebra.Etale S1779R A] : Prop :=
  letI : Algebra S1779R (S1909K ⊗[S1779R] A) := Algebra.TensorProduct.instAlgebra
  letI : Algebra S1909K (S1909K ⊗[S1779R] A) := Algebra.TensorProduct.leftAlgebra
  ∀ y : S1909K ⊗[S1779R] A,
    IsIntegral S1779R y →
      IsIntegral S1779R (Algebra.trace S1909K (S1909K ⊗[S1779R] A) y)

/-- The exact missing trace-integrality input for all finite etale R'-algebras. -/
def S1909TraceIntegral : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra S1779R A]
    [Module.Finite S1779R A] [Algebra.Etale S1779R A],
    S1909TraceIntegralFor A

/-- The finite etale integral closure target: every finite etale R'-algebra A is the
integral closure of R' in its generic fibre FractionRing R' (x)_{R'} A. -/
def S1909FiniteEtaleIntegralClosure : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra S1779R A]
    [Module.Finite S1779R A] [Algebra.Etale S1779R A],
    letI : Algebra S1779R (S1909K ⊗[S1779R] A) := Algebra.TensorProduct.instAlgebra
    letI : Algebra A (S1909K ⊗[S1779R] A) := Algebra.TensorProduct.rightAlgebra
    IsIntegralClosure A S1779R (S1909K ⊗[S1779R] A)

/-- The two inputs isolated by the trace-duality route to the finite etale integral
closure: normality of R' and trace integrality.  This is a proposition, not a proof of
either input and not a proof that the conjunction suffices. -/
def S1909FiniteEtaleIntegralClosureResidual : Prop :=
  IsIntegrallyClosed S1779R ∧ S1909TraceIntegral

end LeanFormal.IUT.XiFPaper.S1909TraceTarget
