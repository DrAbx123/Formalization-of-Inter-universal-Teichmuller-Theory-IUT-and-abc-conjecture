/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1909

# S1909: normality of the Weierstrass coordinate ring R', and finite etale integral closure

The ring R' = S1726CoordinateRing is the coordinate ring of the affine elliptic curve
y^2 = x^3 + (61/64) x^2 - (125/64) x over the number field F'.

This file addresses two independent questions.

1. Normality of R'.  We prove that R' is integrally closed if and only if the
   localization of the affine Weierstrass coordinate ring at every nonzero maximal ideal
   is a discrete valuation ring.  The latter is the exact missing local smoothness input
   already isolated in the existing development
   ABCBridge.WeierstrassCoordinateRingIntegrallyClosed.SourceWeierstrassLocalizationDVR.
   No normality instance and no local DVR instance is postulated: the missing statement is
   a plain Prop with no inhabitant.

2. Finite etale integral closure.  For a finite etale R'-algebra A, the map
   A -> FractionRing R' (x)_{R'} A exhibits A as the integral closure of R' in the
   generic fibre, provided the trace of every integral element of the generic fibre is
   integral over R'.  That trace-integrality statement is isolated below as
   S1909TraceIntegral; it is the precise Mathlib gap in the general trace argument.
   The exact target is recorded as S1909FiniteEtaleIntegralClosure, and the residual
   (normality of R' plus trace integrality) is S1909FiniteEtaleIntegralClosureResidual.
   This file proves the normality characterization; it does not claim the trace-integrality
   input or the integral-closure target.

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.
-/

import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual
import tmp.sheaf.xif.paper.S1909TraceTarget
import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassCoordinateRingIntegrallyClosed
import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassCoordinateRingDedekind
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
open scoped TensorProduct

namespace LeanFormal.IUT.XiFPaper.S1909NormalRPrimeActual

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open ABCBridge.WeierstrassCoordinateRingIntegrallyClosed
open ABCBridge.WeierstrassCoordinateRingDedekind
open WeierstrassCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

/-- The affine Weierstrass curve attached to R'. -/
abbrev S1909W : WeierstrassCurve.Affine S1779K := S1849W

/-- The fraction field of R', the generic point of Spec R'. -/
abbrev S1909K : Type := FractionRing S1779R

/-- The explicit polynomial-ring equivalence carries the defining ideal of R' to the
Weierstrass polynomial of S1909W. -/
theorem S1909_ideal_map :
    Ideal.map (S1849mvEquiv : MvPolynomial (Fin 2) S1779K →+* Polynomial (Polynomial S1779K))
      (Ideal.span {S1726AffinePolynomial}) = Ideal.span {S1909W.polynomial} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {S1849mvEquiv S1726AffinePolynomial} = Ideal.span {S1909W.polynomial}
  rw [S1849mvEquiv_poly]

/-- The coordinate ring R' is the affine Weierstrass coordinate ring W.CoordinateRing. -/
noncomputable def S1909RCoord : S1779R ≃ₐ[S1779K] S1909W.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ S1849mvEquiv S1909_ideal_map.symm

/-- Normality transports along the coordinate-ring identification. -/
theorem S1909_isIntegrallyClosed_iff_coord :
    IsIntegrallyClosed S1779R ↔ IsIntegrallyClosed S1909W.CoordinateRing := by
  constructor
  · intro h
    letI : IsIntegrallyClosed S1779R := h
    exact IsIntegrallyClosed.of_equiv S1909RCoord.toRingEquiv
  · intro h
    letI : IsIntegrallyClosed S1909W.CoordinateRing := h
    exact IsIntegrallyClosed.of_equiv S1909RCoord.symm.toRingEquiv

/-- The exact first missing input for normality of R': every nonzero maximal localization
of the affine Weierstrass coordinate ring is a discrete valuation ring. -/
def S1909NormalRPrimeMissing : Prop :=
  SourceWeierstrassLocalizationDVR S1909W

/-- Normality of R' gives the local DVR statement. -/
theorem S1909_missing_of_isIntegrallyClosed
    (h : IsIntegrallyClosed S1779R) : S1909NormalRPrimeMissing := by
  have hcoord : IsIntegrallyClosed S1909W.CoordinateRing :=
    (S1909_isIntegrallyClosed_iff_coord).mp h
  haveI hDed : IsDedekindDomain S1909W.CoordinateRing :=
    sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed S1909W hcoord
  intro p hp hmax
  haveI : p.IsPrime := hmax.isPrime
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A := S1909W.CoordinateRing) (P := p) hp (Localization.AtPrime p)

/-- The local DVR statement gives normality of R'. -/
theorem S1909_isIntegrallyClosed_of_missing
    (h : S1909NormalRPrimeMissing) : IsIntegrallyClosed S1779R := by
  have hcoord : IsIntegrallyClosed S1909W.CoordinateRing :=
    sourceIntegrallyClosed_of_localizationDVR S1909W h
  exact (S1909_isIntegrallyClosed_iff_coord).mpr hcoord

/-- Exact characterization of the normality gap.  R' is integrally closed if and only
if the local DVR statement holds.  No normal instance is postulated. -/
theorem S1909_isIntegrallyClosed_iff_missing :
    IsIntegrallyClosed S1779R ↔ S1909NormalRPrimeMissing :=
  ⟨S1909_missing_of_isIntegrallyClosed, S1909_isIntegrallyClosed_of_missing⟩

/-- The exact missing trace-integrality input for all finite etale R'-algebras,
imported from S1909TraceTarget. -/
abbrev S1909TraceIntegral : Prop :=
  LeanFormal.IUT.XiFPaper.S1909TraceTarget.S1909TraceIntegral

/-- The finite etale integral closure target, imported from S1909TraceTarget. -/
abbrev S1909FiniteEtaleIntegralClosure : Prop :=
  LeanFormal.IUT.XiFPaper.S1909TraceTarget.S1909FiniteEtaleIntegralClosure

/-- The two inputs isolated by the trace-duality route to the finite etale integral
closure: normality of R' and trace integrality.  This is a proposition, not a proof of
either input and not a proof that the conjunction suffices. -/
abbrev S1909FiniteEtaleIntegralClosureResidual : Prop :=
  LeanFormal.IUT.XiFPaper.S1909TraceTarget.S1909FiniteEtaleIntegralClosureResidual

end LeanFormal.IUT.XiFPaper.S1909NormalRPrimeActual
