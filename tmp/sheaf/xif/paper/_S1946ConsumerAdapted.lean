/- Consumer / acceptance probe for S1946: checks the exact frozen target type of S1937
from the compiled olean, the two specification lemmas, and the compactification consumers. -/
import tmp.sheaf.xif.paper.S1946ChartAlgEquivActual

noncomputable section

open MvPolynomial HomogeneousLocalization
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open LeanFormal.IUT.XiFPaper.S1937ProjectiveClosureGeometryActual
open LeanFormal.IUT.XiFPaper.S1946ChartAlgEquivActual

attribute [local instance] MvPolynomial.gradedAlgebra

variable [GradedRing (CohomGr (R := S1726K) Wang)]

-- 1. The exact frozen statement of S1937, as an F'-algebra isomorphism (not a ring iso):
example : Away WGr Zbar ≃ₐ[S1726K] S1726CoordinateRing := S1946ChartAlgEquiv
example : S1937ChartAlgEquiv := S1946ChartAlgEquiv

-- 2. The S1925 ring residual is filled.
example : S1925ChartIso := S1946ChartIso

-- 3. It is the actual chart identification: X/Z |-> x, Y/Z |-> y.
example : S1946ChartAlgEquiv XZ = xAff := S1946ChartAlgEquiv_XZ
example : S1946ChartAlgEquiv YZ = yAff := S1946ChartAlgEquiv_YZ

-- 4. Consumer: S1937's scheme-level compactification datum with the chart input supplied.
example (hdense : S1925DenseChart) := S1946AffineCompactification hdense
-- 5. ... and unconditionally in its chart input once the homogeneous coordinate ring is a
-- domain (the single remaining S1937 residual, density).
example (hdom : IsDomain W) := S1946Compactification_of_domain hdom

#check @S1946ChartAlgEquiv
#print axioms S1946ChartAlgEquiv
#print axioms S1946Compactification_of_domain
