import tmp.sheaf.xif.paper.S1844PointSeparatedActual
import Mathlib.AlgebraicGeometry.Limits
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
example : IsIso (coprodSpec S1726CoordinateRing S1726CoordinateRing) := by infer_instance
#check (asIso (coprodSpec S1726CoordinateRing S1726CoordinateRing))
