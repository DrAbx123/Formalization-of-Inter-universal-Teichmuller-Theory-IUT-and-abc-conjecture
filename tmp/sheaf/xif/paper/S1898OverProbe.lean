import tmp.sheaf.xif.paper.S1898EllipticInvolutionActual
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

example (h : S1898AffineEndo = 𝟙 S1726AffineOver) :
    S1898CoordEndo = AlgHom.id S1726K S1726CoordinateRing := by
  have hleft := congrArg (fun f : S1726AffineOver ⟶ S1726AffineOver => f.left) h
  change Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
    𝟙 (Spec (CommRingCat.of S1726CoordinateRing)) at hleft
  sorry
