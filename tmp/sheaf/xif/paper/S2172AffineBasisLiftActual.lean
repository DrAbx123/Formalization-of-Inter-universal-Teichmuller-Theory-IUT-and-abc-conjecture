import tmp.sheaf.xif.paper.S2166AffinePairCorrespondenceActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual

open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual

/-- The actual additive equivalence between the projective 5-torsion carrier
and the affine 5-torsion carrier, obtained by restricting the projective/
affine point equivalence to the torsion subgroups. -/
noncomputable def S2172AffineTorsionEquiv :
    S1720Curve.LTorsion S1982Five ≃+ S2056Torsion where
  toFun P := ⟨S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W), by
    change (5 : ℤ) • S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W) = 0
    calc
      (5 : ℤ) • S1906ProjAffineEquiv (P : WeierstrassCurve.Projective.Point S2056W)
          = S1906ProjAffineEquiv ((5 : ℤ) • (P : WeierstrassCurve.Projective.Point S2056W)) :=
            (map_zsmul S1906ProjAffineEquiv (5 : ℤ)
              (P : WeierstrassCurve.Projective.Point S2056W)).symm
      _ = S1906ProjAffineEquiv 0 := by rw [show (5 : ℤ) •
            (P : WeierstrassCurve.Projective.Point S2056W) = 0 from P.2]
      _ = 0 := map_zero S1906ProjAffineEquiv⟩
  invFun Q := ⟨S1906ProjAffineEquiv.symm (Q : S2056W.Point), by
    change (5 : ℤ) • S1906ProjAffineEquiv.symm (Q : S2056W.Point) = 0
    calc
      (5 : ℤ) • S1906ProjAffineEquiv.symm (Q : S2056W.Point)
          = S1906ProjAffineEquiv.symm ((5 : ℤ) • (Q : S2056W.Point)) :=
            (map_zsmul S1906ProjAffineEquiv.symm (5 : ℤ) (Q : S2056W.Point)).symm
      _ = S1906ProjAffineEquiv.symm 0 := by rw [show (5 : ℤ) •
            (Q : S2056W.Point) = 0 from Q.2]
      _ = 0 := map_zero S1906ProjAffineEquiv.symm⟩
  left_inv P := Subtype.ext (S1906ProjAffineEquiv.symm_apply_apply _)
  right_inv Q := Subtype.ext (S1906ProjAffineEquiv.apply_symm_apply _)
  map_add' P Q := Subtype.ext (map_add S1906ProjAffineEquiv _ _)

/-- The actual affine lift of the S1982 projective torsion basis. -/
noncomputable def S2172AffineBasis :
    (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion :=
  (S1982Basis : (Fin 2 → ZMod S1982Five.value) ≃+ S1720Curve.LTorsion S1982Five).trans
    S2172AffineTorsionEquiv

/-- The exact S2166 affine-basis-lift target is actual. -/
theorem S2172AffineBasisLiftRequired_actual :
    Nonempty S2166AffineBasisLift :=
  ⟨⟨S2172AffineBasis⟩⟩

end LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual

end
