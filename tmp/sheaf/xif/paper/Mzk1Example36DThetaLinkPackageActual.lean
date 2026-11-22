import LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1Example36DThetaLinkPackageActual — A479 real packages (DTheta at / H1 links)

New conjunction packages combining the existing donors of
`SourceH1H2Construction.lean`:

1. `dThetaAt_package`: the DTheta-at map's projection compatibility,
   Pi-bijectivity, G-bijectivity and identity form jointly (:78/84/88/99);
2. `fLinkAt_laws_package`: F-link symmetry and transitivity jointly
   (:222/232);
3. `dLinkAt_laws_package`: D-link symmetry and transitivity jointly
   (:227/238).

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Example36DThetaLinkPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

/-- Joint DTheta-at package (compatibility + two bijectivities + identity). -/
theorem dThetaAt_package {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n m).proj v ((I.dThetaAt n m).isoPi v x) =
        (I.dThetaAt n m).isoG v ((I.dPrimeStripAt n m).proj v x) ∧
      Function.Bijective ((I.dThetaAt n m).isoPi v) ∧
      Function.Bijective ((I.dThetaAt n m).isoG v) ∧
      I.dThetaAt n m = DPrimeStripEquiv.refl (I.dPrimeStripAt n m) :=
  ⟨I.dThetaAt_compatibility n m v x,
   I.dThetaAt_bijective_pi n m v,
   I.dThetaAt_bijective_g n m v,
   I.dThetaAt_identity n m⟩

/-- Joint F-link laws (symmetry + transitivity). -/
theorem fLinkAt_laws_package {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.symm (I.fLinkAt n m n' m') =
        I.fLinkAt n' m' n m ∧
      FPrimeStripEquiv.trans (I.fLinkAt n m n' m')
          (I.fLinkAt n' m' n'' m'') =
        I.fLinkAt n m n'' m'' :=
  ⟨I.fLinkAt_symm n m n' m', I.fLinkAt_trans n m n' m' n'' m''⟩

/-- Joint D-link laws (symmetry + transitivity). -/
theorem dLinkAt_laws_package {l : PrimeGeFive} {V : Type*}
    (I : OriginalInput l V) (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.symm (I.dLinkAt n m n' m') =
        I.dLinkAt n' m' n m ∧
      DPrimeStripEquiv.trans (I.dLinkAt n m n' m')
          (I.dLinkAt n' m' n'' m'') =
        I.dLinkAt n m n'' m'' :=
  ⟨I.dLinkAt_symm n m n' m', I.dLinkAt_trans n m n' m' n'' m''⟩

#check dThetaAt_package
#check fLinkAt_laws_package

end LeanFormal.IUT.XiFPaper.Mzk1Example36DThetaLinkPackageActual
end