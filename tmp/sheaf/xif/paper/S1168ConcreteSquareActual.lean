import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

/-! # S1168: concrete canonical-link square from fPrimeStripAt / fLinkAt

This file constructs the four canonical-lift arrows from actual source
F-prime-strips/F-links and proves commEnv under the actual link-path equality.
The paper's evaluation/Kummer provenance is the first exact missing datum,
not the canonical-link path equality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1168ConcreteSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S1168Strip (F : FPrimeStrip.{umon, uv, upi} V) :=
  SourceFTimesMuPrimeStrip.canonical F

abbrev S1168Arrow (F G : FPrimeStrip.{umon, uv, upi} V) :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical F) (SourceFTimesMuPrimeStrip.canonical G)

noncomputable def s1168Arrow {F G : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F G) : S1168Arrow (V := V) F G :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ)

structure S1168CanonicalSquare
    (A B C D : FPrimeStrip.{umon, uv, upi} V) where
  upperEnv : S1168Arrow (V := V) A B
  lowerEnv : S1168Arrow (V := V) C D
  verticalEnv : S1168Arrow (V := V) A C
  verticalGau : S1168Arrow (V := V) B D
  commEnv : SourceFTimesMuPrimeStripFullPolyIsomorphism.comp verticalEnv lowerEnv = SourceFTimesMuPrimeStripFullPolyIsomorphism.comp upperEnv verticalGau

noncomputable def s1168CanonicalSquare
    {A B C D : FPrimeStrip.{umon, uv, upi} V}
    (φAB : FPrimeStripEquiv A B) (φCD : FPrimeStripEquiv C D)
    (φAC : FPrimeStripEquiv A C) (φBD : FPrimeStripEquiv B D)
    (hsq : FPrimeStripEquiv.trans φAC φCD = FPrimeStripEquiv.trans φAB φBD) :
    S1168CanonicalSquare (V := V) A B C D where
  upperEnv := s1168Arrow (V := V) φAB
  lowerEnv := s1168Arrow (V := V) φCD
  verticalEnv := s1168Arrow (V := V) φAC
  verticalGau := s1168Arrow (V := V) φBD
  commEnv := by
    unfold s1168Arrow
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.canonical_trans, SourceFTimesMuPrimeStripFullPolyIsomorphism.canonical_trans, hsq]

noncomputable def s1168SquareOfFamily
    (n m : Int)
    (hsq : FPrimeStripEquiv.trans (I.fLinkAt n m (n+1) m) (I.fLinkAt (n+1) m (n+1) (m+1)) = FPrimeStripEquiv.trans (I.fLinkAt n m n (m+1)) (I.fLinkAt n (m+1) (n+1) (m+1))) :
    S1168CanonicalSquare (V := V) (I.fPrimeStripAt n m) (I.fPrimeStripAt n (m+1)) (I.fPrimeStripAt (n+1) m) (I.fPrimeStripAt (n+1) (m+1)) :=
  s1168CanonicalSquare (V := V) (I.fLinkAt n m n (m+1)) (I.fLinkAt (n+1) m (n+1) (m+1)) (I.fLinkAt n m (n+1) m) (I.fLinkAt n (m+1) (n+1) (m+1)) hsq

end LeanFormal.IUT.XiFPaper.S1168ConcreteSquareActual

end
