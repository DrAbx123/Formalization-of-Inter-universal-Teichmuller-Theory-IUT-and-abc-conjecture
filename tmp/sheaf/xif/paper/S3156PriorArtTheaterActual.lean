import LeanFormal.IUT.Audit.Status

/-! # S3156: REPO-FIRST prior-art audit - theater family / F-prime-strip

The theater-family construction and laws ALREADY EXIST in the tree; reuse them
instead of re-proving.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Prior-art rows: (file:line, declaration, reuse action). -/
def S3156TheaterPriorArt : List (String × String × String) := [
  ("LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122", "sourceHaarActualPrimeStrip (n m : Int) : FPrimeStrip Unit", "REUSE: proven index-dependent prime-strip family"),
  (".../SourceUnitRegionHaarDataActual.lean:139", "sourceHaarActualThetaPacket", "REUSE for model theta packet shape"),
  (".../SourceUnitRegionHaarDataActual.lean:143", "sourceHaarActualTheater", "REUSE: concrete theater at index i"),
  (".../SourceUnitRegionHaarDataActual.lean:151", "sourceHaarActualPrimeStripEquiv", "REUSE: prime-strip equivalences"),
  (".../SourceUnitRegionHaarDataActual.lean:213", "sourceHaarActualTheaterLink", "REUSE: theater links"),
  (".../SourceUnitRegionHaarDataActual.lean:224-284", "theorem sourceHaarActualTheaterLink_refl / PrimeStripEquiv_symm/_trans / TheaterLink_symm/_trans", "REUSE: link laws"),
  (".../SourceUnitRegionHaarDataActual.lean:288", "sourceHaarActualTheater_injective", "REUSE: injectivity (index-dependent theater family)"),
  (".../SourceUnitRegionHaarDataActual.lean:322", "sourceHaarActualFamily", "REUSE: theater family"),
  (".../SourceUnitRegionHaarDataActual.lean:346", "sourceHaarActualOriginalInput (S : SourceDefinition31Data)", "REUSE: assembled OriginalInput"),
  (".../SourceUnitRegionHaarDataActual.lean:374", "sourceHaarActualImageRealization / sourceHaarActual_logDegreeAt_eq (384) / sourceHaarActual_sourceLocalLogDegree_nonpos (394)", "REUSE: realization + log-degree facts") ]

theorem S3156TheaterPriorArt_length : S3156TheaterPriorArt.length = 10 := rfl

/-- Prior-art audit record: theater family. -/
def S3156PriorArtTheater : Obligation :=
  { id := "IUT.project.prior-art-theater-family"
    source := "Lead §7.9 repo-first directive; SourceUnitRegionHaarDataActual.lean"
    status := VerificationStatus.interface
    note :=
      "PRIOR ART CONFIRMED (theater family): SourceUnitRegionHaarDataActual.lean proves the "
      ++ "concrete infinite index-dependent F-prime-strip/theater family with links, laws and "
      ++ "INJECTIVITY. Red file S3133ModelTheaterFamilyActual fails because it uses a wrong "
      ++ "namespace path (the file's namespace is LeanFormal.IUT, not the long directory path); "
      ++ "FIX: open LeanFormal.IUT (or fully qualify LeanFormal.IUT.sourceHaarActualTheater etc.) "
      ++ "and REUSE those declarations. Red file S3137ModelTheaterPrimeStripDataActual tries an "
      ++ "alternate Mon := Multiplicative (IntxInt) degree encoding against FPrimeStrip's "
      ++ "V-indexed Mon/degree fields; REUSE sourceHaarActualPrimeStrip instead. No re-proving."
    dependsOn := [] }

#check S3156PriorArtTheater
#check S3156TheaterPriorArt_length

end LeanFormal.IUT.Audit
