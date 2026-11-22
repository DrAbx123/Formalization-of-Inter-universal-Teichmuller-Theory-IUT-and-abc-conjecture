import tmp.sheaf.xif.paper.S1960QPilotAnchorActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual

#check @reducedQPilotAnchor
#check @reducedQPilotTimesMu
#check @reducedAnchorIdentification
#check @s1960QPilotAnchoredUQ
#check @s1960QPilotAnchoredUQ_exists
#check @s1960_r6_exact_reduction

-- The constructed target: the S1958 package together with the reduced anchor.
example (D : S1895PaperInput) : Nonempty (S1960QPilotAnchoredUQ D) :=
  s1960QPilotAnchoredUQ_exists D

-- The reduced anchor is the lower-left (LGP) corner of the package square.
example (D : S1895PaperInput) :
    reducedQPilotAnchor D = (paperFullLogKummerUQ D).evaluationSquare.lowerLeft :=
  reducedQPilotAnchor_eq_packageSquare_lowerLeft D

-- S1895's paper-strip slot is the reduced self-identification, not R6.
example (D : S1895PaperInput) :
    (S1895PaperO D).paper_strip_identification =
      Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
        (reducedQPilotTimesMu D) (s1895TimesMuStrip D)) :=
  s1895PaperO_paper_strip_eq_reducedSelf D

-- The R6 interface, parameterized by the missing paper-side strip.
example (D : S1895PaperInput) (P : SourceFTimesMuPrimeStrip (FinitePrimePlace 2 7)) :
    Nonempty (QPilotAnchorIdentification D P) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D) P) :=
  s1960_r6_exact_reduction D P

#print axioms s1960QPilotAnchoredUQ_exists
#print axioms reducedQPilotAnchor_eq_packageSquare_lowerLeft

end
