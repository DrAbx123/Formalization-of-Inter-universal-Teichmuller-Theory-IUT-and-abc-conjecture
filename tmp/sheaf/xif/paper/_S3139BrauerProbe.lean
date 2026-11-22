import Brauer.DualityH1
import Brauer.FundamentalClass
import Mathlib.Tactic

-- S3139: probe the Brauer duality / Artin pairing tools for the Galois-Kummer
-- compatibility (paper-faithful C2). Light imports; tool probe, not a paper object.

#check @PadicField.pairingH1
#check @PadicField.pairingH1_kummer
#check @PadicField.artinChar
#check @PadicField.pairing
#check @PadicField.eq_one_of_forall_pairingH1_eq_zero
#check @KummerTheory.kummer
#check @KummerTheory.kummerEquiv
#check @PadicField.exists_lift_artin
