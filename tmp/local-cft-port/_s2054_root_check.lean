import ContinuousKummerTheory

-- Whole-port integration check: every module olean in the import cone must load together.
#print axioms KummerTheory.padicKummerZHatEquiv
#print axioms KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing
#check @KummerTheory.padicKummerZHatEquiv
#check @KummerTheory.kummerZHatEquivProfiniteCompletion
