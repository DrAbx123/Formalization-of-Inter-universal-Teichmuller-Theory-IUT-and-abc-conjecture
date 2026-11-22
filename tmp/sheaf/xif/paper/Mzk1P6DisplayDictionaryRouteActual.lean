/- Route-valid P6 display terms from any accepted display source data. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryRouteActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
variable (D : P6DisplaySourceData)
noncomputable def p6RouteDisplayTerms : Thm110DisplayTerms := D.toTerms
theorem p6RouteDisplayTerms_eq : p6RouteDisplayTerms D = D.toTerms := rfl
#print axioms p6RouteDisplayTerms_eq
end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryRouteActual
end
