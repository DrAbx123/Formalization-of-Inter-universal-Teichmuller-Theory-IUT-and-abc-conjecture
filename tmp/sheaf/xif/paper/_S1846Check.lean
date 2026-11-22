import tmp.sheaf.xif.paper.S1846MonoFFActual

open LeanFormal.IUT.XiFPaper.S1846MonoFFActual
open LeanFormal.IUT.XiFPaper.S1842RPrimeMonoActual

#check S1846MonoFaithfullyFlat
#check S1846SupportIdempotent_eq_one
#check S1846BCInjectiveOnMonos
#check S1846BCPreservesEpis
#check S1846PreservesEpis

#print axioms S1846SupportIdempotent_eq_one
#print axioms S1846MonoFaithfullyFlat
#print axioms S1846BCInjectiveOnMonos
#print axioms S1846BCPreservesEpis
#print axioms S1846PreservesEpis

example : S1842MonoFaithfullyFlat := S1846MonoFaithfullyFlat
#check S1842BCPreservesEpis_of_monoFaithfullyFlat S1846MonoFaithfullyFlat
