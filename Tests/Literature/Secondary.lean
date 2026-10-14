module

import KIP126.Def.Literature

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
open KIP126.Literature.Standard

example : sphereProduct syntheticH0 eta = 0 := toda_h0_eta

example (a : BiHom 2 3 (S_0_0 : SyntheticSpectrum)) :
    sphereProduct syntheticH0 a = 0 := toda_low_indeterminacy a

example (W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum)) :
    MossStatementAt W X Y Z := moss_at W X Y Z

#check may_pushpull
#check may_signed_boundary
#check moss_indeterminacy
#check mappingSphereCompatibility
#check toda_exists_relation
#check toda_relation_iff_indeterminacy
#check toda_shuffle_iff
#check toda_juggling
#check_failure KIP126.Literature.SecondaryResults
#check_failure KIP126.Literature.Route.MaySourceResults
#check_failure KIP126.Literature.Route.TodaSourceResults
