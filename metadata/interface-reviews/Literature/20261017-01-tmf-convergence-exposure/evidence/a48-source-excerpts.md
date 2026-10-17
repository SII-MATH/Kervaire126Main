## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Def/AdamsSynthetic/ComparisonStatements.lean:700–726
Blob text SHA-256: 3b508733d6a36e1b58b696016ce8fd67bac66b52b1f062beadfb3898f52be483
```lean
700: structure TmfDetectionData (H : Mod2EilenbergMacLane (C := C)) where
701:   spectrum : C
702:   algebra : MonObj spectrum
703:   labels : TmfDetectionClasses H
704:   sphereConvergence : TowerDetection.Convergence H.unit SphereSpectrum
705:   convergence : TowerDetection.Convergence H.unit spectrum
706:   kappaBar : HomotopyGroup (C := C) 20 SphereSpectrum
707:   wClass : HomotopyGroup (C := C) 45 SphereSpectrum
708: 
709: def TmfDetectionData.unit (S : TmfDetectionData H) : SphereSpectrum ⟶ S.spectrum :=
710:   S.algebra.one
711: 
712: def TmfDetectionData.high125 (S : TmfDetectionData H) :
713:     HomotopyGroup (C := C) 125 SphereSpectrum :=
714:   classicalSphereProduct
715:     (classicalSphereProduct (classicalSphereProduct S.kappaBar S.kappaBar)
716:       (classicalSphereProduct S.kappaBar S.kappaBar)) S.wClass
717: 
718: /-- Explicit identities with the specified detecting spectrum, its unit, its G classes
719: and its convergence. The page map is the map of the actual Adams tower,
720: so no unrelated linear equivalence is introduced. -/
721: structure TmfDetectorComparison (D : AdamsComparison H M Syn) (G : TmfDetectionClasses H) (S : TmfDetectionData H) where
722:   detectorIso : D.hopfAndDetector.detector ≅ S.spectrum
723:   unit : D.hopfAndDetector.detectorUnit ≫ detectorIso.hom = S.unit
724:   g : G.g = S.labels.g
725:   delta_h_1_mul_g : G.delta_h_1_mul_g = S.labels.delta_h_1_mul_g
726:   sphereConvergence : D.classicalConvergence .sphere = S.sphereConvergence
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Literature/Assumptions.lean:1–11
Blob text SHA-256: 6db465093d2e2a914c5c8e6d7f2411e3035013ed09b1369ad36c79ee116d3257
```lean
1: module
2: 
3: public import KIP126.Literature.Hypotheses
4: 
5: @[expose] public section
6: 
7: namespace KIP126.Literature
8: 
9: /-- The cited literature results, together with their source objects and
10: comparisons with the fixed classical and synthetic Adams sequences. -/
11: axiom adamsSyntheticResults : KIP126.ExternalHypotheses.LiteratureHypotheses
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Literature/Hypotheses.lean:23–27
Blob text SHA-256: 03c9fc8358e5a71c21ae74483b0a1076b0b3851ac271379ad6f9dd63cff288b3
```lean
23: structure LiteratureSources where
24:   tmfLabels : Literature.AdamsSynthetic.TmfDetectionClasses standardFoundation.hf2
25:   sourceComparisons : Literature.AdamsSynthetic.SourceComparisons standardAdamsComparison Def.standardEta
26:     tmfLabels Def.standardAdamsSyntheticComparisons
27:   br21Classes : Tmf.Br21Classes standardFoundation.hf2 sourceComparisons.tmfSource.spectrum
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Literature/Hypotheses.lean:182–184
Blob text SHA-256: 03c9fc8358e5a71c21ae74483b0a1076b0b3851ac271379ad6f9dd63cff288b3
```lean
182: structure LiteratureHypotheses where
183:   sources : LiteratureSources
184:   theorems : LiteratureTheorems sources
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Literature/Source.lean:297–305
Blob text SHA-256: 80fad1c52768fd9ba0e2e7868de514b86a4deb1658df3b81b04ea52556def207
```lean
297: structure SourceComparisons (background : AlgebraRealizationComparison D) where
298:   todaSource : SyntheticH0Class (Syn := Syn)
299:   kernelSource : SyntheticCompletionAdjunction Syn
300:   kernelComparison : RealizationKernelComparison D kernelSource
301:   classicalSource : ClassicalHopfThetaClasses H
302:   hopfComparison : ClassicalHopfComparison D η classicalSource
303:   synthetic_eta : EtaChoice M D.toAdamsComparisonData η
304:   tmfSource : TmfDetectionData H
305:   tmfComparison : TmfDetectorComparison D L tmfSource
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Main/AdamsSynthetic/SphereConvergence.lean:858–880
Blob text SHA-256: 25f13441f2122fc75f183337f23e9dba324a8dd9880b12c00057c5e10de51490
```lean
858: private theorem strong_of_acyclic_and_finite
859:     {C : Type u} [StableHomotopyCategory.{u,v} C]
860:     [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
861:     {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
862:     (hacyclic : IsENilpotentComplete unit X)
863:     (hfinite : ∀ (n : ℤ) (s : ℕ), Finite (LinearMap.ker
864:       (inducedMap (adamsTowerStep unit X s) n).toIntLinearMap)) :
865:     IsAdamsTowerStronglyConvergent unit X := by
866:   have hdelta (n : ℤ) := hom_delta_bijective (adamsResidualSequence unit X) hacyclic (Sphere n)
867:   have hsep (n : ℤ) := adams_separated_of_finite_ker unit X n (hfinite n) (hdelta n).1
868:   have hzero (n : ℤ) (x : HomotopyGroup n X)
869:       (hx : ∀ s : ℕ, x ∈ LinearMap.range
870:         (inducedMap (adamsTowerMap unit X 0 s (Nat.zero_le s)) n).toIntLinearMap) : x = 0 :=
871:     hsep n 0 x (fun s _ => hx s)
872:   refine ⟨?_, adams_filtration_separated unit X hzero, ?_⟩
873:   · intro n
874:     apply adams_complete_of_difference unit X n (hdelta n).2
875:     intro x hx
876:     apply hzero n x
877:     intro s
878:     simpa only [adamsHomotopyFiltrationSubmodule, adamsTowerToSpectrum,
879:       Int.toNat_natCast] using hx s
880:   · exact associatedGraded_of_separated unit X (integer_separated_of_natural unit X hsep)
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Def/ClassicalAdams/Convergence/Tower/Predicates.lean:19–33
Blob text SHA-256: 193f78a56d27f9916a3985b21dd32f377480577a2bd0834a52ad3bbb0e50fad0
```lean
19: variable {C : Type u} [StableHomotopyCategory.{u, v} C]
20:   [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
21: 
22: /-- Source-faithful strong convergence of this constructed Adams sequence.
23: The filtration, abutment and E∞ are fixed; witnesses assert properties of
24: them and do not select replacements. Completeness uses the canonical cone
25: to the filtration quotients. -/
26: structure IsAdamsTowerStronglyConvergent : Prop where
27:   complete : ∀ n : ℤ,
28:     Nonempty (Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n)
29:   separated : ∀ (n : ℤ) (S : Subobject (towerAbutment X n)),
30:     (∀ s : ℤ, S ≤ (adamsHomotopyFiltration unit X).F s n) → S = ⊥
31:   associatedGraded : ∀ (s t : ℤ),
32:     Nonempty (((adamsTowerInternalSpectralSequence unit X).ssData (s, t)).eInfty ≅
33:       (adamsHomotopyFiltration unit X).associatedGraded s (t - s))
```

## a484b981fad612eabe2bc7a01b54e049e9a01ce4:KIP126/Def/ClassicalAdams/Detection/Convergence/Canonical/Predicates.lean:19–32
Blob text SHA-256: df6884658eb825ce2949c29a8f7b4b7455fd405bc2d49c5d3a649d065991abcb
```lean
19: def CanonicalIdentification (X : C)
20:     (e : ∀ p : ℤ × ℤ,
21:       ((adamsTowerInternalSpectralSequence unit X).ssData p).eInfty ≅
22:         (filtration unit X).associatedGraded p.1 (p.2-p.1)) : Prop :=
23:   ∀ (p : ℤ × ℤ)
24:     (a : HomotopyGroup (p.2-p.1) (adamsTowerAt unit X p.1))
25:     (z : InfiniteRepresentative unit X p),
26:     infiniteRepresentativeE1 unit X p z = adamsJ unit X p.1 p.2 a →
27:     ∀ b : (Subobject.underlying.obj
28:       ((filtration unit X).F p.1 (p.2-p.1)) : ModuleCat ℤ),
29:     ((filtration unit X).F p.1 (p.2-p.1)).arrow b =
30:       inducedMap (adamsTowerMap unit X 0 p.1.toNat (Nat.zero_le _)) (p.2-p.1) a →
31:     (e p).hom (((adamsTowerInternalSpectralSequence unit X).ssData p).pageπ ⊤ z) =
32:       (filtration unit X).toAssociatedGraded p.1 (p.2-p.1) b
```
