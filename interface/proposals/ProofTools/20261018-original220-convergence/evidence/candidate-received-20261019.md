# Candidate complete mathematical Model for Proposition 2.20

Evidence status: a concrete spectra/synthetic construction with all Model fields addressed below; independent review is still pending. This is not a Lean-constructed `D : Model` and no proof of `False` or project sorry is used.

## Categories and fixed objects

Let C be the stable homotopy category of ordinary 2-local spectra, with its usual tensor, shift and actual functorial cofiber choices. Let Syn be the full stable symmetric-monoidal subcategory of non-hypercomplete HF2-based synthetic spectra in which every odd integer acts invertibly. Its unit is nu(S_(2)): nu preserves filtered colimits (Pstragowski local source 1913), and is additive, so applying nu to the filtered central-odd-integer localization of S gives precisely the corresponding odd localization of the synthetic unit. Mapping from its bigraded shifts to odd-local targets gives the same Hom groups as mapping from the old spheres, by the localization adjunction. Lambda inversion commutes with this central localization. This restriction is essential: lambda-invertible objects in Syn identify with Sp_(2), rather than all spectra. All finite cofibers, bigraded shifts and lambda quotients remain in Syn.

Take coefficients HF2. Take the actual classical HF2 Adams family and actual synthetic nu(HF2) Adams family, with the canonical coefficient-unit fiber towers. Let

M = H(Z_(2)) direct-sum H(Q[t]).

Set auxiliary.detector=M, detectorUnit the ordinary unit into H(Z_(2)). Set etaMap=0 and nuMap=0, permitted by AuxiliaryData (no Hopf identification is a Model field). Consequently auxiliary.nuCofiber is S_(2) wedge Sigma^4 S_(2). ClassicalObject therefore denotes integer shifts of S_(2), S_(2) wedge Sigma^4 S_(2), and M. All these are connective up to an integer shift and have finite-type mod-2 homology. They are not required to be 2-complete by Model.

## Complete Model field table

- StableHomotopyCategory, SyntheticCategory, both cofiber instances: actual stable categories and enhancement cofibers, restricted to the stated 2-local subcategories.
- coefficients: HF2, pi_0=F2, all other coefficient homotopy groups zero.
- classical, family, classicalTower, syntheticTower, classicalSuspension: actual coefficient-unit fiber towers and their full exact-couple spectral sequences, all maps natural and layers literally coefficient smash with the same tower stage.
- nu: Pstragowski synthetic analogue restricted to 2-local spectra; additive, zero/unit comparisons, nu(Sigma X)=Sigma^(1,1)nu X.
- nuExactTriangle: Pstragowski Lemma 4.23 (local source synthetic_spectra.tex around 2116): exactly the full mod-2-homology short exactness hypothesis used by Model.
- recovery: lambda inversion, with the full lambda-invertible subcategory equivalent to Sp_(2); Pstragowski Theorem 4.37/Proposition 4.40, local source around 2345-2410.
- exactness: the stable symmetric-monoidal lambda localization is exact, and all bigraded shifts exact/additive.
- sphereAlgebra/standardClasses: actual mod-2 Ext multiplication and actual h_i (no nonvanishing requirement is imposed by these fields).
- comparison: actual E2 polynomial-lambda comparison, its naturality and lambda compatibility; BHS theorem synth-ASS, local SynRevAdams.tex around 83-114. No GL/MH/crossing statement is used.
- quotients: actual cofibers of lambda powers and their natural rho/lambda/delta triangles.
- normalizedMap: when e=0 use nu(f) with zero-shift comparison. When e=1, actual target-tower factorization implies HF2-homology(f)=0. On C_lambda nu(-), maps of degree zero between heart objects are the actual homology maps, hence C_lambda nu(f)=0 and nu(f) factors through lambda. Choose such a factorization; its exact factorization equation is precisely the NormalizedSyntheticMap field. No uniqueness or filtration bound is imposed.
- firstQuotient: Pstragowski's C_lambda nu(X) heart/comodule identification and Ext formula, at the exact source shift/weight; local source around 2233, 2594, 2612. It applies without completeness.
- classicalConvergence and convergence: the weak canonical associated-graded identifications are constructed in the next section; no separation/strong convergence is claimed on M.
- comparisonCompatible.convergence_natural: this follows for ARBITRARY maps between selected objects from the already proved completely generic private theorem canonical_convergence_natural in KIP126/AdamsSynthetic/Standard/Background.lean:282-368. Its parameters are any P, X, Y, f, cx and cy, with no Standard-object hypothesis. The proof uses only canonical lift equations, actual tower maps, and epimorphy of the graded quotient. Thus the objectwise canonical constructions need no extra natural choice of completion maps. The rational invisible summands contribute zero to both grades; no arbitrary noncanonical graded isomorphism is used.
- comparisonCompatible.first_quotient and sphereDetectionCompatible: the above first-quotient identification uses the actual inclusion and actual canonical lift, so the first quotient detects that very homotopy representative. Sphere lambda action follows from the actual lambda maps and the same coefficient-tower lifts. Transfer from the completed sphere changes only an everywhere-filtered rational piece and is identical on every associated grade.
- multiplicationCompatible and sphereProductCommutative: the actual multiplicative canonical Adams comparison and symmetry of the synthetic unit. Only sphere operations are required, and their associated grades are identical to the completed sphere's. These assertions are independent of 2.20.

## Weak canonical convergence, without assuming incomplete objects complete

Write B=HZ_2 or the 2-complete sphere, and A=HZ_(2) or S_(2), respectively. The completion map A->B has rational cofiber H(V), V=Z_2/Z_(2). This V is uniquely divisible by 2 and, since all spectra are 2-local, rational. It is concentrated in stem zero. For S_(2), completion is an isomorphism on every positive stem and zero on negative stems. For HZ this is immediate on homotopy.

1. The completion triangle is mod-2-homology short exact. Thus nu(A)->nu(B)->nu(HV) is an actual triangle, by Pstragowski Lemma 4.23.
2. C_lambda nu(HV) is its homology comodule, hence zero. Therefore nu(HV) is lambda-invertible and its pi_(m,w) is V for m=0, zero otherwise, with lambda an isomorphism. Also nu(HV) tensor nu(HF2)=0: multiplication by 2 is invertible on the first factor and zero on the second factor. Its actual Adams tower maps are equivalences, all its filtration subgroups equal the whole group, and every associated grade and every spectral page is zero.
3. On completed B, BHS strong convergence supplies the actual canonical convergence, and the stem-zero calculation is
   pi_(0,w)nu(B)=2^max(w,0) Z_2,
   F^s pi_(0,w)nu(B)=2^max(s,w,0) Z_2.
   These are the ordinary h0 tower and its lambda copies, with no differential entering or leaving stem zero. In stem -1 all groups are zero. The map to nu(HV) is the actual reduction Z_2->V under these identifications, since lambda inversion is the completion map and lambda is injective on this stem-zero tower.
4. Every subgroup 2^N Z_2 maps onto V: for any z in Z_2 one can subtract its first N binary digits (an element of Z_(2)) to place it in 2^N Z_2. Hence pi_(0,w)nu(B)->V is surjective at EVERY weight. The actual triangle LES now gives pi_(-1,w)nu(A)=0; there is no unproved adjacent-stem exception. It also gives
   pi_(0,w)nu(A)=2^max(w,0) Z_(2).
   In all other stems the completion map is an isomorphism on synthetic homotopy (the rational cofiber has no such groups).
5. The associated graded transfer follows from the actual tower triangles, not from arbitrary E-equivalence. The coefficient smash of the rational cofiber is zero, so every fiber-tower comparison has the same rational cofiber and projection is identity on it. At stem zero, images onto V are surjective at each tower stage: 2^s pi_(0,w)nu(B) lies in F^s, and its reduction still surjects onto V. All other rational images are zero. The LES diagram therefore identifies the two successive filtration quotients. Explicitly the incomplete stem-zero filtration is
   F^s pi_(0,w)nu(A)=2^max(s,w,0) Z_(2).
   Its quotient by the next level is identical to B's quotient. The isomorphism is natural on the actual stage lift, layer map and projection; composing the completed canonical convergence with this graded isomorphism gives SyntheticCanonicalIdentification exactly as defined in Detection.lean. The corresponding classical assertion has the same proof with w=0.
6. Nu preserves finite sums. Thus nu(M)=nu(HZ_(2)) direct-sum nu(HQ[t]); the second summand has constant actual filtration and zero pages/grades as in step 2. Canonical weak convergence on M and nu(M) is the sum of the HZ_(2) comparison and the zero rational comparison. The same argument applies to S_(2) wedge Sigma^4 S_(2). Integer shifts of classical objects and all synthetic bigraded shifts simply reindex these canonical lift equations.
7. Every positive lambda quotient of nu(A) is equivalent to the corresponding quotient of nu(B): apply the exact quotient functor to the completion triangle and note that the lambda quotient of its lambda-invertible rational cofiber is zero. A zero-th quotient is zero. The rational summand of M also disappears after the first quotient. Hence every object in SyntheticObject involving a quotient is a finite iterated shift/quotient of the complete base objects nu(S_2-complete) and nu(HZ_2) (and finite sums).
8. Such iterated objects are nu(HF2)-nilpotent complete, because completion is closed under finite fibers/cofibers and shifts. Every fixed tridegree has finite F2 Adams input, inherited from those base objects and the finite lambda windows; the page groups form a Mittag-Leffler system, so lim^1_r vanishes. BHS/Boardman strong convergence therefore supplies their actual canonical convergence. This covers ALL recursively defined SyntheticObject objects, not only one quotient. Canonicality and naturality use the actual exact-couple lift/cofiber maps throughout.

The sole algebraic lemma used in step 5 can also be phrased independently. In a triangle A->B->R with coefficient smash R=0 and im(pi B->pi R) uniquely 2-divisible, the map gr(pi A)->gr(pi B) is an isomorphism: ker(pi A->pi B)=im(delta_0) lies in EVERY source filtration by the tower LES; surjectivity on grades follows by subtracting an (s+1)-stage representative with the same R-image from an s-stage representative. The image in R is independent of stage because 2^s pi B is in F^s and its image is all of the 2-divisible image. This is the actual representative-level identification, so the canonical condition is preserved.

## Contradiction to the target statement at the chosen objects

Choose X=sphere, Y=Z=detector=M, f=0. Define the actual HZ-linear map g by

  g(z,p(t)) = (0, z+t p(t)).

This additive map is injective: its constant polynomial coefficient is z, and its positive coefficients are those of p. M has no homotopy in other degrees. Thus for every d and a, a>>g=0 iff a=0 iff exists b, b>>f=a, exactly the original hexact with no stronger assumption.

At d=s=0, actual classical filtration on M is

  F^n pi_0(M)=2^n Z_(2) direct-sum Q[t]   (n>=0).

In particular its grade zero is F2. Let y be the E-infinity class canonically corresponding to (1,0) mod F^1, which is nonzero. Let a=(1,0). Then a>>g=(0,1) is in the rational summand and lies in EVERY actual Adams filtration. By the already Lean-proved classical_represents_zero_iff, the SAME a witnesses ClassicalExtension g 0 0 n y 0 for every natural n. Hence ClassicalPermanent holds, without exchanging witnesses.

If extensionBoundary_of_exact held, its conclusion would give a source class x and representative b with target y represented by b>>f=0. Canonical convergence is injective on grades, so the zero homotopy representative has grade zero; hence y=0, contradicting the chosen nonzero grade. This uses no disputed theorem, no target recursion, and no inconsistent project environment.

This is a counterexample to the GENERIC `D : Model` statement, not to AimPaper under its stated 2-complete hypotheses and not a Lean-constructed refutation of Standard.model. A production interface change requires independent review and user authorization.
