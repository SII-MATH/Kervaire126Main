module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Computation.Lambda


@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

section
open CategoryTheory.Limits KIP126.Computation.SphereAndCofiber KIP126.Algebra
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}

/-- Stabilized incoming boundaries identify the BHS permanent quotient with
the same complete classical infinity frame. -/
private theorem theta_quotient_frame
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  refine ⟨x',rfl,?_⟩
  have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hzero : P.pageπ ⊤ z'=0) :
      PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
    have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
    change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
      (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
    rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
    refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
    rw [←hb]
    change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
      (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
    congr 1
    dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  rcases hall (P.pageπ ⊤ z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_infinity_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x ∈ _
    rw [←hz',←hz,←map_sub]
    exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])

/-- BHS label agreement and the actual nu-unit map transport common infinity
representatives to the synthetic sphere, including the zero case. -/
private theorem theta_sphere_frame_family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
    familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
  have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
  have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
      (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _


private theorem theta_sphere_frame_map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [theta_sphere_frame_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem theta_sphere_frame
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  classical
  obtain ⟨x',hx',hframe⟩ := theta_quotient_frame I s t k hst hsk x hx
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := theta_sphere_frame_map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [theta_sphere_frame_family_map_data,theta_sphere_frame_family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [theta_sphere_frame_family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh

/-- Actual convergence gives either nonzero leading detection or membership
in the next actual tower filtration. -/
private theorem theta_detection_step
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)

  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    classical
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha

  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := (D.sphereConvergence.identification i).inv q
  have he : (D.sphereConvergence.identification i).hom e=q :=
    ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (subobject_cokernel_π_eq_zero_iff
      (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
      (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
    rw [ha'] at hmem
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
/-- The two complete frames and the intervening finite-page gap yield the
three branches, retaining an actual lambda preimage in the last branch. -/
private theorem theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
    (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
    Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    let E := (sequence D .sphere).ssData (s, t)
    haveI : Subsingleton (E.page 4) := hpage
    have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
        PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
      rintro x ⟨z, hz⟩
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
      have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
      refine ⟨y, ?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
      have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
          PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
        dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
        rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
      rw [← hfactor, CategoryTheory.comp_apply]
      apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
      exact (congrArg (fun f => f z)
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
    have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
      rintro ⟨x⟩
      change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
      apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
      exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩



private theorem theta_three_cases_from_frames
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D)
    (x10 : E2 H SphereSpectrum 10 134) (x13 : E2 H SphereSpectrum 13 137)
    (h10 : ClassicalInfinityGenerated 10 134 x10)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha10 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a) :
    SphereDetected D 10 134 6 x10 a ∨ SphereDetected D 13 137 9 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 10 b=a := by
  classical
  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
    classical
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      11 13 124 128 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-128) (j,124+j)) :=
      theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 128 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

  have hf10 := theta_sphere_frame I BHS 10 134 6 (by omega) (by omega) x10 h10

  rcases theta_detection_step (10,134,128) (D.sphereE2 10 134 6 x10) hf10 a ha10 with hdet|ha11
  · exact Or.inl hdet
  have ha13 := hgap ha11
  have hf13 := theta_sphere_frame I BHS 13 137 9 (by omega) (by omega) x13 h13
  rcases theta_detection_step (13,137,128) (D.sphereE2 13 137 9 x13) hf13 a ha13 with hdet|ha14
  · exact Or.inr (Or.inl hdet)
  right; right
  have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have h := BHS.filtration_lambda .sphere 124 128 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb


open CategoryTheory.Limits KIP126.Algebra in
/-- On the last possible outgoing page of a finite quotient, a classical
nonzero differential remains nonzero. A zero target would give a common
infinite-cycle representative and hence a classical cycle one page later. -/
private theorem finite_last_nonzero_last_cycle_infinity_lift
    (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) Tridegree)
    (r : ℤ) (hr : E.r₀ ≤ r) (p : Tridegree)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → E.d j p = 0) :
    ∃ zi : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top)) zi = z := by
  classical
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hsucc : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hsucc)
  have hker : D.pageπ ↑n z ∈ LinearMap.ker (E.d r p).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image] at hker
  obtain ⟨z',hz'⟩ := hker
  change D.pageπ ↑n (i z') = D.pageπ ↑n z at hz'
  have hzero : D.pageπ ↑n (z-i z')=0 := by rw [map_sub,hz',sub_self]
  have hb : ∃ b : (Subobject.underlying.obj (D.B ↑n) : ModuleCat.{v} ℤ),
      (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)) b = z-i z' :=
    (cokernel_π_eq_zero_iff_mem_range _ _).mp hzero
  obtain ⟨b,hb⟩ := hb
  have hBZ : D.B ↑n ≤ D.Z ↑(n+1) := (D.B_mono hsucc).trans (D.B_le_Z _)
  let zn : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ) :=
    z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ) b
  have hnz : i zn=z := by
    dsimp only [zn]
    rw [map_add]
    change i z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ ≫ i) b = z
    dsimp only [i]
    rw [Subobject.ofLE_comp_ofLE,hb]
    abel
  have hn1 : (r+1-E.r₀).toNat=n+1 := by dsimp only [n]; omega
  have hZ : D.Z ⊤ = D.Z ↑(n+1) := by
    have hh := cycles_top_eq_of_d_eq_zero E (r+1) (by omega) p hout
    simpa only [hn1] using hh
  let zi := (Subobject.ofLE (D.Z ↑(n+1)) (D.Z ⊤) hZ.ge) zn
  refine ⟨zi,?_⟩
  dsimp only [zi]
  rw [←CategoryTheory.comp_apply,Subobject.ofLE_comp_ofLE]
  exact hnz



private theorem finite_last_nonzero_normalized_last_cycle_infinity
    (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.E₂ i) (xr : A.Page r i)
    (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r i x xr)
    (hd : A.d r i xr = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → A.d j i = 0) :
    ∃ e, HasInfinityRepresentative A 2 i x e := by
  classical
  rcases A with ⟨⟨⟨r₀,S,deg,d⟩,dd,Zs,Bs⟩,hf,hdeg⟩
  dsimp only at hf
  subst r₀
  have hdg : deg=syntheticAdamsDifferentialDegree := funext hdeg
  subst deg
  let E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) Tridegree :=
    ⟨⟨2,S,syntheticAdamsDifferentialDegree,d⟩,dd,Zs,Bs⟩
  obtain ⟨hr,z,hz,hzr⟩ := hx
  simp only [SyntheticAdamsSS.d,eqToHom_refl,Category.id_comp,Category.comp_id] at hd hout
  have hz0 : E.d r i ((E.ssData i).pageπ ↑(r-2).toNat z) = 0 := by
    rw [hzr]
    exact hd
  have ho : ∀ j : ℤ, r+1≤j → E.d j i=0 := hout
  obtain ⟨zi,hzi⟩ := finite_last_nonzero_last_cycle_infinity_lift E r hr i z hz0 ho
  refine ⟨(S i).pageπ ⊤ zi,by norm_num,zi,?_,rfl⟩
  change ((Subobject.ofLE _ _ ((S i).Z_anti le_top)) ≫ (S i).pageπ 0) zi=x
  rw [←hz,←hzi]
  rw [←CategoryTheory.comp_apply]
  dsimp only [E]
  rw [Subobject.ofLE_comp_ofLE_assoc]
  rfl


private theorem finite_last_nonzero_finite_quotient_rep_naturality {D : AdamsComparison H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree)
    (x : (D.family.obj X).E₂ i) (xr : (D.family.obj X).Page r i)
    (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj X) r i x xr) :
    KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj Y) r i
      (familyPageMap D.family f 2 i x) (familyPageMap D.family f r i xr) := by
  classical
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _

  obtain ⟨hr,z,hz,he⟩ := hx
  let F := (D.family.functor.map f).toSSDataMorphism
  let n : WithTop ℕ := ↑(r-2).toNat
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z n)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=x at hz
  refine ⟨hr,F.cycleMap i n z,?_,?_⟩
  · rw [family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤n from bot_le)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · rw [family_map_data]
    exact (congrArg (fun a => a z) (F.pageπ_pageMap i n)).symm.trans
      (congrArg (fun q => F.pageMap i n q) he)



private theorem finite_last_nonzero_finite_quotient_d_naturality {D : AdamsComparison H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ (D.family.obj Y).d r i =
      (D.family.obj X).d r i ≫ familyPageMap D.family f r (syntheticAdamsDifferentialTarget r i) := by
  classical
  have h := (D.family.functor.map f).pageMap_comm_d r i
  dsimp only [familyPageMap,SyntheticAdamsSS.d,SyntheticAdamsFamily.obj]
  simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp]
  erw [←Category.assoc (SpectralSequenceMorphism.pageMap (D.family.functor.map f) r i)
    ((D.family.functor.obj Y).d r i), h]
  simp only [Category.assoc]
  have hi : i+(D.family.functor.obj X).diffDeg r=syntheticAdamsDifferentialTarget r i := by
    simp only [D.family.differentialDegree,syntheticAdamsDifferentialTarget]
  erw [←eqToHom_naturality_assoc (fun j => (D.family.functor.map f).pageMap r j) hi]
  simp only [eqToHom_trans]




private theorem finite_last_nonzero_quotient_family_map_data {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
  have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
  have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
      (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _



private theorem finite_last_nonzero_quotient_family_map_comp {D : AdamsComparison H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (i : Tridegree) :
    familyPageMap D.family (f ≫ g) r i =
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i := by
  classical
  rw [finite_last_nonzero_quotient_family_map_data,finite_last_nonzero_quotient_family_map_data,finite_last_nonzero_quotient_family_map_data]
  rw [D.family.functor.map_comp]
  exact SSDataMorphism.pageMap_comp (D.family.functor.map f).toSSDataMorphism
    (D.family.functor.map g).toSSDataMorphism i _



private theorem finite_last_nonzero_quotient_hasDifferential_map {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y)
    (r : ℤ) (i j : Tridegree)
    (x : (D.family.obj X).E₂ i) (y : (D.family.obj X).E₂ j)
    (h : KIP126.Synthetic.SpectralSequence.HasDifferential (D.family.obj X) r i j x y) :
    KIP126.Synthetic.SpectralSequence.HasDifferential (D.family.obj Y) r i j
      (familyPageMap D.family f 2 i x) (familyPageMap D.family f 2 j y) := by
  classical
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := h
  refine ⟨hdeg,familyPageMap D.family f r i xr,familyPageMap D.family f r j yr,
    finite_last_nonzero_finite_quotient_rep_naturality f r i x xr hx,
    finite_last_nonzero_finite_quotient_rep_naturality f r j y yr hy,?_⟩
  have heq : familyPageMap D.family f r i ≫ (D.family.obj Y).d r i ≫
      eqToHom (congrArg ((D.family.obj Y).Page r) hdeg) =
      ((D.family.obj X).d r i ≫ eqToHom (congrArg ((D.family.obj X).Page r) hdeg)) ≫
        familyPageMap D.family f r j := by
    rw [←Category.assoc,finite_last_nonzero_finite_quotient_d_naturality,Category.assoc]
    subst j
    simp
  have hz := congrArg (fun a => a xr) heq
  simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply,hd] using hz



private theorem finite_last_nonzero_classical_to_finite_equation {D : AdamsComparison H M Syn}
    (BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (q r k : ℕ) (hr : 2≤r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.quotient (S_0_0 : Syn) q) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      (D.quotientLabel q s t k x)
      (D.quotientLabel q (s+r) (t+r-1) (k+(r-1)) y) := by
  classical
  let f : (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum) ⟶
      (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let ny : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))).E₂
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 (s+r) (t+r-1) (k+(r-1)) y
  have hnx : familyPageMap D.family f 2 (s,t,t-k) nx = D.sphereE2 s t k x := by
    convert D.comparisonCompatible.sphere_nu s t k x using 1 <;> simp [nx,f,ClassicalObject.obj] <;> rfl
  have hny : familyPageMap D.family f 2 (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) ny =
      D.sphereE2 (s+r) (t+r-1) (k+(r-1)) y := by
    convert D.comparisonCompatible.sphere_nu (s+r) (t+r-1) (k+(r-1)) y using 1 <;> simp [ny,f,ClassicalObject.obj] <;> rfl
  have hs := (BHS.differentials .sphere 0 s t r k hr x y).mp h
  have hx : familyPageMap D.family (f ≫ XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      nx = D.quotientLabel q s t k x := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap D.family (XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      (familyPageMap D.family f 2 (s,t,t-k) nx) = _
    rw [hnx]
    rfl
  have hy : familyPageMap D.family (f ≫ XModLambdaN.incl S_0_0 q) 2
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      ny =
      D.quotientLabel q (s+r) (t+r-1) (k+(r-1)) y := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap D.family (XModLambdaN.incl S_0_0 q) 2 _
      (familyPageMap D.family f 2 _ ny) = _
    rw [hny]
    rfl
  have hs' : KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      nx
      ny := by
    convert hs using 1 <;> simp [nx,ny,ClassicalObject.obj]
  have ht := finite_last_nonzero_quotient_hasDifferential_map (f ≫ XModLambdaN.incl S_0_0 q) r
    (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) _ _ hs'
  rw [hx,hy] at ht
  exact ht



private theorem finite_last_nonzero_family_map_data {D : AdamsComparison H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
  have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
  have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
      (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _


private theorem finite_last_nonzero_family_page_comp {D : AdamsComparison H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [finite_last_nonzero_family_map_data,finite_last_nonzero_family_map_data,finite_last_nonzero_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem finite_last_nonzero_family_infinity_representative_map {D : AdamsComparison H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [finite_last_nonzero_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])



private theorem finite_last_nonzero_quotient_nu_infinity_cycles {D : AdamsComparison H M Syn}
    (BHS : EInftyComparison D) (q k : ℕ) (hk : k < q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (e : ((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,t-k)).eInfty)
    (hx : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x) e) :
    x ∈ PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-k) (s,t) := by
  classical
  let P := BHS.presentation
  let Zq := PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t)
  let Z1 := PageRepresentatives.cycles H SphereSpectrum ((k+1:ℕ)-t+(t-k)) (s,t)
  let Bk := PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-k)) (s,t)
  have hq : 0 < q := by omega
  have hsurj : Function.Surjective (NestedQuotient.projection Zq Bk) := by rintro ⟨a⟩; exact ⟨a,rfl⟩
  obtain ⟨x',hx'⟩ := hsurj (P.finiteWindow SphereSpectrum q hq (s,t) (t-k) (by constructor <;> omega) e)
  have hrep' : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x'.val) e :=
    (BHS.labels.1 .sphere q hq (s,t) k hk x' e).mpr hx'.symm
  let rho := (D.quotientTower (D.nu.functor.obj SphereSpectrum)).rho (k+1) q (by omega)
  let ek := ((D.family.functor.map rho).eInftyMap (s,t,t-k)) e
  have restrict (y : E2 H SphereSpectrum s t)
      (hy : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D .sphere q s t k y) e) :
      HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum (k+1)) 2 (s,t,t-k)
        (finiteTargetLabel D .sphere (k+1) s t k y) ek := by
    have hh := finite_last_nonzero_family_infinity_representative_map rho (s,t,t-k) _ _ hy
    have hlabel : familyPageMap D.family rho 2 (s,t,t-k) (finiteTargetLabel D .sphere q s t k y)=
        finiteTargetLabel D .sphere (k+1) s t k y := by
      change familyPageMap D.family rho 2 (s,t,t-k)
        (familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (targetNuLabel D .sphere s t k y)) =
        familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) (k+1)) 2 (s,t,t-k)
          (targetNuLabel D .sphere s t k y)
      rw [←CategoryTheory.comp_apply,finite_last_nonzero_family_page_comp]
      dsimp only [rho]
      rw [FiniteLambdaQuotientTower.rho_quotient]
    exact hlabel ▸ hh
  have hz1 : Z1 = ⊤ := by
    dsimp only [Z1]
    have hindex : ((k+1:ℕ):ℤ)-t+(t-k)=1 := by omega
    rw [hindex,PageRepresentatives.cycles_one]
  let y : Z1 := ⟨x,by rw [hz1]; trivial⟩
  let y' : Z1 := ⟨x'.val,by rw [hz1]; trivial⟩
  have hy := (BHS.labels.1 .sphere (k+1) (by omega) (s,t) k (by omega) y ek).mp (restrict x hx)
  have hy' := (BHS.labels.1 .sphere (k+1) (by omega) (s,t) k (by omega) y' ek).mp (restrict x'.val hrep')
  have heq : NestedQuotient.projection Z1 Bk y=NestedQuotient.projection Z1 Bk y' := hy.symm.trans hy'
  have hd : x-x'.val ∈ Bk := by
    apply (NestedQuotient.projection_eq_zero (y-y')).mp
    rw [map_sub,heq,sub_self]
  have hz : x-x'.val ∈ Zq := PageRepresentatives.boundaries_le_cycles H SphereSpectrum (s,t) _ _ hd
  have hh := Zq.add_mem hz x'.property
  have hindex : (q:ℤ)-t+(t-k)=(q:ℤ)-k := by omega
  simpa only [sub_add_cancel,Zq,hindex] using hh


private theorem finite_last_nonzero_sphere_quotient_label_to_nu {D : AdamsComparison H M Syn} (q k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x) = finiteTargetLabel D .sphere q s t k x := by
  classical
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let f := XModLambdaN.map D.nu.unitIso.inv q
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem finite_last_nonzero_nonzero_differential_not_cycle
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.SpectralSequence.HasNonzeroDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    x ∉ PageRepresentatives.cycles H SphereSpectrum r (s,t) := by
  classical
  intro hx
  have hc : PageRepresentatives.IsCycle H SphereSpectrum ((r:ℤ)+1-1) (s,t) x := by
    refine ⟨by omega, ?_⟩
    simpa only [add_sub_cancel_right] using hx
  obtain ⟨xnext,hnext⟩ := (PageRepresentatives.isCycle_iff_represents H SphereSpectrum
    ((r:ℤ)+1) (by omega) (s,t) x).mp hc
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd,hn⟩ := h
  have hz := represents_d_zero_of_later (by change (2:ℤ)≤r; omega)
    (by omega : (r:ℤ)<(r:ℤ)+1) hxr ⟨xnext,hnext⟩
  apply hn
  rw [←hd]
  change (eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r) hdeg))
    ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r (s,t) xr) = 0
  rw [hz,map_zero]


private theorem finite_last_nonzero
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    (BHS : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (q r k : ℕ) (hr : 2≤r) (hqr : q=k+r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.SpectralSequence.HasNonzeroDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    FiniteNonzeroDifferential D q r s t (s+r) (t+r-1) k (k+(r-1)) x y := by
  classical
  let A := D.family.quotient (S_0_0 : Syn) q
  let N := D.family.nuQuotient D.nu SphereSpectrum q
  let f := XModLambdaN.map D.nu.unitIso.inv q
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := finite_last_nonzero_classical_to_finite_equation BHS q r k hr s t x y h.toHasDifferential
  refine ⟨hdeg,xr,yr,hx,hy,hd,?_⟩
  intro hyr
  have hz : A.d r (s,t,t-k) xr=0 := by
    have hi := (ModuleCat.mono_iff_injective
      (eqToHom (congrArg (A.Page r) hdeg))).mp inferInstance
    apply hi
    change (A.d r (s,t,t-k) ≫ eqToHom (congrArg (A.Page r) hdeg)) xr = _
    rw [hd,hyr,map_zero]
  let nxr := familyPageMap D.family f r (s,t,t-k) xr
  have hnx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage N r (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x) nxr := by
    have hh := finite_last_nonzero_finite_quotient_rep_naturality (D:=D) f r (s,t,t-k) (D.quotientLabel q s t k x) xr hx
    rw [finite_last_nonzero_sphere_quotient_label_to_nu] at hh
    exact hh
  have hnz : N.d r (s,t,t-k) nxr=0 := by
    have hh := congrArg (fun a => a xr) (finite_last_nonzero_finite_quotient_d_naturality (D:=D) f r (s,t,t-k))
    change N.d r (s,t,t-k) nxr =
      familyPageMap D.family f r (syntheticAdamsDifferentialTarget r (s,t,t-k)) (A.d r (s,t,t-k) xr) at hh
    simpa only [hz,map_zero] using hh
  have hout : ∀ j : ℤ, (r:ℤ)+1 ≤ j → N.d j (s,t,t-k)=0 := by
    intro j hj
    have hv := BHS.finite_quotient_page_vanishing .sphere q (by omega)
      j (s+j) (t+(j-1)) (t-k) (by omega) (Or.inr (by omega))
    have ht : syntheticAdamsDifferentialTarget j (s,t,t-k)=(s+j,t+(j-1),t-k) := by
      simp [syntheticAdamsDifferentialTarget,syntheticAdamsDifferentialDegree]
    haveI : Subsingleton (N.Page j (syntheticAdamsDifferentialTarget j (s,t,t-k))) := by
      rw [ht]
      exact hv
    ext z
    exact Subsingleton.elim _ _
  obtain ⟨e,he⟩ := finite_last_nonzero_normalized_last_cycle_infinity N r (s,t,t-k) _ nxr hnx hnz hout
  have hc := finite_last_nonzero_quotient_nu_infinity_cycles BHS.eInfty q k (by omega) s t x e he
  have hidx : (q:ℤ)-k=(r:ℤ) := by omega
  rw [hidx] at hc
  exact finite_last_nonzero_nonzero_differential_not_cycle r hr s t x y h hc


end

end
end KIP126.Main.SectionSeven
