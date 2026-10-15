module

public import KIP126.Computation.LinCoordinates.Certificates.LowDegrees
public import KIP126.Main.SectionSeven.SphereClasses
public import KIP126.Main.SectionSeven.Lambda

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison

local notation "M" => standardMilnorCooperations

local notation "I" => computationTheorems

local notation "η" => etaClass

local notation "h₀" => literatureTheorems.toda.h0

section ThetaBShuffleProof

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}

open KIP126.Literature.AdamsSynthetic
open KIP126.LinE2 KIP126.Algebra KIP126.StableHomotopy.Toda
set_option maxHeartbeats 4000000 in
private theorem theta_b_shuffle_from_low_degrees (D' : AdamsComparison H M' Syn)
    (BHS : EInftyComparison D') (V:SphereVanishingLine H)
    (eta_nonzero_unique : ∀ x y : E2 H SphereSpectrum 1 2, x ≠ 0 → y ≠ 0 → x = y)
    (h23 : Subsingleton (E2 H SphereSpectrum 2 3))
    (h0:BiHom 0 1 (S_0_0:Syn)) (eta:BiHom 1 2 (S_0_0:Syn))
    (hlambda:lambdaMultiply 1 h0=syntheticTwo)
    (theta:BiHom 62 64 (S_0_0:Syn)) (b:BiHom 62 70 (S_0_0:Syn))
    (htheta:theta+theta=0) (hb:b+b=0)
    (z:BiHom 125 134 (S_0_0:Syn)) (hz:TripleToda theta syntheticTwo b z)
    (hv:TripleToda syntheticTwo theta syntheticTwo (lambdaMultiply 2 (sphereProduct eta theta))) :
    lambdaMultiply 2 (sphereProduct h0 z)=lambdaMultiply 3 (sphereProduct eta (sphereProduct theta b)) := by
  classical
  letI := D'.syntheticTriangulated
  have lambda_one_division_of_quotient_zero
      {X : Syn} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
      ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
    obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors 1 z).mp hz
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let e : F.obj (Smn m w : Syn) ≅ Smn m (w-1) :=
      (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp [sub_eq_add_neg])
    let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).preimage (e.hom≫a)
    have hb : F.map b=e.hom≫a :=
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_preimage _
    refine ⟨b,?_⟩
    have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
      unfold lambdaMultiply
      change eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
        lambdaPow 1 (Smn m w) ≫ b =
        (eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
        lambdaPow 1 (Smn m w) ≫ b
      exact (Category.assoc _ _ _).symm
    rw [he]
    rw [←lambdaPow_naturality 1 b]
    change e.inv≫F.map b≫lambdaPow 1 X=z
    rw [hb]
    simp only [Category.assoc,e.inv_hom_id_assoc]
    exact ha
  have sphere_one_three_zero (BHS : EInftyComparison D')
      (V : SphereVanishingLine H) (h23 : Subsingleton (E2 H SphereSpectrum 2 3))
      (z : BiHom 1 3 (S_0_0 : Syn)) : z=0 := by
    have hsep := D'.homotopySeparated .sphere 1 3
    refine (D'.convergence .sphere).eq_zero_of_eInfty_isZero_ge 0 1 3 hsep ?_ z ?_
    · intro j hj
      let i : Tridegree := (j,1+j,3)
      let P := BHS.presentation.nu SphereSpectrum ((j:ℤ),1+j) 3
      haveI : Subsingleton (PageRepresentatives.nuEInftyModel H SphereSpectrum ((j:ℤ),1+j) 3) := by
        dsimp only [PageRepresentatives.nuEInftyModel]
        split_ifs with h
        · have hs : Subsingleton (E2 H SphereSpectrum j (1+j)) := by
            by_cases he : j=2
            · subst j; exact h23
            · exact V _ _ (by omega) (by omega)
          letI : Subsingleton (PageRepresentatives.permanentCycles H SphereSpectrum ((j:ℤ),1+j)) :=
            ⟨fun a b => Subtype.ext (hs.elim _ _)⟩
          refine ⟨?_⟩
          rintro ⟨a⟩ ⟨b⟩
          exact congrArg (NestedQuotient.projection _ _) (Subsingleton.elim a b)
        · infer_instance
      apply ModuleCat.isZero_iff_subsingleton.mpr
      apply subsingleton_of_forall_eq 0
      intro e
      have he : (D'.family.functor.map D'.nu.unitIso.inv).eInftyMap i e=0 :=
        P.injective (Subsingleton.elim _ _)
      have hh := congrArg (fun a => (D'.family.functor.map D'.nu.unitIso.hom).eInftyMap i a) he
      change ((D'.family.functor.map D'.nu.unitIso.inv).eInftyMap i ≫
        (D'.family.functor.map D'.nu.unitIso.hom).eInftyMap i) e=_ at hh
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
      simpa only [ConcreteCategory.id_apply,map_zero] using hh
    · change ∃a,towerHomotopyMap (nuCoefficientUnit H.unit D'.nu)
        (S_0_0:Syn) 0 (1,3) a=z
      refine ⟨z,?_⟩
      change _≫adamsTowerMap (nuCoefficientUnit H.unit D'.nu) (S_0_0:Syn) 0 0 _=_
      rw [adamsTowerMap_self]
      exact Category.comp_id _
  have eta_first_quotient_injective (BHS : EInftyComparison D')
      (V : SphereVanishingLine H) (h23 : Subsingleton (E2 H SphereSpectrum 2 3)) :
      Function.Injective (fun z : BiHom 1 2 (S_0_0:Syn) => quotientClass 1 z) := by
    intro x y h
    have hz : quotientClass 1 (x-y)=0 := by
      simp only [quotientClass,Preadditive.sub_comp] at h ⊢
      rw [h,sub_self]
    obtain ⟨b,hb⟩ := lambda_one_division_of_quotient_zero 1 3 (x-y) hz
    rw [sphere_one_three_zero BHS V h23 b] at hb
    simp only [lambdaMultiply,comp_zero] at hb
    exact sub_eq_zero.mp hb.symm
  have eta_unique_from_low_degrees (BHS : EInftyComparison D')
      (V:SphereVanishingLine H)
      (eta_nonzero_unique : ∀ x y : E2 H SphereSpectrum 1 2, x ≠ 0 → y ≠ 0 → x = y)
      (h23 : Subsingleton (E2 H SphereSpectrum 2 3)) :
      ∀x y:BiHom 1 2 (S_0_0:Syn),x≠0→y≠0→x=y := by
    have hi:=eta_first_quotient_injective BHS V h23
    let f:=fun z:BiHom 1 2 (S_0_0:Syn)=>D'.sphereFirstQuotient 1 2 (quotientClass 1 z)
    have hf:Function.Injective f:=(D'.sphereFirstQuotient 1 2).injective.comp hi
    intro x y hx hy
    have hn (z:BiHom 1 2 (S_0_0:Syn)) (hz:z≠0) : f z≠0 := by
      intro hh
      apply hz
      apply hf
      simpa only [f,quotientClass,zero_comp,map_zero] using hh
    apply hf
    exact eta_nonzero_unique _ _ (hn x hx) (hn y hy)
  have two_shuffle
      {X Y W : Syn} (f : X ⟶ Y) (b : Y ⟶ W)
      (hf : f+f=0) (hb : b+b=0)
      (z : X⟦(1:ℤ)⟧ ⟶ W) (v : X⟦(1:ℤ)⟧ ⟶ Y)
      (hz : Relation z f (2 • 𝟙 Y) b)
      (hv : Relation v (2 • 𝟙 X) f (2 • 𝟙 Y)) :
      z+z = -(v ≫ b) := by
    have h2b : (2 • 𝟙 Y) ≫ b = 0 := by
      simpa [two_smul,Preadditive.add_comp,Category.id_comp] using hb
    obtain ⟨z',hz',he⟩ := juggling hv h2b
    obtain ⟨a,c,hac⟩ := indeterminacy_complete hz hz'
    have hdouble : (z-z')+(z-z')=0 := by
      rw [hac,add_add_add_comm,←Preadditive.add_comp,←Preadditive.comp_add]
      have hfshift : f⟦(1:ℤ)⟧'+f⟦(1:ℤ)⟧'=0 := by
        rw [←Functor.map_add,hf,Functor.map_zero]
      rw [hfshift,hb,zero_comp,comp_zero,add_zero]
    have hh : z+z=z'+z' := by
      have : z+z-(z'+z')=0 := by
        calc
          _ = (z-z')+(z-z') := by abel
          _ = 0 := hdouble
      exact sub_eq_zero.mp this
    rw [hh]
    simpa [two_smul,Functor.map_add,Functor.map_id,Preadditive.neg_comp,
      Preadditive.add_comp,Category.id_comp,neg_neg] using (congrArg Neg.neg he).symm
  have middle_two_normalized (coh : BiShiftCoherence Syn) :
      (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (62,70)).map syntheticTwo =
        2 • 𝟙 ((SyntheticCategory.biShift (62,70)).obj (S_0_0 : Syn)) := by
    have hu := coh.left_unit (62,70) (S_0_0 : Syn)
    change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _ = _ at hu
    have hu' : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0 : Syn) =
        (SyntheticCategory.biShift (62,70)).map (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,
        eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id, Smn] using hu
    dsimp only [syntheticTwo]
    simp only [two_smul,Functor.map_add,
      Preadditive.comp_add,Category.comp_id]
    rw [←hu']
    simp
  have theta_two_normalized (coh : BiShiftCoherence Syn)
      (theta : BiHom 62 64 (S_0_0 : Syn)) (b : BiHom 62 70 (S_0_0 : Syn))
      (z : BiHom 125 134 (S_0_0 : Syn))
      (hz : TripleToda theta syntheticTwo b z) :
      Toda.Relation ((tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70).inv ≫ z)
        ((SyntheticCategory.biShift (62,70)).map theta)
        (2 • 𝟙 (Smn (Syn:=Syn) 62 70)) b := by
    change Toda.Relation _ _ _ b at hz
    rw [middle_two_normalized coh] at hz
    exact hz
  have two_theta_two_normalized (coh : BiShiftCoherence Syn)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (v : BiHom 63 64 (S_0_0 : Syn))
      (hv : TripleToda syntheticTwo theta syntheticTwo v) :
      Toda.Relation
        (((SyntheticCategory.biShift (62,64)).map
          (SyntheticCategory.biShift_zero.inv.app (S_0_0 : Syn)))⟦(1:ℤ)⟧' ≫
          (tripleTodaSource (Syn:=Syn) 0 0 62 64 0 0).inv ≫ v)
        (2 • 𝟙 (Smn (Syn:=Syn) 62 64)) theta (2 • 𝟙 (S_0_0 : Syn)) := by
    have hr := coh.right_unit (62,64) (S_0_0 : Syn)
    change (biShiftAddIso (62,64) (0,0) (62,64) (by decide)).hom.app _ = _ at hr
    have hr' : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn) =
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=Syn) 62 64) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,
        eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hr
    have hg : (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,0)).map theta ≫
        SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn) = theta := by
      rw [SyntheticCategory.biShift_zero.hom.naturality theta]
      dsimp only [Functor.id_map]
      rw [←hr']
      simp
    change Toda.Relation _ _ _ _ at hv
    have hn := Toda.precompose hv ((SyntheticCategory.biShift (62,64)).map
      (SyntheticCategory.biShift_zero.inv.app (S_0_0 : Syn)))
    have hf : (SyntheticCategory.biShift (62,64)).map
        (SyntheticCategory.biShift_zero.inv.app (S_0_0 : Syn)) ≫
        (SyntheticCategory.biShift (62+0,64+0)).map syntheticTwo =
          2 • 𝟙 (Smn (Syn:=Syn) 62 64) := by
      simp [syntheticTwo,←Functor.map_comp,two_smul,Smn]
    rw [hf] at hn
    unfold syntheticTwo at hn
    have hh := Toda.absorb_last hn
    simpa only [hg,Category.assoc,add_zero,Smn,Functor.id_obj] using hh
  have shifted_two_toda_shuffle
      (coh : BiShiftCoherence Syn)
      [IsTriangulated Syn]
      [(SyntheticCategory.biShift (Syn:=Syn) (62,70)).CommShift ℤ]
      [(SyntheticCategory.biShift (Syn:=Syn) (62,70)).IsTriangulated]
      (theta : BiHom 62 64 (S_0_0 : Syn)) (b : BiHom 62 70 (S_0_0 : Syn))
      (htheta : theta+theta=0) (hb : b+b=0)
      (z : BiHom 125 134 (S_0_0 : Syn)) (v : BiHom 63 64 (S_0_0 : Syn))
      (hz : TripleToda theta syntheticTwo b z)
      (hv : TripleToda syntheticTwo theta syntheticTwo v) :
      let F := SyntheticCategory.biShift (Syn:=Syn) (62,70)
      let src := (tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70).inv
      let srcv := ((SyntheticCategory.biShift (62,64)).map
        (SyntheticCategory.biShift_zero.inv.app (S_0_0 : Syn)))⟦(1:ℤ)⟧' ≫
        (tripleTodaSource (Syn:=Syn) 0 0 62 64 0 0).inv
      src ≫ z + src ≫ z =
        -((F.commShiftIso (1:ℤ)).inv.app (Smn 62 64) ≫ F.map (srcv ≫ v) ≫ b) := by
    dsimp only
    let F := SyntheticCategory.biShift (Syn:=Syn) (62,70)
    have ht := theta_two_normalized coh theta b z hz
    have hs := two_theta_two_normalized coh theta v hv
    have hmap := Toda.map F hs
    have hf : F.map theta+F.map theta=0 := by
      rw [←Functor.map_add,htheta,Functor.map_zero]
    have hmap' : Toda.Relation
        ((F.commShiftIso (1:ℤ)).inv.app (Smn 62 64) ≫ F.map
          (((SyntheticCategory.biShift (62,64)).map
            (SyntheticCategory.biShift_zero.inv.app (S_0_0 : Syn)))⟦(1:ℤ)⟧' ≫
            (tripleTodaSource (Syn:=Syn) 0 0 62 64 0 0).inv ≫ v))
        (2 • 𝟙 (F.obj (Smn 62 64))) (F.map theta) (2 • 𝟙 (Smn (Syn:=Syn) 62 70)) := by
      simpa [two_smul,Smn] using hmap
    simpa only [Category.assoc] using
      two_shuffle (F.map theta) b hf hb _ _ ht hmap'
  have source_iso_fixed_transport
      {A B U X:Syn} (F:Syn⥤Syn) (ff:F.FullyFaithful)
      (f:A⟶B) (hf:∀a:A≅A,a.hom≫f=f) (d:U≅F.obj A) (x:F.obj B⟶X)
      (a:U≅U) : a.hom≫d.hom≫F.map f≫x=d.hom≫F.map f≫x := by
    let b:=ff.preimageIso (d.symm≪≫a≪≫d)
    have hb:F.map b.hom=d.inv≫a.hom≫d.hom := ff.map_preimage _
    have hh:=congrArg F.map (hf b)
    rw [Functor.map_comp,hb] at hh
    have hh':=congrArg (fun z => d.hom≫z≫x) hh
    simpa only [Category.assoc,d.hom_inv_id_assoc] using hh'
  have source_iso_fixed_action
      {m n k l:ℤ} {X:Syn} (f:BiHom m n (S_0_0:Syn))
      (hf:∀a:Smn (Syn:=Syn) m n≅Smn m n,a.hom≫f=f)
      (x:BiHom k l X) (a:Smn (Syn:=Syn) (m+k) (n+l)≅Smn (m+k) (n+l)) :
      a.hom≫sphereAction f x=sphereAction f x := by
    exact source_iso_fixed_transport (SyntheticCategory.biShift (k,l))
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (k,l)) f hf
      ((SyntheticCategory.biShift_comp (m,n) (k,l)).app (S_0_0:Syn)).symm x a
  have source_iso_fixed_lambda
      {m n:ℤ} {X:Syn} (k:ℕ) (f:BiHom m n X)
      (hf:∀a:Smn (Syn:=Syn) m n≅Smn m n,a.hom≫f=f)
      (a:Smn (Syn:=Syn) m (n-k)≅Smn m (n-k)) :
      a.hom≫lambdaMultiply k f=lambdaMultiply k f := by
    let F:=SyntheticCategory.biShift (Syn:=Syn) (0,-(k:ℤ))
    let d:Smn (Syn:=Syn) m (n-k)≅F.obj (Smn m n) :=
      eqToIso (by congr 1; simp) ≪≫
        ((SyntheticCategory.biShift_comp (m,n) (0,-(k:ℤ))).app (S_0_0:Syn)).symm
    have he:lambdaMultiply k f=d.hom≫F.map f≫lambdaPow k X := by
      dsimp only [lambdaMultiply,d,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,eqToIso.hom]
      rw [lambdaPow_naturality]
      simp only [Category.assoc]
    rw [he]
    exact source_iso_fixed_transport F
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(k:ℤ))) f hf d (lambdaPow k X) a
  have eta_source_iso_fixed
      (unique : ∀ x y : BiHom 1 2 (S_0_0:Syn), x≠0 → y≠0 → x=y)
      (eta:BiHom 1 2 (S_0_0:Syn)) (a:Smn (Syn:=Syn) 1 2≅Smn 1 2) :
      a.hom≫eta=eta := by
    by_cases he:eta=0
    · simp [he]
    apply unique _ _ ?_ he
    intro hh
    apply he
    have h:=congrArg (fun z => a.inv≫z) hh
    simpa only [←Category.assoc,a.inv_hom_id,Category.id_comp,comp_zero] using h
  have theta_b_shuffle_double
      (coh : BiShiftCoherence Syn) [IsTriangulated Syn]
      [(SyntheticCategory.biShift (Syn:=Syn) (62,70)).CommShift ℤ]
      [(SyntheticCategory.biShift (Syn:=Syn) (62,70)).IsTriangulated]
      (unique : ∀ x y : BiHom 1 2 (S_0_0:Syn), x≠0 → y≠0 → x=y)
      (eta:BiHom 1 2 (S_0_0:Syn))
      (theta : BiHom 62 64 (S_0_0 : Syn)) (b : BiHom 62 70 (S_0_0 : Syn))
      (htheta : theta+theta=0) (hb : b+b=0)
      (z : BiHom 125 134 (S_0_0 : Syn))
      (hz : TripleToda theta syntheticTwo b z)
      (hv : TripleToda syntheticTwo theta syntheticTwo (lambdaMultiply 2 (sphereProduct eta theta))) :
      z+z=sphereProduct (lambdaMultiply 2 (sphereProduct eta theta)) b := by
    let F:=SyntheticCategory.biShift (Syn:=Syn) (62,70)
    let v:BiHom 63 64 (S_0_0:Syn):=lambdaMultiply 2 (sphereProduct eta theta)
    have hs:=shifted_two_toda_shuffle coh theta b htheta hb z v hz hv
    let sv:((Smn (Syn:=Syn) 62 64)⟦(1:ℤ)⟧)≅Smn 63 64 :=
      (shiftFunctor Syn (1:ℤ)).mapIso
        ((SyntheticCategory.biShift (62,64)).mapIso (SyntheticCategory.biShift_zero.app (S_0_0:Syn)).symm) ≪≫
        (tripleTodaSource (Syn:=Syn) 0 0 62 64 0 0).symm
    let src:=tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70
    let c:F.obj (Smn (Syn:=Syn) 63 64)≅Smn 125 134 :=
      (SyntheticCategory.biShift_comp (63,64) (62,70)).app (S_0_0:Syn)
    let a:Smn (Syn:=Syn) 125 134≅Smn 125 134 :=
      src≪≫((F.commShiftIso (1:ℤ)).app (Smn 62 64)).symm≪≫F.mapIso sv≪≫c
    have he:z+z=-(a.hom≫sphereProduct v b) := by
      have hh:=congrArg (fun t => src.hom≫t) hs
      change src.hom≫(src.inv≫z+src.inv≫z)=
        src.hom ≫ (-(((F.commShiftIso (1:ℤ)).app (Smn 62 64)).inv≫F.map (sv.hom≫v)≫b)) at hh
      simp only [Preadditive.comp_add,src.hom_inv_id_assoc,Preadditive.comp_neg,
        Functor.map_comp,Category.assoc] at hh
      change z+z=-((src.hom≫((F.commShiftIso (1:ℤ)).app (Smn 62 64)).inv≫F.map sv.hom≫c.hom)≫
        c.inv≫F.map v≫b)
      simpa only [Category.assoc,c.hom_inv_id_assoc] using hh
    have hvfix:∀aa:Smn (Syn:=Syn) 63 64≅Smn 63 64,aa.hom≫v=v := by
      intro aa
      exact source_iso_fixed_lambda 2 (sphereProduct eta theta)
        (source_iso_fixed_action eta (eta_source_iso_fixed unique eta) theta) aa
    have hp:a.hom≫sphereProduct v b=sphereProduct v b :=
      source_iso_fixed_action v hvfix b a
    rw [hp] at he
    have ht:sphereProduct v b+sphereProduct v b=0 := by
      dsimp only [sphereProduct]
      simp only [←Preadditive.comp_add,hb,comp_zero]
    have hn:-(sphereProduct v b)=sphereProduct v b := neg_eq_of_add_eq_zero_right ht
    exact he.trans hn
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have shiftSwap_add (coh : BiShiftCoherence Syn)
      (a b c : ℤ × ℤ) (A : Syn) :
      (shiftSwap a (b+c) A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
      (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    let habc : (a+b)+c=a+(b+c) := add_assoc a b c
    let hbac : b+(a+c)=a+(b+c) := by abel
    have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
    have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
      (add_comm _ _) rfl habc hbac A
    have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
      rfl (add_comm _ _) (add_comm _ _) hbac A
    simp only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
    rw [Functor.map_comp]
    apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
      ((SyntheticCategory.biShift a).obj A))).mp
    simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc,← h₁]
    simp only [Category.assoc]
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
    -- Cancel the common left factor introduced by the first associativity square.
    apply (cancel_epi ((SyntheticCategory.biShift c).map
      ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
    rw [← Category.assoc,h₂]
    simp only [Category.assoc]
    apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
      ((SyntheticCategory.biShift b).obj A))).mpr
    apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
      ((SyntheticCategory.biShift b).obj A))).mp
    rw [← Category.assoc,← Category.assoc,← h₃]
    simp only [Category.assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
    rfl
  have shiftSwap_add_eq (coh : BiShiftCoherence Syn)
      (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
      (shiftSwap a d A).hom ≫
        (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
      (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift c).map (shiftSwap a b A).hom ≫
        (shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
    subst d
    exact shiftSwap_add coh a b c A
  have shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
        (shiftSwap a b B).hom =
      (shiftSwap a b A).hom ≫
        (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
    exact ((biShiftAddIso a b (a+b) rfl) ≪≫
      (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f
  have shiftSwap_hom_eq (a b d : ℤ × ℤ)
      (hab : a+b=d) (hba : b+a=d) (A : Syn) :
      (shiftSwap a b A).hom =
        (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
    subst d
    rfl
  have lambda_pow_shift (coh : BiShiftCoherence Syn)
      (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
      lambdaPow n ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow n A) := by
    induction n generalizing A with
    | zero =>
      change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (shiftSwap a 0 A).hom ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
      have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
          (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
            (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
              (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
        rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
        exact (coh.right_unit a A).symm
      rw [shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
      exact h
    | succ n ih =>
      have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
            (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
        rw [lambdaPow_one coh,lambdaPow_one coh]
        change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
          (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
        rw [shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
        exact coh.lambda_comm a A
      have hn := shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
      have hh := shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
        (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
      change (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
          (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
        (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
          (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
      rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
        lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
      simp only [Functor.map_comp,Category.assoc]
      rw [reassoc_of% hn]
      rw [reassoc_of% hh]
      rfl
  have shift_assoc_inv (coh : BiShiftCoherence Syn)
      (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
      (biShiftAddIso ab c total habc).inv.app A ≫
        (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
      (biShiftAddIso a bc total habc').inv.app A ≫
        (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
    have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
        (biShiftAddIso ab c total habc).app A) =
      ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
        (biShiftAddIso a bc total habc').app A) :=
      Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
    have hi := congrArg Iso.inv he
    exact hi
  have shuffle_lambda_left_two (D' : AdamsComparison H M' Syn)
      (etaShuffle : BiHom 63 66 (S_0_0 : Syn))
      (a : BiHom 62 70 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 2 etaShuffle) a = lambdaMultiply 2 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv D'.shiftCoherence (63,66) (62,70) (0,-2)
      (125,136) (62,68) (125,134) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv D'.shiftCoherence (63,66) (0,-2) (62,70)
      (63,64) (62,68) (125,134) (by decide) (by decide) (by decide) (by decide) S
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at h₁ h₂
    have hp :
      (SyntheticCategory.biShift_comp (125,136) (0,-2)).inv.app S ≫
        lambdaPow 2 (Smn 125 136) ≫
        (SyntheticCategory.biShift_comp (63,66) (62,70)).inv.app S =
      (SyntheticCategory.biShift_comp (63,64) (62,70)).inv.app S ≫
        (SyntheticCategory.biShift (62,70)).map
          ((SyntheticCategory.biShift_comp (63,66) (0,-2)).inv.app S) ≫
        (SyntheticCategory.biShift (62,70)).map (lambdaPow 2 (Smn 63 66)) := by
      rw [←lambdaPow_naturality]
      change (SyntheticCategory.biShift_comp (125,136) (0,-2)).inv.app S ≫
        (SyntheticCategory.biShift (0,-2)).map ((SyntheticCategory.biShift_comp (63,66) (62,70)).inv.app S) ≫
        lambdaPow 2 ((SyntheticCategory.biShift (62,70)).obj (Smn 63 66)) = _
      rw [lambda_pow_shift D'.shiftCoherence 2 (62,70) (Smn 63 66)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (125,136) (0,-2)).inv.app S)]
      erw [h₁]
      simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,70)).map (lambdaPow 2 (Smn 63 66))) h₂.symm)
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (62,70)).map etaShuffle ≫ a) hp).symm
  have shuffle_lambda_h0_left_one (D' : AdamsComparison H M' Syn)
      (etaShuffle : BiHom 0 1 (S_0_0 : Syn))
      (a : BiHom 125 134 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 1 etaShuffle) a = lambdaMultiply 1 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv D'.shiftCoherence (0,1) (125,134) (0,-1)
      (125,135) (125,133) (125,134) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv D'.shiftCoherence (0,1) (0,-1) (125,134)
      (0,0) (125,133) (125,134) (by decide) (by decide) (by decide) (by decide) S
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at h₁ h₂
    have hp :
      (SyntheticCategory.biShift_comp (125,135) (0,-1)).inv.app S ≫
        lambdaPow 1 (Smn 125 135) ≫
        (SyntheticCategory.biShift_comp (0,1) (125,134)).inv.app S =
      (SyntheticCategory.biShift_comp (0,0) (125,134)).inv.app S ≫
        (SyntheticCategory.biShift (125,134)).map
          ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S) ≫
        (SyntheticCategory.biShift (125,134)).map (lambdaPow 1 (Smn 0 1)) := by
      rw [←lambdaPow_naturality]
      change (SyntheticCategory.biShift_comp (125,135) (0,-1)).inv.app S ≫
        (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift_comp (0,1) (125,134)).inv.app S) ≫
        lambdaPow 1 ((SyntheticCategory.biShift (125,134)).obj (Smn 0 1)) = _
      rw [lambda_pow_shift D'.shiftCoherence 1 (125,134) (Smn 0 1)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (125,135) (0,-1)).inv.app S)]
      erw [h₁]
      simp only [Category.assoc,Smn,S,Int.natCast_one,Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (125,134)).map (lambdaPow 1 (Smn 0 1))) h₂.symm)
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (125,134)).map etaShuffle ≫ a) hp).symm
  have shuffle_lambda_one_one (D' : AdamsComparison H M' Syn)
      (c : BiHom 125 135 (S_0_0 : Syn)) :
      lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,135) (0,-1) (0,-1)
      (125,134) (0,-2) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,Int.natCast_one, Int.reduceSub]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (125,135) (0,-1)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 135)))]
    erw [← Category.assoc, ha]
    erw [lambdaPow_add D'.shiftCoherence 1 1 2 (by decide) (Smn 125 135)]
    simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.assoc]
    rfl
  have shuffle_lambda_one_two (D' : AdamsComparison H M' Syn)
      (c : BiHom 125 136 (S_0_0 : Syn)) :
      lambdaMultiply 1 (lambdaMultiply 2 c) = lambdaMultiply 3 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,136) (0,-2) (0,-1)
      (125,134) (0,-3) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,Int.natCast_one, Int.reduceSub]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (125,136) (0,-2)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 2 (Smn 125 136)))]
    erw [← Category.assoc, ha]
    erw [lambdaPow_add D'.shiftCoherence 2 1 3 (by decide) (Smn 125 136)]
    simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.assoc]
    rfl
  have shuffle_action_associativity (D' : AdamsComparison H M' Syn)
   (eta:BiHom 1 2 (S_0_0:Syn)) (theta:BiHom 62 64 (S_0_0:Syn))
   (b:BiHom 62 70 (S_0_0:Syn)) :
   sphereAction (sphereAction eta theta) b=sphereAction eta (sphereAction theta b) := by
    have ha := shift_assoc_inv D'.shiftCoherence (1,2) (62,64) (62,70)
      (63,66) (124,134) (125,136) (by decide) (by decide) (by decide) (by decide) (S_0_0:Syn)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at ha
    dsimp only [sphereAction]
    simp only [Functor.map_comp,Category.assoc,Int.reduceAdd]
    erw [reassoc_of% ha]
    erw [←reassoc_of% ((SyntheticCategory.biShift_comp (62,64) (62,70)).inv.naturality eta)]
    rfl
  have shuffle_two_normalized (coh : BiShiftCoherence Syn) :
      (SyntheticCategory.biShift_comp (0,0) (125,134)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (125,134)).map syntheticTwo =
        2 • 𝟙 ((SyntheticCategory.biShift (125,134)).obj (S_0_0 : Syn)) := by
    have hu := coh.left_unit (125,134) (S_0_0 : Syn)
    change (biShiftAddIso (0,0) (125,134) (125,134) (by decide)).hom.app _ = _ at hu
    have hu' : (SyntheticCategory.biShift_comp (0,0) (125,134)).hom.app (S_0_0 : Syn) =
        (SyntheticCategory.biShift (125,134)).map (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,
        eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id, Smn] using hu
    dsimp only [syntheticTwo]
    simp only [two_smul,Functor.map_add,
      Preadditive.comp_add,Category.comp_id]
    rw [←hu']
    simp
  letI:=D'.syntheticTriangulated
  letI:=D'.shiftCommShift (62,70)
  letI:=D'.shiftExact (62,70)
  have huq:=eta_unique_from_low_degrees BHS V eta_nonzero_unique h23
  have hd:=theta_b_shuffle_double D'.shiftCoherence huq eta theta b htheta hb z hz hv
  have ht:sphereAction syntheticTwo z=z+z := by
    dsimp only [sphereAction]
    erw [reassoc_of% (shuffle_two_normalized D'.shiftCoherence)]
    simp [two_smul,Preadditive.add_comp]
  change lambdaMultiply 2 (sphereAction h0 z)=lambdaMultiply 3 (sphereAction eta (sphereAction theta b))
  calc
    _ = lambdaMultiply 1 (lambdaMultiply 1 (sphereAction h0 z)) := (shuffle_lambda_one_one D' _).symm
    _ = lambdaMultiply 1 (sphereAction (lambdaMultiply 1 h0) z) := by rw [shuffle_lambda_h0_left_one D']
    _ = lambdaMultiply 1 (z+z) := by rw [hlambda,ht]
    _ = lambdaMultiply 1 (sphereAction (lambdaMultiply 2 (sphereAction eta theta)) b) := congrArg (lambdaMultiply 1) hd
    _ = lambdaMultiply 1 (lambdaMultiply 2 (sphereAction (sphereAction eta theta) b)) := by rw [shuffle_lambda_left_two D']
    _ = lambdaMultiply 3 (sphereAction (sphereAction eta theta) b) := shuffle_lambda_one_two D' _
    _ = _ := by rw [shuffle_action_associativity D']

end
end ThetaBShuffleProof

/-- The precise multiplied shuffle in `lem:toda2ext`. The premise is
actual Toda membership, so no selected value replaces the original set.
The two multiplied-indeterminacy statements above are internal proof
dependencies, rather than new assumptions of this theorem. -/
theorem theta_b_multiplied_shuffle
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice M (D).toAdamsComparisonData theta)
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (hz : TripleToda theta syntheticTwo b z) :
    lambdaMultiply 2 (sphereProduct h₀ z) =
      lambdaMultiply 3 (sphereProduct η (sphereProduct theta b)) := by
  have horder := KIP126.Computation.SphereAndCofiber.theta5_choice_order_two literatureTheorems I theta htheta
  exact theta_b_shuffle_from_low_degrees D literatureTheorems.synthetic.eInfty sphereVanishing
    (KIP126.Computation.LinCoordinates.sphere_eta_nonzero_unique KIP126.Main.externalHypotheses)
    (KIP126.Computation.LinCoordinates.sphere_e2_two_three_subsingleton KIP126.Main.externalHypotheses)
    h₀ η literatureTheorems.toda.lambda_h0
    theta b horder
    (KIP126.Computation.SphereAndCofiber.two_torsion_62_70 literatureTheorems I sphereVanishing b)
    z hz (literatureTheorems.toda.symmetric_two theta horder)

end
end KIP126.Main.SectionSeven
