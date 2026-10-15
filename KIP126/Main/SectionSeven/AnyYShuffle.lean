module
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.Internal.LowEta
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! Toda shuffle and complete indeterminacy argument, AnyYHelpers:1675–2042
at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.StableHomotopy.Toda
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [IsTriangulated C]
set_option backward.isDefEq.respectTransparency false

theorem y_detection_toda_juggling_every_member
    {X Y Z W V:C} {f:X⟶Y} {g:Y⟶Z} {h:Z⟶W} {d:W⟶V}
    {x:X⟦(1:ℤ)⟧⟶W} (hx:Relation x f g h)
    (hhd:h≫d=0)
    (hind:∀u:Y⟦(1:ℤ)⟧⟶W,f⟦(1:ℤ)⟧'≫u=0)
    {y:Y⟦(1:ℤ)⟧⟶V} (hy:Relation y g h d) :
    x≫d=(-f⟦(1:ℤ)⟧')≫y := by
  obtain ⟨x',hx',he⟩ := (shuffle_iff f g h d (composable hx).1
    (composable hx).2 hhd ((-f⟦(1:ℤ)⟧')≫y)).mpr ⟨y,hy,rfl⟩
  obtain ⟨u,v,huv⟩:=(relation_iff_indeterminacy hx').mp hx
  have hh:=congrArg (fun a => a≫d) huv
  simp only [Preadditive.sub_comp,Preadditive.add_comp,Category.assoc,hhd,
    comp_zero,hind u,zero_comp,add_zero] at hh
  exact (sub_eq_zero.mp hh).trans he

end KIP126.StableHomotopy.Toda

namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Literature.Route KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private theorem y_detection_toda_shifted_h0_low_indeterminacy
    (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hind:∀a:BiHom 2 3 (S_0_0:SyntheticSpectrum),sphereProduct h0 a=0)
    (u:((SyntheticCategory.biShift (1,3)).obj (S_0_0:SyntheticSpectrum))⟦(1:ℤ)⟧⟶(S_0_0:SyntheticSpectrum)) :
    ((SyntheticCategory.biShift (1,3)).map h0)⟦(1:ℤ)⟧'≫u=0 := by
  let G:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,3)
  let K:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (2,3)
  let j:G⋙shiftFunctor SyntheticSpectrum (1:ℤ)≅K :=
    Functor.isoWhiskerLeft G (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm ≪≫
      SyntheticCategory.biShift_comp (1,3) (1,0)
  let a:BiHom 2 3 (S_0_0:SyntheticSpectrum):=j.inv.app (S_0_0:SyntheticSpectrum)≫u
  have hz:K.map h0≫a=0 := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (0,1) (2,3)).inv.app (S_0_0:SyntheticSpectrum))).mp
    simpa only [sphereProduct,comp_zero] using hind a
  have hn:=j.hom.naturality h0
  have hh:=congrArg (fun k => k≫a) hn
  dsimp only [Functor.comp_map] at hh
  have hu:j.hom.app (S_0_0:SyntheticSpectrum)≫a=u := by
    dsimp only [a]
    simp only [j.hom_inv_id_app_assoc]
  rw [Category.assoc,hu,Category.assoc,hz,comp_zero] at hh
  exact hh

private theorem y_detection_toda_map_left_indeterminacy
    (F:SyntheticSpectrum⥤SyntheticSpectrum) [F.CommShift ℤ] [F.Additive] (ff:F.FullyFaithful)
    {A B W:SyntheticSpectrum} (f:A⟶B)
    (hind:∀u:B⟦(1:ℤ)⟧⟶W,f⟦(1:ℤ)⟧'≫u=0)
    (u:(F.obj B)⟦(1:ℤ)⟧⟶F.obj W) :
    (F.map f)⟦(1:ℤ)⟧'≫u=0 := by
  let j:=F.commShiftIso (1:ℤ)
  let u0:B⟦(1:ℤ)⟧⟶W:=ff.preimage (j.hom.app B≫u)
  have hu:F.map u0=j.hom.app B≫u:=ff.map_preimage _
  have hh:=congrArg F.map (hind u0)
  simp only [Functor.map_comp,Functor.map_zero] at hh
  rw [hu] at hh
  have hn:=j.inv.naturality f
  have hnu:=congrArg (fun a => a≫j.hom.app B≫u) hn
  simp only [Functor.comp_map,Category.assoc,j.inv_hom_id_app_assoc] at hnu
  rw [hh,comp_zero] at hnu
  exact hnu

private theorem y_detection_toda_module_low_shuffle_raw
    [IsTriangulated SyntheticSpectrum]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)).IsTriangulated]
    (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum)) (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:SyntheticSpectrum),sphereProduct h0 a=0)
    {X:SyntheticSpectrum} (a:BiHom 123 129 X) (ha:sphereAction h0 a=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda a h0 eta z) :
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
    let d:F.obj (Smn (Syn:=SyntheticSpectrum) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    ((F.commShiftIso (1:ℤ)).inv.app ((SyntheticCategory.biShift (1,3)).obj (Smn 0 1)) ≫
      F.map ((tripleTodaSource (Syn:=SyntheticSpectrum) 0 1 1 2 0 1).inv ≫ sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))≫a =
      (-(F.map ((SyntheticCategory.biShift (1,3)).map h0))⟦(1:ℤ)⟧')≫
        d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129).inv≫z := by
  dsimp only
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
  let d:F.obj (Smn (Syn:=SyntheticSpectrum) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
    F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
  let e: F.obj (Smn (Syn:=SyntheticSpectrum) 0 1)≅Smn 123 130 :=
    (SyntheticCategory.biShift_comp (0,1) (123,129)).app (S_0_0:SyntheticSpectrum)
  have hh:F.map h0≫a=0 := by
    apply (cancel_epi e.inv).mp
    simpa only [e,F,sphereAction,Category.assoc,comp_zero,Iso.app_inv,Int.reduceAdd] using ha
  have hmap:=Toda.map F hlow
  have hnorm:=Toda.precompose hz d.hom
  have hn:d.hom≫(SyntheticCategory.biShift (123,130)).map eta=
      F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift (0,1)).map eta)≫e.hom := by
    change (F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum)) ≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).hom.app (Smn 1 2)) ≫ _ = _
    simpa only [e,F,Functor.map_comp,Functor.comp_map,Category.assoc,Prod.mk_add_mk,Int.reduceAdd,
      Iso.app_hom] using
      congrArg (fun k => F.map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum))≫k)
        ((SyntheticCategory.biShift_comp (0,1) (123,129)).hom.naturality eta).symm
  change Toda.Relation _ (d.hom≫(SyntheticCategory.biShift (123,130)).map eta)
    (e.inv≫F.map h0) a at hnorm
  rw [hn] at hnorm
  have hn':=Toda.absorb_first hnorm
  simp only [e.hom_inv_id_assoc] at hn'
  have hi:∀u:(F.obj ((SyntheticCategory.biShift (1,3)).obj (S_0_0:SyntheticSpectrum)))⟦(1:ℤ)⟧⟶F.obj (S_0_0:SyntheticSpectrum),
      (F.map ((SyntheticCategory.biShift (1,3)).map h0))⟦(1:ℤ)⟧'≫u=0 := by
    intro u
    exact y_detection_toda_map_left_indeterminacy F (SyntheticCategory.biShift_fullyFaithful (123,129))
      _ (y_detection_toda_shifted_h0_low_indeterminacy h0 hind) u
  have hresult:=Toda.y_detection_toda_juggling_every_member hmap hh hi hn'
  simpa only [F,d,Category.assoc,homotopyRegrade,Int.reduceAdd,eqToHom_refl,Category.id_comp] using hresult

private theorem y_detection_toda_module_low_source_iso (coh:BiShiftCoherence SyntheticSpectrum) :
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
    let d:F.obj (Smn (Syn:=SyntheticSpectrum) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    d.hom=(SyntheticCategory.biShift_comp (1,3) (123,129)).hom.app (S_0_0:SyntheticSpectrum)≫
      (SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:SyntheticSpectrum) := by
  dsimp only
  have hh:=coh.associativity (1,2) (0,1) (123,129) (1,3) (123,130) (124,132)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hh
  have he:=congrArg (fun k =>
    (SyntheticCategory.biShift (123,129)).map ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0:SyntheticSpectrum))≫
      k≫(SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:SyntheticSpectrum)) hh
  simp only [←Category.assoc,←Functor.map_comp,Iso.inv_hom_id_app] at he
  simp only [Category.assoc,Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Smn,Functor.comp_obj,Prod.mk_add_mk,Int.reduceAdd,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,
    Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Iso.app_inv,Iso.app_hom] using he.symm

private theorem y_detection_toda_module_low_normalized_source (coh:BiShiftCoherence SyntheticSpectrum) :
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
    let G:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,3)
    let d:F.obj (Smn (Syn:=SyntheticSpectrum) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
      F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
    let J: (G⋙F)⋙shiftFunctor SyntheticSpectrum (1:ℤ)≅SyntheticCategory.biShift (125,132):=
      Functor.isoWhiskerLeft (G⋙F) (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm ≪≫
        Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,3) (123,129))
          (SyntheticCategory.biShift (1,0)) ≪≫
            SyntheticCategory.biShift_comp (124,132) (1,0)
    d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129).inv=J.hom.app (S_0_0:SyntheticSpectrum) := by
  dsimp only
  rw [y_detection_toda_module_low_source_iso coh]
  simp only [Functor.map_comp,Category.assoc]
  have hsrc : tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129 =
      ((SyntheticCategory.biShift_comp (124,132) (1,0)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
        (SyntheticCategory.biShift (1,0)).mapIso
          ((SyntheticCategory.biShift_comp (1,2) (123,130)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).app
          ((SyntheticCategory.biShift (123,130)).obj (Smn 1 2)) := by rfl
  rw [hsrc]
  simp only [Iso.trans_inv,Iso.symm_inv,Functor.mapIso_inv,Iso.app_inv,Iso.app_hom,
    Iso.symm_hom,Iso.trans_hom,NatTrans.comp_app,Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,Functor.whiskerLeft_app,Functor.whiskerRight_app,Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.naturality
    ((SyntheticCategory.biShift_comp (1,2) (123,130)).inv.app (S_0_0:SyntheticSpectrum)))]
  erw [((SyntheticCategory.biShift_comp (1,2) (123,130)).app (S_0_0:SyntheticSpectrum)).map_inv_hom_id_assoc
    (SyntheticCategory.biShift (1,0))]
  erw [reassoc_of% ((SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.naturality
    ((SyntheticCategory.biShift_comp (1,3) (123,129)).hom.app (S_0_0:SyntheticSpectrum)))]

private theorem y_detection_toda_source_iso_fixed_transport
    {A B U X:SyntheticSpectrum} (F:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
    (f:A⟶B) (hf:∀a:A≅A,a.hom≫f=f) (d:U≅F.obj A) (x:F.obj B⟶X)
    (a:U≅U) : a.hom≫d.hom≫F.map f≫x=d.hom≫F.map f≫x := by
  let b:=ff.preimageIso (d.symm≪≫a≪≫d)
  have hb:F.map b.hom=d.inv≫a.hom≫d.hom := ff.map_preimage _
  have hh:=congrArg F.map (hf b)
  rw [Functor.map_comp,hb] at hh
  have hh':=congrArg (fun z => d.hom≫z≫x) hh
  simpa only [Category.assoc,d.hom_inv_id_assoc] using hh'

private theorem y_detection_toda_source_iso_fixed_action
    {m n k l:ℤ} {X:SyntheticSpectrum} (f:BiHom m n (S_0_0:SyntheticSpectrum))
    (hf:∀a:Smn (Syn:=SyntheticSpectrum) m n≅Smn m n,a.hom≫f=f)
    (x:BiHom k l X) (a:Smn (Syn:=SyntheticSpectrum) (m+k) (n+l)≅Smn (m+k) (n+l)) :
    a.hom≫sphereAction f x=sphereAction f x := by
  exact y_detection_toda_source_iso_fixed_transport (SyntheticCategory.biShift (k,l))
    (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (k,l)) f hf
    ((SyntheticCategory.biShift_comp (m,n) (k,l)).app (S_0_0:SyntheticSpectrum)).symm x a

private theorem y_detection_toda_eta_source_iso_fixed
    (unique : ∀ x y : BiHom 1 2 (S_0_0:SyntheticSpectrum), x≠0 → y≠0 → x=y)
    (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum)) (a:Smn (Syn:=SyntheticSpectrum) 1 2≅Smn 1 2) :
    a.hom≫eta=eta := by
  by_cases he:eta=0
  · simp [he]
  apply unique _ _ ?_ he
  intro hh
  apply he
  have h:=congrArg (fun z => a.inv≫z) hh
  simpa only [←Category.assoc,a.inv_hom_id,Category.id_comp,comp_zero] using h

private theorem y_detection_toda_module_low_shuffle_exact
    (coh:BiShiftCoherence SyntheticSpectrum)
    [IsTriangulated SyntheticSpectrum]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)).IsTriangulated]
    (unique:∀x y:BiHom 1 2 (S_0_0:SyntheticSpectrum),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum)) (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:SyntheticSpectrum),sphereProduct h0 a=0)
    {X:SyntheticSpectrum} (a:BiHom 123 129 X) (ha:sphereAction h0 a=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda a h0 eta z) :
    sphereAction h0 z=sphereAction (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta) a := by
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (123,129)
  let G:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,3)
  let d:F.obj (Smn (Syn:=SyntheticSpectrum) 1 3)≅(SyntheticCategory.biShift (123,130)).obj (Smn 1 2):=
    F.mapIso ((SyntheticCategory.biShift_comp (1,2) (0,1)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      (SyntheticCategory.biShift_comp (0,1) (123,129)).app (Smn 1 2)
  let J: (G⋙F)⋙shiftFunctor SyntheticSpectrum (1:ℤ)≅SyntheticCategory.biShift (125,132):=
    Functor.isoWhiskerLeft (G⋙F) (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm ≪≫
      Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,3) (123,129))
        (SyntheticCategory.biShift (1,0)) ≪≫
          SyntheticCategory.biShift_comp (124,132) (1,0)
  let src: ((F.obj (G.obj (Smn (Syn:=SyntheticSpectrum) 0 1)))⟦(1:ℤ)⟧)≅Smn 125 133 :=
    J.app (Smn 0 1) ≪≫ (SyntheticCategory.biShift_comp (0,1) (125,132)).app (S_0_0:SyntheticSpectrum)
  let v:BiHom 2 4 (S_0_0:SyntheticSpectrum):=sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta
  have hs:=y_detection_toda_module_low_shuffle_raw eta h0 hlow hind a ha z hz
  have hn:(F.map (G.map h0))⟦(1:ℤ)⟧'≫d.hom⟦(1:ℤ)⟧'≫
      (tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129).inv≫z=src.hom≫sphereAction h0 z := by
    have he:=y_detection_toda_module_low_normalized_source coh
    change d.hom⟦(1:ℤ)⟧'≫(tripleTodaSource (Syn:=SyntheticSpectrum) 1 2 0 1 123 129).inv=J.hom.app (S_0_0:SyntheticSpectrum) at he
    erw [reassoc_of% he]
    have hh:=J.hom.naturality h0
    dsimp only [Functor.comp_map] at hh
    erw [←Category.assoc,hh]
    change _ = (J.hom.app (Smn 0 1)≫(SyntheticCategory.biShift_comp (0,1) (125,132)).hom.app (S_0_0:SyntheticSpectrum))≫
      (SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift (125,132)).map h0≫z
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
  have hs':
      (F.commShiftIso (1:ℤ)).inv.app (G.obj (Smn 0 1))≫
        F.map ((tripleTodaSource (Syn:=SyntheticSpectrum) 0 1 1 2 0 1).inv≫v)≫a =
      -(src.hom≫sphereAction h0 z) := by
    simpa only [F,G,d,v,Preadditive.neg_comp,Category.assoc,hn] using hs
  let au:Smn (Syn:=SyntheticSpectrum) 125 133≅Smn 125 133 :=
    src.symm ≪≫ ((F.commShiftIso (1:ℤ)).app (G.obj (Smn 0 1))).symm ≪≫
      F.mapIso (tripleTodaSource (Syn:=SyntheticSpectrum) 0 1 1 2 0 1).symm ≪≫
        (SyntheticCategory.biShift_comp (2,4) (123,129)).app (S_0_0:SyntheticSpectrum)
  have he:au.hom≫sphereAction v a=-(sphereAction h0 z) := by
    have hh:=congrArg (fun k => src.inv≫k) hs'
    simp only [Category.assoc,Preadditive.comp_neg,src.inv_hom_id_assoc,Functor.map_comp] at hh
    change (src.inv≫(F.commShiftIso (1:ℤ)).inv.app (G.obj (Smn 0 1))≫
      F.map ((tripleTodaSource (Syn:=SyntheticSpectrum) 0 1 1 2 0 1).inv)≫
      (SyntheticCategory.biShift_comp (2,4) (123,129)).hom.app (S_0_0:SyntheticSpectrum))≫
      (SyntheticCategory.biShift_comp (2,4) (123,129)).inv.app (S_0_0:SyntheticSpectrum)≫F.map v≫a = _
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    exact hh
  have hv:∀aa:Smn (Syn:=SyntheticSpectrum) 2 4≅Smn 2 4,aa.hom≫v=v := by
    intro aa
    exact y_detection_toda_source_iso_fixed_action eta (y_detection_toda_eta_source_iso_fixed unique eta) eta aa
  have hp:∀aa:Smn (Syn:=SyntheticSpectrum) 125 133≅Smn 125 133,
      aa.hom≫sphereAction v a=sphereAction v a := by
    intro aa
    exact y_detection_toda_source_iso_fixed_action v hv a aa
  rw [hp au] at he
  let negIso:Smn (Syn:=SyntheticSpectrum) 125 133≅Smn 125 133 :=
    ⟨-𝟙 _, -𝟙 _,by simp,by simp⟩
  have hneg:=hp negIso
  change (-𝟙 _)≫sphereAction v a=sphereAction v a at hneg
  simp only [Preadditive.neg_comp,Category.id_comp] at hneg
  exact ((congrArg Neg.neg he).trans (neg_neg _)).symm.trans hneg

private theorem y_detection_toda_h0_action_lambda_three     (η : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 123 132 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := shift_assoc_inv model.quotients.coherence (0,1) (123,132) (0,-3)
    (123,133) (123,129) (123,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (0,1) (123,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (123,132)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (123,132) (0,-3)).inv.naturality η)]
  rfl

private theorem y_detection_toda_eta_action_right_three     (η : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {X : SyntheticSpectrum} (c : BiHom 123 132 X) :
    sphereAction η (lambdaMultiply 3 c) = lambdaMultiply 3 (sphereAction η c) := by
  have ha := shift_assoc_inv model.quotients.coherence (1,2) (123,132) (0,-3)
    (124,134) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app (S_0_0 : SyntheticSpectrum)))]
  erw [← reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift (123,132)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (123,132) (0,-3)).inv.naturality η)]
  rfl


private theorem y_detection_toda_eta_double_action (coh:BiShiftCoherence SyntheticSpectrum)
    (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum)) {X:SyntheticSpectrum} (a:BiHom 123 129 X) :
    sphereAction (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta) a =
      sphereAction eta (sphereAction eta a) := by
  have ha:=shift_assoc_inv coh (1,2) (1,2) (123,129) (2,4) (124,131) (125,133)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at ha
  dsimp only [sphereProduct,sphereAction]
  simp only [Functor.map_comp,Category.assoc,Int.reduceAdd]
  erw [reassoc_of% ha]
  erw [←reassoc_of% ((SyntheticCategory.biShift_comp (1,2) (123,129)).inv.naturality eta)]
  rfl

private theorem y_detection_toda_main_toda_h0_relation     (unique:∀x y:BiHom 1 2 (S_0_0:SyntheticSpectrum),x≠0→y≠0→x=y)
    (eta:BiHom 1 2 (S_0_0:SyntheticSpectrum)) (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (hlow:TripleToda h0 eta h0 (sphereProduct (m:=1) (n:=2) (k:=1) (l:=2) eta eta))
    (hind:∀a:BiHom 2 3 (S_0_0:SyntheticSpectrum),sphereProduct h0 a=0)
    {X:SyntheticSpectrum} (a:BiHom 123 132 X) (ha:lambdaMultiply 3 (sphereAction h0 a)=0)
    (z:BiHom 125 132 X) (hz:ModuleTripleToda (lambdaMultiply 3 a) h0 eta z) :
    sphereAction h0 z=sphereAction eta (lambdaMultiply 3 (sphereAction eta a)) := by
  letI:=model.exactness.syntheticTriangulated
  letI:=model.exactness.shiftCommShift (123,129)
  letI:=model.exactness.shiftExact (123,129)
  have hh:sphereAction h0 (lambdaMultiply 3 a)=0 := (y_detection_toda_h0_action_lambda_three h0 a).trans ha
  have he:=y_detection_toda_module_low_shuffle_exact model.quotients.coherence unique eta h0 hlow hind (lambdaMultiply 3 a) hh z hz
  rw [y_detection_toda_eta_double_action model.quotients.coherence,y_detection_toda_eta_action_right_three] at he
  exact he

end
end KIP126.Main.SectionSeven.Internal
