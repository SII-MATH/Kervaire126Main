module
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

private def verticalCancellationIso (e : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e) ⋙
      SyntheticCategory.biShift (0,-e) ≅ 𝟭 SyntheticSpectrum :=
  biShiftAddIso (0,e) (0,-e) (0,0) (by ext <;> simp) ≪≫ SyntheticCategory.biShift_zero

private def exactSuspensionTransport (e : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ⋙ SyntheticCategory.biShift (0,-e) ≅
      SyntheticCategory.biShift (1,0) := by
  letI := model.exactness.shiftCommShift (0,-e)
  exact Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,e))
      ((SyntheticCategory.biShift (0,-e)).commShiftIso (1:ℤ)) ≪≫
    Functor.isoWhiskerRight (verticalCancellationIso e) (shiftFunctor SyntheticSpectrum (1:ℤ)) ≪≫
    Functor.leftUnitor _ ≪≫ (SyntheticCategory.biShift_compat 1).symm

private def canonicalSuspensionComm (e : ℤ) :
    shiftFunctor SyntheticSpectrum (1:ℤ) ⋙ SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-e) ≅
      SyntheticCategory.biShift (0,-e) ⋙ shiftFunctor SyntheticSpectrum (1:ℤ) :=
  Functor.isoWhiskerRight (SyntheticCategory.biShift_compat 1).symm
      (SyntheticCategory.biShift (0,-e)) ≪≫
    shiftCommIso (1,0) (0,-e) ≪≫
    Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-e)) (SyntheticCategory.biShift_compat 1)

private def canonicalSuspensionTransport (e : ℤ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,e) ⋙
      shiftFunctor SyntheticSpectrum (1:ℤ) ⋙ SyntheticCategory.biShift (0,-e) ≅
      SyntheticCategory.biShift (1,0) :=
  Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,e)) (canonicalSuspensionComm e) ≪≫
    Functor.isoWhiskerRight (verticalCancellationIso e) (shiftFunctor SyntheticSpectrum (1:ℤ)) ≪≫
    Functor.leftUnitor _ ≪≫ (SyntheticCategory.biShift_compat 1).symm

private theorem exactSuspensionTransport_tail (T : TriangleData model.auxiliary) :
    letI := model.exactness.shiftCommShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))
    (exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) =
      ((SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalized_g_source_iso T).hom ≫
        (SyntheticCategory.biShift_compat 1).inv.app _ := by
  simp [exactSuspensionTransport,verticalCancellationIso,normalized_g_source_iso,Category.assoc]


private theorem exact_of_canonical_transport_detects
    (X : ClassicalObject) (e : ℤ) (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε : XModLambdaN.incl _ q≫ε.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t-k)+(1,0)).1 ((t-s,t-k)+(1,0)).2
      (XModLambdaN (((SyntheticCategory.biShift (0,e) ⋙
        shiftFunctor SyntheticSpectrum (1:ℤ) ⋙ SyntheticCategory.biShift (0,-e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (1,0) (t-s,t-k) q ε
        (a≫XModLambdaN.map ((canonicalSuspensionTransport e).hom.app _) q))) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x)
      (quotientUnshift X (1,0) (t-s,t-k) q ε
        (a≫XModLambdaN.map ((exactSuspensionTransport e).hom.app _) q)) := by
  let η := (canonicalSuspensionTransport e).symm ≪≫ exactSuspensionTransport e
  have h := quotient_unshift_natural_automorphism_detects X (1,0) q k hkq s t x η ε hε
    (a≫XModLambdaN.map ((canonicalSuspensionTransport e).hom.app _) q) ha
  have hc : ((canonicalSuspensionTransport e).hom.app _) ≫ η.hom.app _ =
      (exactSuspensionTransport e).hom.app (model.nu.functor.obj (X.obj model.auxiliary)) := by
    simp [η]
  simpa only [Category.assoc,←model.quotients.functoriality.map_comp,hc] using h

private theorem normalized_g_boundary_exact_transport
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
        (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) ≫
      (exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) =
      -((SyntheticCategory.biShift
          (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
          (normalized_g_raw_cofiber_iso T he hT).hom ≫
        (normalized_connecting_tail_iso T he).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.normalizedMap T.X T.Y T.f).map ≫
        (SyntheticCategory.biShift_compat 1).inv.app _) := by
  letI := model.exactness.shiftCommShift
    (0,-(normalizedExponent model.classicalTower T.g : ℤ))
  have h := congrArg (fun a => a ≫ (SyntheticCategory.biShift_compat 1).inv.app
      (model.nu.functor.obj (T.Y.obj model.auxiliary)))
    (normalized_g_raw_cofiber_boundary T he hT)
  simpa only [exactSuspensionTransport_tail,Category.assoc,Preadditive.neg_comp] using h


private def quotientClassUnshift (A : SyntheticSpectrum) (δ p : ℤ×ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj A) q ≅
      (SyntheticCategory.biShift δ).obj (XModLambdaN A q))
    (a : BiHom (p+δ).1 (p+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj A) q)) :
    BiHom p.1 p.2 (XModLambdaN A q) :=
  (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)

private theorem quotient_unshift_normalized_map
    (X Y : ClassicalObject) (k : ℕ) (hk : k≤1)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary))
    (δ p : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (εA : XModLambdaN ((SyntheticCategory.biShift δ).obj
        ((SyntheticCategory.biShift (0,(k:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))) q ≅
      (SyntheticCategory.biShift δ).obj (XModLambdaN
        ((SyntheticCategory.biShift (0,(k:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (εB : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q))
    (hεA : XModLambdaN.incl _ q≫εA.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (hεB : XModLambdaN.incl _ q≫εB.hom=
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom (p+δ).1 (p+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        ((SyntheticCategory.biShift (0,(k:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))) q)) :
    quotientUnshift Y δ p q εB
        (a≫XModLambdaN.map ((SyntheticCategory.biShift δ).map f) q) =
      quotientClassUnshift _ δ p q εA a ≫ XModLambdaN.map f q := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let A := (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let M := ff.preimage (εA.inv≫XModLambdaN.map (F.map f) q≫εB.hom)
  have hM : F.map M=εA.inv≫XModLambdaN.map (F.map f) q≫εB.hom := ff.map_preimage _
  dsimp only [F] at hM
  have hbase : XModLambdaN.incl A q≫M =
      XModLambdaN.incl A q≫XModLambdaN.map f q := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hM,←hεA]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hεB]
    rw [←Category.assoc,hεA,←Functor.map_comp,XModLambdaN.incl_naturality]
    simp only [Functor.map_comp]
  have heq := normalized_quotient_maps_equal_on_spheres X Y k hk q hq
    M (XModLambdaN.map f q) hbase p.1 p.2 (quotientClassUnshift A δ p q εA a)
  rw [←heq]
  apply ff.map_injective
  simp only [quotientUnshift,quotientClassUnshift,Functor.map_comp,
    Functor.FullyFaithful.map_preimage,hM,Category.assoc,Iso.hom_inv_id_assoc]

private def normalized_f_suspended_source_iso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
      (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map) ≅
      (SyntheticCategory.biShift (1,0)).obj
        ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower T.f : ℤ))).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) :=
  (SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower T.g : ℤ))).mapIso
      (normalized_g_raw_cofiber_iso T he hT) ≪≫
    normalized_connecting_tail_iso T he ≪≫
    (SyntheticCategory.biShift_compat 1).symm.app _

private theorem normalized_g_boundary_suspended_f
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he) :
    (SyntheticCategory.biShift
        (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
        (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map) ≫
      (exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app
        (model.nu.functor.obj (T.Y.obj model.auxiliary)) =
      (-(normalized_f_suspended_source_iso T he hT).hom) ≫
        (SyntheticCategory.biShift (1,0)).map (model.normalizedMap T.X T.Y T.f).map := by
  have h := normalized_g_boundary_exact_transport T he hT
  have hn := (SyntheticCategory.biShift_compat 1).inv.naturality
    (model.normalizedMap T.X T.Y T.f).map
  change (shiftFunctor SyntheticSpectrum (1:ℤ)).map _ ≫
      (SyntheticCategory.biShift_compat 1).inv.app _ =
    (SyntheticCategory.biShift_compat 1).inv.app _ ≫
      (SyntheticCategory.biShift (1,0)).map _ at hn
  rw [hn] at h
  simpa only [normalized_f_suspended_source_iso,Iso.trans_hom,
    Functor.mapIso_hom,Iso.app_hom,Iso.symm_hom,Category.assoc,Preadditive.neg_comp] using h


private theorem normalized_f_raw_boundary_equation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0<q) (p : ℤ×ℤ)
    (εA : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary)) q ≅
      (SyntheticCategory.biShift (1,0)).obj (XModLambdaN
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary) q))
    (εB : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.Y.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) q))
    (hεA : XModLambdaN.incl _ q≫εA.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (hεB : XModLambdaN.incl _ q≫εB.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (a : BiHom (p+(1,0)).1 (p+(1,0)).2 (XModLambdaN
      ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map)) q)) :
    quotientClassUnshift _ (1,0) p q εA
        (a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) q) ≫
        finiteExtensionMap model T.X T.Y T.f q =
      quotientUnshift T.Y (1,0) p q εB
        (a≫XModLambdaN.map
          ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
            (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map)) q ≫
          XModLambdaN.map
            ((exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q) := by
  have hmap : a≫XModLambdaN.map
        ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
          (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map)) q ≫
        XModLambdaN.map
          ((exactSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q =
      (a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) q) ≫
        XModLambdaN.map ((SyntheticCategory.biShift (1,0)).map
          (model.normalizedMap T.X T.Y T.f).map) q := by
    rw [←model.quotients.functoriality.map_comp,
      normalized_g_boundary_suspended_f T he hT]
    exact (congrArg (fun z => a≫z) (model.quotients.functoriality.map_comp
      (-(normalized_f_suspended_source_iso T he hT).hom)
      ((SyntheticCategory.biShift (1,0)).map (model.normalizedMap T.X T.Y T.f).map) q)).trans
        (Category.assoc _ _ _).symm
  rw [hmap]
  exact (quotient_unshift_normalized_map T.X T.Y
    (normalizedExponent model.classicalTower T.f) (normalizedExponent_le_one model.classicalTower T.f)
    (model.normalizedMap T.X T.Y T.f).map (1,0) p q hq εA εB hεA hεB _).symm

private theorem normalized_f_raw_boundary_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (y : Ambient model T.Y (s,t))
    (εA : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary)) q ≅
      (SyntheticCategory.biShift (1,0)).obj (XModLambdaN
        ((extensionSourceObject model T.X T.Y T.f).obj model.nu model.auxiliary) q))
    (εB : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
        (model.nu.functor.obj (T.Y.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) q))
    (hεA : XModLambdaN.incl _ q≫εA.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (hεB : XModLambdaN.incl _ q≫εB.hom=
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ q))
    (a : BiHom ((t-s,t-k)+(1,0)).1 ((t-s,t-k)+(1,0)).2 (XModLambdaN
      ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).obj
        (HasFunctorialCofiber.cofib (model.normalizedMap T.Y T.Z T.g).map)) q))
    (ha : Detects (model.convergence (.quotient q (.nu T.Y))) (s,t,t-k)
      (finiteTargetLabel model T.Y q s t k y)
      (quotientUnshift T.Y (1,0) (t-s,t-k) q εB
        (a≫XModLambdaN.map
          ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
            (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map)) q ≫
          XModLambdaN.map
            ((canonicalSuspensionTransport (normalizedExponent model.classicalTower T.g)).hom.app _) q))) :
    Detects (model.convergence (.quotient q (.nu T.Y))) (s,t,t-k)
      (finiteTargetLabel model T.Y q s t k y)
      (quotientClassUnshift _ (1,0) (t-s,t-k) q εA
        (a≫XModLambdaN.map (-(normalized_f_suspended_source_iso T he hT).hom) q) ≫
          finiteExtensionMap model T.X T.Y T.f q) := by
  rw [normalized_f_raw_boundary_equation T he hT q (by omega) (t-s,t-k) εA εB hεA hεB]
  have h := exact_of_canonical_transport_detects T.Y (normalizedExponent model.classicalTower T.g)
    q k hkq s t y εB hεB
    (a≫XModLambdaN.map
      ((SyntheticCategory.biShift (0,-(normalizedExponent model.classicalTower T.g : ℤ))).map
        (HasFunctorialCofiber.cofibδ (model.normalizedMap T.Y T.Z T.g).map)) q)
    (by simpa only [Category.assoc] using ha)
  simpa only [Category.assoc] using h


end
end KIP126.ProofTools.Internal.Mahowald
