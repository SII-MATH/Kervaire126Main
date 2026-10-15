module

public import KIP126.Main.Computation.LowDegrees
public import KIP126.Main.SectionSeven.ThetaMassey
public import KIP126.Main.SectionSeven.ThetaNoCrossing
public import KIP126.Main.Computation.Lambda

-- The following lemmas provide the representative and filtration calculations.
import all KIP126.Main.SectionSeven.ThetaMassey

-- The CSV coordinate calculations use the defining string and list equations.
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

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
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

open private h5_square_times_entire_770_zero from KIP126.Main.SectionSeven.ThetaMassey

section ThetaBSyntheticProof

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra KIP126.SpectralSequence.PageHomology
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}

open KIP126.Literature.AdamsSynthetic


open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126 KIP126.LinE2 KIP126.Algebra
open CategoryTheory.MonoidalCategory KIP126.StableHomotopy.Toda
attribute [local irreducible] homogeneousPart

set_option maxHeartbeats 8000000 in
private theorem theta_b_complete_from_low_degrees
 {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} {etaThetaB:BiHom 1 2 (S_0_0:Syn)}
 (A:KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D' etaThetaB G) (I':KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
 (V:SphereVanishingLine H)
 (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
 (zero_nonzero_unique : ∀ x y : E2 H SphereSpectrum 0 0, x ≠ 0 → y ≠ 0 → x = y)
 (hall:∀a:E2 H SphereSpectrum 7 70,
   Sphere.Internal.product H M' (s:=2) (t:=64) (s':=7) (t':=70) (Sphere.Internal.hiSquare H M' 5) a=0)
 (theta:BiHom 62 64 (S_0_0:Syn)) (htheta:ThetaChoice M' D'.toAdamsComparisonData theta) :
 ∃ (b:BiHom 62 70 (S_0_0:Syn)) (z:BiHom 125 134 (S_0_0:Syn)),
   SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b ∧
   SphereDetected D' 9 134 0
     (Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
       (Sphere.Internal.hi H M' 6) (I'.interpretation.sphere 8 70 B)) z ∧
   TripleToda theta syntheticTwo b z := by
  classical
  have relation_from_middle_cofiber
      {X Y Z W Q : Syn} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      {i : Z ⟶ Q} {p : Q ⟶ Y⟦(1:ℤ)⟧}
      (hT : Triangle.mk g i p ∈ distTriang Syn)
      (hfg : f≫g=0)
      (a : X⟦(1:ℤ)⟧ ⟶ Q) (ha : a≫p = -f⟦(1:ℤ)⟧')
      (b : Q ⟶ W) (hb : i≫b=h) :
      Relation (a≫b) f g h := by
    obtain ⟨Qf,j,q,hTf⟩ := distinguished_cocone_triangle f
    let Tf := Triangle.mk f j q
    let Tg := Triangle.mk g i p
    obtain ⟨gbar,hgbar⟩ := Tf.yoneda_exact₂ hTf g hfg
    dsimp only [Tf,Triangle.mk] at gbar hgbar
    have hTfr : Tf.rotate ∈ distTriang Syn := rot_of_distTriang Tf hTf
    obtain ⟨a0,ha0i,ha0p⟩ := complete_distinguished_triangle_morphism
      Tf.rotate Tg hTfr hT (𝟙 Y) gbar (by
        change j≫gbar=𝟙 Y≫g
        simpa only [Category.id_comp] using hgbar.symm)
    dsimp only [Tf,Tg,Triangle.mk,Triangle.rotate] at a0 ha0i ha0p
    have hai : q≫a0=gbar≫i := ha0i
    have hap : a0≫p = -f⟦(1:ℤ)⟧' := by
      simpa only [CategoryTheory.Functor.map_id,Category.comp_id] using ha0p.symm
    have hdiff : (a-a0)≫p=0 := by
      rw [Preadditive.sub_comp,ha,hap,sub_self]
    obtain ⟨c,hc⟩ := Tg.coyoneda_exact₃ hT (a-a0) hdiff
    dsimp only [Tg,Triangle.mk] at c hc
    have h0 : Relation (a0≫b) f g h := by
      refine ⟨Qf,j,q,hTf,gbar,hgbar.symm,?_⟩
      rw [←Category.assoc,hai,Category.assoc,hb]
    have hsum : a≫b=a0≫b+c≫h := by
      have hh := congrArg (fun z => z≫b) hc
      rw [Preadditive.sub_comp,Category.assoc,hb] at hh
      exact (sub_eq_iff_eq_add'.mp hh)
    rw [hsum]
    exact indeterminacy_right h0 c
  have sphere_two_factors_lambda_nonzero
      (coh:BiShiftCoherence Syn) (h0:BiHom 0 1 (S_0_0:Syn))
      (hlambda:lambdaMultiply 1 h0=syntheticTwo) :
      ∃ k:Smn (Syn:=Syn) 62 70⟶(SyntheticCategory.biShift (0,-1)).obj (Smn 62 70),
        k≫lambdaPow 1 (Smn 62 70)=2 • 𝟙 (Smn 62 70) ∧
        ∀theta:BiHom 62 64 (S_0_0:Syn),sphereProduct theta h0≠0 →
          (SyntheticCategory.biShift (62,70)).map theta≫k≠0 := by
    let S := (S_0_0:Syn)
    let F:=SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let E:=SyntheticCategory.biShift (Syn:=Syn) (62,70)
    let k0:S⟶F.obj S := SyntheticCategory.biShift_zero.inv.app S≫
      (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S≫F.map h0
    have hk0:k0≫SyntheticCategory.lam.app S=2 • 𝟙 S := by
      have hn:=SyntheticCategory.lam.naturality h0
      dsimp only [Functor.id_map] at hn
      have hh:=congrArg (fun f=>SyntheticCategory.biShift_zero.inv.app S≫f) hlambda
      dsimp only [lambdaMultiply,syntheticTwo] at hh
      rw [lambdaPow_one coh] at hh
      simp only [eqToHom_refl,Category.id_comp] at hh
      change SyntheticCategory.biShift_zero.inv.app S ≫
        (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S ≫ SyntheticCategory.lam.app (Smn 0 1)≫h0 =
        SyntheticCategory.biShift_zero.inv.app S≫SyntheticCategory.biShift_zero.hom.app S≫(2 • 𝟙 S) at hh
      dsimp only [k0]
      simp only [Category.assoc]
      rw [hn]
      simpa only [S,Functor.id_obj,Category.assoc,Iso.inv_hom_id_app_assoc] using hh
    let e : F.obj (E.obj S) ≅ E.obj (F.obj S) :=
      (biShiftAddIso (62,70) (0,-1) ((62,70)+(0,-1)) rfl).app S ≪≫
        ((biShiftAddIso (0,-1) (62,70) ((62,70)+(0,-1)) (add_comm _ _)).app S).symm
    have he : SyntheticCategory.lam.app (E.obj S)=e.hom≫E.map (SyntheticCategory.lam.app S) := by
      have hh:=coh.lambda_comm (62,70) S
      simpa only [E,e,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc] using hh
    refine ⟨E.map k0≫e.inv,?_,?_⟩
    · change (E.map k0≫e.inv)≫lambdaPow 1 (E.obj S)=2 • 𝟙 (E.obj S)
      rw [lambdaPow_one coh,he]
      simp only [Category.assoc,Iso.inv_hom_id_assoc]
      rw [←Functor.map_comp,hk0]
      simp [two_smul]
    · intro theta hprod hz
      have hmap:E.map (theta≫k0)≫e.inv=0 := by
        simpa only [Functor.map_comp,Category.assoc] using hz
      have hmap':E.map (theta≫k0)=0 := by
        apply (cancel_mono e.inv).mp
        simpa only [zero_comp] using hmap
      have hk:theta≫k0=0 := by
        apply (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (62,70)).map_injective
        simpa only [Functor.map_zero] using hmap'
      have hn:=(SyntheticCategory.biShift_zero (Syn:=Syn)).inv.naturality theta
      have hn':=(SyntheticCategory.biShift_comp (Syn:=Syn) (0,1) (0,-1)).inv.naturality theta
      dsimp only [Functor.id_map] at hn
      have hn0:theta≫SyntheticCategory.biShift_zero.inv.app S =
          SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫
            (SyntheticCategory.biShift (0,0)).map theta := hn
      have hn1:(SyntheticCategory.biShift (0,0)).map theta≫
          (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S =
          (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app (Smn 62 64)≫
            F.map ((SyntheticCategory.biShift (0,1)).map theta) := hn'
      dsimp only [k0] at hk
      have hh :
          SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫
          (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app (Smn 62 64)≫
          F.map ((SyntheticCategory.biShift (0,1)).map theta≫h0)=0 := by
        rw [Functor.map_comp]
        have hN0:=congrArg (fun q => q≫(SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S≫F.map h0) hn0
        have hN1:=congrArg (fun q => SyntheticCategory.biShift_zero.inv.app (Smn 62 64)≫q≫F.map h0) hn1
        simp only [Category.assoc] at hN0 hN1
        rw [←hN1,←hN0]
        exact hk
      have hF:F.map ((SyntheticCategory.biShift (0,1)).map theta≫h0)=0 := by
        simpa only [comp_eq_zero_iff_of_epi] using hh
      have hraw:(SyntheticCategory.biShift (0,1)).map theta≫h0=0 := by
        apply (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_injective
        simpa only [Functor.map_zero] using hF
      apply hprod
      unfold sphereProduct
      rw [hraw,comp_zero]
  have theta_b_actual_lambda_cofiber_candidate_universal
      (coh:BiShiftCoherence Syn) (h0:BiHom 0 1 (S_0_0:Syn))
      (hlambda:lambdaMultiply 1 h0=syntheticTwo)
      (theta:BiHom 62 64 (S_0_0:Syn)) (htheta:theta+theta=0)
      (hprod:sphereProduct theta h0≠0) (b:BiHom 62 70 (S_0_0:Syn)) :
      ∃ a:((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=Syn) 62 64))⟦(1:ℤ)⟧⟶
          XModLambdaN (Smn (Syn:=Syn) 62 70) 1,
        a≠0 ∧ ∀ r:XModLambdaN (Smn (Syn:=Syn) 62 70) 1⟶XModLambdaN (S_0_0:Syn) 1,
          XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1≫r=quotientClass 1 b →
          Toda.Relation (a≫r)
          ((SyntheticCategory.biShift (62,70)).map theta)
          (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b) := by
    obtain ⟨k,hk,hkn⟩:=sphere_two_factors_lambda_nonzero coh h0 hlambda
    let f:=(SyntheticCategory.biShift (62,70)).map theta
    let Y:=(Smn (Syn:=Syn) 62 70)
    let T:=XModLambdaN.cofiberTriangle Y 1
    have hT:T∈distTriang Syn:=HasFunctorialCofiber.cofib_distinguished _
    have hfg:(f≫k)≫lambdaPow 1 Y=0 := by
      rw [Category.assoc,hk]
      have hf:f+f=0 := by
        dsimp only [f]
        rw [←Functor.map_add,htheta,Functor.map_zero]
      simpa [Y,f,Smn,two_smul,Preadditive.comp_add] using hf
    have hm:(-(f≫k)⟦(1:ℤ)⟧')≫(lambdaPow 1 Y)⟦(1:ℤ)⟧'=0 := by
      rw [Preadditive.neg_comp,←Functor.map_comp,hfg,Functor.map_zero,neg_zero]
    obtain ⟨a,ha⟩:=T.coyoneda_exact₁ hT (-(f≫k)⟦(1:ℤ)⟧') hm
    dsimp only [T,XModLambdaN.cofiberTriangle,Triangle.mk] at a ha
    refine ⟨a,?_,?_⟩
    · intro ha0
      apply hkn theta hprod
      apply (shiftFunctor Syn (1:ℤ)).map_injective
      rw [ha0,zero_comp] at ha
      simpa only [Functor.map_zero] using neg_eq_zero.mp ha
    intro r hr
    have hrel:=relation_from_middle_cofiber hT hfg a ha.symm r hr
    have hr':Toda.Relation (a≫r) (f≫k)
        (lambdaPow 1 Y) (quotientClass 1 b) := hrel
    have hh:=Toda.absorb_first hr'
    rw [hk] at hh
    exact hh
  have quotient_algebra_product_zero_swap {D' : AdamsComparison H M' Syn}
      (algebra:AdamsAlgebraStructures D') (m n k l:ℤ) :
      letI:=algebra.syntheticSymmetric
      ∀ (x:BiHom m n (XModLambdaN (S_0_0:Syn) 1))
        (y:BiHom k l (XModLambdaN (S_0_0:Syn) 1)),
        KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide)) x y=0 →
        KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide)) y x=0 := by
    letI:=algebra.syntheticSymmetric
    intro x y h
    let Q:=algebra.quotients.algebra 1 (by decide)
    letI:=Q
    letI:=algebra.quotients.commutative 1 (by decide)
    have hh:(y⊗ₘx)≫Q.mul=0 := by
      simpa only [KIP126.AdamsSynthetic.algebraProduct,Category.assoc,comp_eq_zero_iff_of_epi] using h
    have hz:(x⊗ₘy)≫Q.mul=0 := by
      have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:Syn) 1)
      change (β_ (XModLambdaN (S_0_0:Syn) 1) (XModLambdaN (S_0_0:Syn) 1)).hom≫Q.mul=Q.mul at hc
      rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc,hh,comp_zero]
    dsimp only [KIP126.AdamsSynthetic.algebraProduct]
    rw [hz,comp_zero,comp_zero]
  have theta_h0_first_nonzero {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
   (h0:BiHom 0 1 (S_0_0:Syn)) (theta:BiHom 62 64 (S_0_0:Syn))
   (h0label:D'.sphereFirstQuotient 1 1 (quotientClass 1 h0)=Sphere.Internal.hi H M' 0)
   (htheta:ThetaChoice M' D'.toAdamsComparisonData theta) :
   D'.sphereFirstQuotient 3 65 (quotientClass 1 (sphereProduct h0 theta))≠0 := by
   letI := algebra.syntheticSymmetric
   have hmul := ab.first_quotient 1 1 2 64 (quotientClass 1 h0) (quotientClass 1 theta)
   change D'.sphereFirstQuotient 3 65
     (KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
       (quotientClass 1 h0) (quotientClass 1 theta)) = _ at hmul
   have hact := qb.sphere_action 1 (by decide) 0 1 62 64 h0 (quotientClass 1 theta)
   change KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
     (quotientClass 1 h0) (quotientClass 1 theta)=sphereAction h0 (quotientClass 1 theta) at hact
   rw [hact] at hmul
   have hprod : D'.sphereFirstQuotient 3 65 (quotientClass 1 (sphereProduct h0 theta)) =
     Sphere.Internal.product H M' (s:=1) (t:=1) (s':=2) (t':=64)
        (Sphere.Internal.hi H M' 0) (Sphere.Internal.hiSquare H M' 5) := by
     change D'.sphereFirstQuotient 3 65 (sphereAction h0 (quotientClass 1 theta)) =
       Sphere.Internal.product H M' (s:=1) (t:=1) (s':=2) (t':=64)
         (D'.sphereFirstQuotient 1 1 (quotientClass 1 h0))
         (D'.sphereFirstQuotient 2 64 (quotientClass 1 theta)) at hmul
     rw [h0label,show D'.sphereFirstQuotient 2 64 (quotientClass 1 theta)=
        Sphere.Internal.hiSquare H M' 5 from htheta] at hmul
     simpa only [sphereAction,sphereProduct,quotientClass,Category.assoc] using hmul
   have ht : I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq) = I'.interpretation.basis .sphere 3 65 0 := by
     have hc := I'.monomials (⟨.sphere,3,65,["0,1,18,2"]⟩ : Raw.Degree) (by
       unfold Raw.degrees
       iterate 102 apply List.mem_cons_of_mem
       exact List.mem_cons_self) rfl
     obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
     have heq : (mulAt dataH0 h5Sq)=z := by
       apply Subtype.ext
       rw [hz]
       change generator ⟨0,by decide⟩ * (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,1,18,2")
       have hp : (("0,1,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 18, 2] := by
         have split : "0,1,18,2".splitOn "," = ["0", "1", "18", "2"] := by
           simp +decide [String.splitOn,String.splitOnAux]
         rw [split]
         simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
           String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
       simp only [monomialOfString,show "0,1,18,2"≠"" by decide,if_false,hp]
       norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
     rw [heq]
     exact he
   have hpn : I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq)≠0 := by
     rw [ht]
     obtain ⟨e,he⟩ := I'.basis ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
       unfold Raw.degrees
       iterate 102 apply List.mem_cons_of_mem
       exact List.mem_cons_self)
     change E2 H SphereSpectrum 3 65 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
     change ∀ i:Fin 1,e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 3 65 i.val at he
     intro h
     have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=I'.interpretation.basis .sphere 3 65 0 := he 0
     have hh := congrArg (fun x => e x 0) (he0.trans h)
     simp at hh
   intro hz
   have hm:=I'.products ⟨1,1,2,64⟩ (by simp [Raw.products]) dataH0 h5Sq
   rw [I'.distinguishedClasses.h0,I'.distinguishedClasses.h5_square] at hm
   exact hpn (hm.trans (hprod.symm.trans hz))
  have theta_h0_right_nonzero {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
   (h0:BiHom 0 1 (S_0_0:Syn)) (theta:BiHom 62 64 (S_0_0:Syn))
   (h0label:D'.sphereFirstQuotient 1 1 (quotientClass 1 h0)=Sphere.Internal.hi H M' 0)
   (htheta:ThetaChoice M' D'.toAdamsComparisonData theta) : sphereProduct theta h0≠0 := by
   letI:=algebra.syntheticSymmetric
   intro hz
   have hq:KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
       (quotientClass 1 theta) (quotientClass 1 h0)=0 := by
     have hact:=qb.sphere_action 1 (by decide) 62 64 0 1 theta (quotientClass 1 h0)
     change KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
       (quotientClass 1 theta) (quotientClass 1 h0)=sphereAction theta (quotientClass 1 h0) at hact
     rw [hact]
     have hh:=congrArg (quotientClass 1) hz
     simpa only [quotientClass,sphereProduct,sphereAction,Category.assoc,zero_comp] using hh
   have hq':=quotient_algebra_product_zero_swap algebra 62 64 0 1
     (quotientClass 1 theta) (quotientClass 1 h0) hq
   have hact:=qb.sphere_action 1 (by decide) 0 1 62 64 h0 (quotientClass 1 theta)
   change KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
     (quotientClass 1 h0) (quotientClass 1 theta)=sphereAction h0 (quotientClass 1 theta) at hact
   rw [hact] at hq'
   apply theta_h0_first_nonzero I' algebra qb ab h0 theta h0label htheta
   have heq:quotientClass 1 (sphereProduct h0 theta)=0 := by
     simpa only [quotientClass,sphereProduct,sphereAction,Category.assoc] using hq'
   rw [heq,map_zero]
  have q1_nonzero_is_h6 {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)) (hune:u≠0) :
   D'.sphereFirstQuotient 1 64 u=Sphere.Internal.hi H M' 6 := by
   have hs : I'.interpretation.sphere 1 64 (dataH6) = I'.interpretation.basis .sphere 1 64 0 := by
     have hc := I'.monomials (⟨.sphere,1,64,["69,1"]⟩ : Raw.Degree) (by
       unfold Raw.degrees
       iterate 85 apply List.mem_cons_of_mem
       exact List.mem_cons_self) rfl
     obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
     have heq : (dataH6)=z := by
       apply Subtype.ext
       rw [hz]
       change generator ⟨69,by decide⟩ = projection (monomialOfString "69,1")
       have hp : (("69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1] := by
         have split : "69,1".splitOn "," = ["69", "1"] := by
           simp +decide [String.splitOn,String.splitOnAux]
         rw [split]
         simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
           String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
       simp only [monomialOfString,show "69,1"≠"" by decide,if_false,hp]
       norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
     rw [heq]
     exact he
   let x:=D'.sphereFirstQuotient 1 64 u
   have hxne:x≠0 := by
     intro h
     apply hune
     apply (D'.sphereFirstQuotient 1 64).injective
     exact h.trans (map_zero _).symm
   obtain ⟨e,he⟩ := I'.basis ⟨.sphere,1,64,["69,1"]⟩ (by
     unfold Raw.degrees
     iterate 85 apply List.mem_cons_of_mem
     exact List.mem_cons_self)
   change E2 H SphereSpectrum 1 64 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
   change ∀ i:Fin 1,e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 1 64 i.val at he
   have heq:e x=Finsupp.single 0 (e x 0) := by
     apply Finsupp.ext
     intro i
     fin_cases i
     simp
   have hxe:x=e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
   generalize hc:e x 0=c at hxe
   fin_cases c
   · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
     exact (hxne hxe).elim
   · change x=e.symm (Finsupp.single 0 1) at hxe
     exact hxe.trans ((he 0).trans (hs.symm.trans I'.distinguishedClasses.h6))
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
  have quotient_shift_iso (D' : AdamsComparison H M' Syn) (a : ℤ × ℤ) (A : Syn) (q : ℕ) :
      ∃ e : (SyntheticCategory.biShift a).obj (XModLambdaN A q) ≅
        XModLambdaN ((SyntheticCategory.biShift a).obj A) q,
        (SyntheticCategory.biShift a).map (XModLambdaN.incl A q) ≫ e.hom =
        XModLambdaN.incl ((SyntheticCategory.biShift a).obj A) q := by
    letI := D'.shiftCommShift a
    letI := D'.shiftExact a
    let T := Triangle.mk (lambdaPow q A)
      (HasFunctorialCofiber.cofibι (lambdaPow q A))
      (HasFunctorialCofiber.cofibδ (lambdaPow q A))
    let U := Triangle.mk (lambdaPow q ((SyntheticCategory.biShift a).obj A))
      (HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
      (HasFunctorialCofiber.cofibδ (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
    let c : ((SyntheticCategory.biShift a).mapTriangle.obj T).obj₁ ≅ U.obj₁ :=
      (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).symm
    have hc : ((SyntheticCategory.biShift a).mapTriangle.obj T).mor₁ ≫ (Iso.refl _).hom =
        c.hom ≫ U.mor₁ := by
      change (SyntheticCategory.biShift a).map (lambdaPow q A) ≫ 𝟙 _ =
        (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).inv ≫
          lambdaPow q ((SyntheticCategory.biShift a).obj A)
      rw [lambda_pow_shift D'.shiftCoherence]
      simp only [Iso.inv_hom_id_assoc,Category.comp_id]
    let E := CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂
      ((SyntheticCategory.biShift a).mapTriangle.obj T) U
      ((SyntheticCategory.biShift a).map_distinguished T (HasFunctorialCofiber.cofib_distinguished _))
      (HasFunctorialCofiber.cofib_distinguished _) c (Iso.refl _) hc
    refine ⟨Triangle.π₃.mapIso E, ?_⟩
    have hh : (SyntheticCategory.biShift a).map (HasFunctorialCofiber.cofibι (lambdaPow q A)) ≫
        E.hom.hom₃ = E.hom.hom₂ ≫
        HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)) := E.hom.comm₂
    have he₂ : E.hom.hom₂ = 𝟙 _ :=
      CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
    rw [he₂,Category.id_comp] at hh
    exact hh
  have theta_b_actual_h6_cofiber_candidate_universal {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
   (h0:BiHom 0 1 (S_0_0:Syn)) (theta:BiHom 62 64 (S_0_0:Syn))
   (h0label:D'.sphereFirstQuotient 1 1 (quotientClass 1 h0)=Sphere.Internal.hi H M' 0)
   (htheta:ThetaChoice M' D'.toAdamsComparisonData theta)
   (hlambda:lambdaMultiply 1 h0=syntheticTwo) (horder:theta+theta=0)
   (b:BiHom 62 70 (S_0_0:Syn)) :
   ∃ (e:(SyntheticCategory.biShift (62,70)).obj (XModLambdaN (S_0_0:Syn) 1) ≅
         XModLambdaN (Smn (Syn:=Syn) 62 70) 1)
     (a:((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=Syn) 62 64))⟦(1:ℤ)⟧⟶
         XModLambdaN (Smn (Syn:=Syn) 62 70) 1)
     (u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)),
     (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:Syn) 1)≫e.hom=
         XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1 ∧
     susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:Syn) 1) u=
       (tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70).hom≫a≫e.inv ∧
     u≠0 ∧ D'.sphereFirstQuotient 1 64 u=Sphere.Internal.hi H M' 6 ∧
     (∀ r:XModLambdaN (Smn (Syn:=Syn) 62 70) 1⟶XModLambdaN (S_0_0:Syn) 1,
       XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1≫r=quotientClass 1 b →
       Toda.Relation (a≫r) ((SyntheticCategory.biShift (62,70)).map theta)
       (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b)) := by
   letI:=D'.shiftAdditive
   obtain ⟨a,ha,hrel⟩:=theta_b_actual_lambda_cofiber_candidate_universal D'.shiftCoherence h0 hlambda
     theta horder (theta_h0_right_nonzero I' algebra qb ab h0 theta h0label htheta) b
   obtain ⟨e,he⟩:=quotient_shift_iso D' (62,70) (S_0_0:Syn) 1
   let src:=tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70
   let u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1):=
     (susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:Syn) 1)).symm (src.hom≫a≫e.inv)
   have hu:susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:Syn) 1) u=src.hom≫a≫e.inv :=
     Equiv.apply_symm_apply _ _
   have hun:u≠0 := by
     intro hz
     apply ha
     apply (cancel_mono e.inv).mp
     apply (cancel_epi src.hom).mp
     rw [hz] at hu
     simpa [susp_invariance] using hu.symm
   exact ⟨e,a,u,he,hu,hun,q1_nonzero_is_h6 I' u hun,hrel⟩
  have tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=Syn) m n)).Faithful := by
    let e : Smn (Syn:=Syn) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ Syn) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:Syn) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:Syn)
    let f : tensorLeft (Smn (Syn:=Syn) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 Syn :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft Syn).mapIso e ≪≫ leftUnitorNatIso Syn
    exact Functor.Faithful.of_comp_iso f
  have q1_nonzero_unique {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (u v:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)) (hu:u≠0) (hv:v≠0) : u=v := by
    classical
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,1,64,["69,1"]⟩ (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 1 64 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    have hc (u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)) (hu:u≠0) :
        e (D'.sphereFirstQuotient 1 64 u)=Finsupp.single 0 1 := by
      let x:=e (D'.sphereFirstQuotient 1 64 u)
      have heq:x=Finsupp.single 0 (x 0) := by
        apply Finsupp.ext
        intro i
        fin_cases i
        simp
      generalize h:x 0=c at heq
      fin_cases c
      · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero] at heq
        exfalso
        apply hu
        apply (D'.sphereFirstQuotient 1 64).injective
        apply e.injective
        simpa only [map_zero] using heq
      · exact heq
    apply (D'.sphereFirstQuotient 1 64).injective
    apply e.injective
    rw [hc u hu,hc v hv]
  have h6_tensor_square {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G) (may:MayContext Syn)
   (u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)) (hu:u≠0) :
   (biShift_eq_tensor_Smn 62 70 (Smn (Syn:=Syn) 63 64)).hom≫
      (𝟙 (Smn (Syn:=Syn) 62 70) ⊗ₘ u)=
   (SyntheticCategory.biShift (62,70)).map u≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom := by
    let F:=SyntheticCategory.biShift (Syn:=Syn) (62,70)
    let T:=tensorLeft (Smn (Syn:=Syn) 62 70)
    letI:=D'.shiftAdditive (62,70)
    letI:=may.leftShift (Smn (Syn:=Syn) 62 70)
    letI:=may.leftExact (Smn (Syn:=Syn) 62 70)
    letI : T.Faithful := tensorLeft_sphere_faithful 62 70
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (62,70)
    let z : BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1) := ff.preimage
      ((biShift_eq_tensor_Smn 62 70 (Smn (Syn:=Syn) 63 64)).hom≫T.map u≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv)
    have hz : F.map z=(biShift_eq_tensor_Smn 62 70 (Smn (Syn:=Syn) 63 64)).hom≫T.map u≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv := ff.map_preimage _
    have hzn:z≠0 := by
      intro h
      rw [h,Functor.map_zero] at hz
      have ht:T.map u=0 := by
        apply (cancel_epi (biShift_eq_tensor_Smn 62 70 (Smn (Syn:=Syn) 63 64)).hom).mp
        apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv).mp
        simpa only [Category.assoc,Limits.comp_zero,Limits.zero_comp] using hz.symm
      apply hu
      apply T.map_injective
      simpa only [Functor.map_zero] using ht
    have he:z=u:=q1_nonzero_unique I' z u hzn hu
    rw [he] at hz
    apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv).mp
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id, T, tensorLeft, curriedTensor_obj_map, F, id_tensorHom] using hz.symm
  have quotient_inclusion_nonzero {D' : AdamsComparison H M' Syn}
   (algebra:AdamsAlgebraStructures D') (may:MayContext Syn)
   (u:BiHom 63 64 (XModLambdaN (S_0_0:Syn) 1)) (hu:u≠0) :
   XModLambdaN.incl (S_0_0:Syn) 1≠0 := by
    letI:=algebra.syntheticSymmetric
    letI:=algebra.quotients.algebra 1 (by decide)
    letI:=may.rightShift
    letI:=may.rightExact
    intro h
    have hunit : (MonObj.one (X:=XModLambdaN (S_0_0:Syn) 1))=0 :=
      (algebra.quotients.unit 1 (by decide)).trans h
    have hm:=Mathlib.Tactic.MonTauto.leftUnitor_inv_one_tensor_mul u
    rw [hunit] at hm
    have hz : (0:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1) ⊗ₘ u=0 := by
      rw [tensorHom_def]
      have hz' : (0:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1) ▷ Smn (Syn:=Syn) 63 64=0 :=
        (tensorRight (Smn (Syn:=Syn) 63 64)).map_zero _ _
      rw [hz',Limits.zero_comp]
    rw [hz,Limits.zero_comp,Limits.comp_zero] at hm
    exact hu hm.symm
  have tensor_inclusion_square (D':AdamsComparison H M' Syn)
   (may:MayContext Syn)
   (hi:XModLambdaN.incl (S_0_0:Syn) 1≠0)
   (unique : ∀f g:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1, f≠0→g≠0→f=g) :
   (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:Syn) 1)≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom=
   (ρ_ (Smn (Syn:=Syn) 62 70)).inv≫
      (𝟙 (Smn (Syn:=Syn) 62 70) ⊗ₘ XModLambdaN.incl (S_0_0:Syn) 1) := by
    let F:=SyntheticCategory.biShift (Syn:=Syn) (62,70)
    let T:=tensorLeft (Smn (Syn:=Syn) 62 70)
    letI:=D'.shiftAdditive (62,70)
    letI:=may.leftShift (Smn (Syn:=Syn) 62 70)
    letI:=may.leftExact (Smn (Syn:=Syn) 62 70)
    letI : T.Faithful := tensorLeft_sphere_faithful 62 70
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (62,70)
    let z : (S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1 := ff.preimage
      ((ρ_ (Smn (Syn:=Syn) 62 70)).inv≫T.map (XModLambdaN.incl (S_0_0:Syn) 1)≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv)
    have hz : F.map z=(ρ_ (Smn (Syn:=Syn) 62 70)).inv≫T.map (XModLambdaN.incl (S_0_0:Syn) 1)≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv := ff.map_preimage _
    have hzn:z≠0 := by
      intro h
      rw [h,Functor.map_zero] at hz
      have ht:T.map (XModLambdaN.incl (S_0_0:Syn) 1)=0 := by
        apply (cancel_epi (ρ_ (Smn (Syn:=Syn) 62 70)).inv).mp
        apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv).mp
        simpa only [Category.assoc,Limits.comp_zero,Limits.zero_comp] using hz.symm
      apply hi
      apply T.map_injective
      simpa only [Functor.map_zero] using ht
    have he:z=XModLambdaN.incl (S_0_0:Syn) 1:=unique _ _ hzn hi
    rw [he] at hz
    apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).inv).mp
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,T,tensorLeft,curriedTensor_obj_map,F,id_tensorHom] using hz
  have algebra_filler_inclusion {D' : AdamsComparison H M' Syn}
   (algebra:AdamsAlgebraStructures D') (may:MayContext Syn)
   (hi:XModLambdaN.incl (S_0_0:Syn) 1≠0)
   (unique : ∀f g:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1, f≠0→g≠0→f=g)
   (b:BiHom 62 70 (S_0_0:Syn))
   (e:(SyntheticCategory.biShift (62,70)).obj (XModLambdaN (S_0_0:Syn) 1) ≅
       XModLambdaN (Smn (Syn:=Syn) 62 70) 1)
   (he:(SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:Syn) 1)≫e.hom=
       XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1) :
   letI:=algebra.syntheticSymmetric
   XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1≫e.inv≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom≫
      (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 1))≫
      (algebra.quotients.algebra 1 (by decide)).mul=quotientClass 1 b := by
    letI:=algebra.syntheticSymmetric
    letI:=algebra.quotients.algebra 1 (by decide)
    have hh:XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1≫e.inv=
        (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:Syn) 1) := by
      rw [←he,Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [←Category.assoc,←Category.assoc,←Category.assoc,hh]
    rw [Category.assoc,Category.assoc]
    rw [←Category.assoc,tensor_inclusion_square D' may hi unique]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=Syn) 62 70) ⊗ₘ XModLambdaN.incl (S_0_0:Syn) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←algebra.quotients.unit 1 (by decide)]
    exact Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 b)
  have theta_b_algebra_toda_candidate {D' : AdamsComparison H M' Syn}
   {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G)
   (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
   (may:MayContext Syn)
   (unique : ∀f g:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1, f≠0→g≠0→f=g)
   (h0:BiHom 0 1 (S_0_0:Syn)) (theta:BiHom 62 64 (S_0_0:Syn))
   (h0label:D'.sphereFirstQuotient 1 1 (quotientClass 1 h0)=Sphere.Internal.hi H M' 0)
   (htheta:ThetaChoice M' D'.toAdamsComparisonData theta)
   (hlambda:lambdaMultiply 1 h0=syntheticTwo) (horder:theta+theta=0)
   (b:BiHom 62 70 (S_0_0:Syn)) :
   ∃ z:BiHom 125 134 (XModLambdaN (S_0_0:Syn) 1),
     Toda.Relation ((tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70).inv≫z)
       ((SyntheticCategory.biShift (62,70)).map theta) (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b) ∧
     D'.sphereFirstQuotient 9 134 z=
       Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
         (Sphere.Internal.hi H M' 6) (D'.sphereFirstQuotient 8 70 (quotientClass 1 b)) := by
    letI:=algebra.syntheticSymmetric
    obtain ⟨e,a,u,he,hu,hun,hul,ha⟩:=theta_b_actual_h6_cofiber_candidate_universal
      I' algebra qb ab h0 theta h0label htheta hlambda horder b
    let Q:=algebra.quotients.algebra 1 (by decide)
    let R:XModLambdaN (Smn (Syn:=Syn) 62 70) 1⟶XModLambdaN (S_0_0:Syn) 1:=
      e.inv≫(biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom≫
        (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 1))≫Q.mul
    have hi:XModLambdaN.incl (Smn (Syn:=Syn) 62 70) 1≫R=quotientClass 1 b :=
      algebra_filler_inclusion algebra may (quotient_inclusion_nonzero algebra may u hun) unique b e he
    let src:=tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70
    refine ⟨src.hom≫a≫R,?_,?_⟩
    · simpa only [src,Iso.inv_hom_id_assoc] using ha R hi
    have hp:src.hom≫a≫R=KIP126.AdamsSynthetic.algebraProduct Q u (quotientClass 1 b) := by
      have huR:src.hom≫a≫R=(susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:Syn) 1) u)≫
          (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom≫
          (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 1))≫Q.mul := by
        dsimp only [R]
        simpa only [Category.assoc] using congrArg (fun v=>v≫
          (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:Syn) 1)).hom≫
          (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:Syn) 1))≫Q.mul) hu.symm
      rw [huR]
      dsimp only [susp_invariance]
      simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
        Iso.homCongr_apply,Iso.refl_hom,Category.comp_id,Category.assoc]
      rw [←Category.assoc ((SyntheticCategory.biShift (62,70)).map u),←h6_tensor_square I' may u hun]
      simp only [Category.assoc]
      rw [←Category.assoc (𝟙 (Smn (Syn:=Syn) 62 70) ⊗ₘ u),tensorHom_comp_tensorHom,
        Category.id_comp,Category.comp_id]
      rfl
    rw [hp]
    have hm:=ab.first_quotient 1 64 8 70 u (quotientClass 1 b)
    change D'.sphereFirstQuotient 9 134 (KIP126.AdamsSynthetic.algebraProduct Q u (quotientClass 1 b))=
      Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
        (D'.sphereFirstQuotient 1 64 u) (D'.sphereFirstQuotient 8 70 (quotientClass 1 b)) at hm
    rw [hul] at hm
    exact hm
  have zero_hom_nonzero_unique (D':AdamsComparison H M' Syn)
   (zero_nonzero_unique : ∀ x y : E2 H SphereSpectrum 0 0, x ≠ 0 → y ≠ 0 → x = y) :
   ∀f g:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1,f≠0→g≠0→f=g := by
    intro f g hf hg
    have hn (x:(S_0_0:Syn)⟶XModLambdaN (S_0_0:Syn) 1) (hx:x≠0) :
        D'.sphereFirstQuotient 0 0 (SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn)≫x)≠0 := by
      intro h
      apply hx
      apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn))).mp
      apply (D'.sphereFirstQuotient 0 0).injective
      simpa only [Limits.comp_zero,map_zero] using h
    apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn))).mp
    apply (D'.sphereFirstQuotient 0 0).injective
    exact zero_nonzero_unique _ _ (hn f hf) (hn g hg)
  have sphere_first_label_transport {D' : AdamsComparison H M' Syn} (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      D'.sphereFirstQuotient s t
        (firstLabel D' .sphere s t x ≫ XModLambdaN.map
          (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum) ≫ D'.nu.unitIso.hom) 1)=x := by
    let e : nuZero D' .sphere ≅ (S_0_0 : Syn) :=
      SyntheticCategory.biShift_zero.app _ ≪≫ D'.nu.unitIso
    let q := (D'.quotientFunctoriality.functor 1).mapIso e
    let c : BiHom (t-s) t (XModLambdaN (nuZero D' .sphere) 1) ≃+ E2 H SphereSpectrum s t :=
      Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D' .sphere) 1) ≃+
        E2 H SphereSpectrum s t) (Int.add_zero t)) (D'.firstQuotient SphereSpectrum 0 s t)
    change c ((firstLabel D' .sphere s t x ≫ q.hom) ≫ q.inv)=x
    rw [Category.assoc,q.hom_inv_id]
    erw [Category.comp_id]
    have cast_symm (w₁ w₂ : ℤ) (h : w₁=w₂)
        (E : BiHom (t-s) w₁ (XModLambdaN (nuZero D' .sphere) 1) ≃+ E2 H SphereSpectrum s t)
        (x : E2 H SphereSpectrum s t) :
        Eq.mp (congrArg (fun z => BiHom (t-s) z (XModLambdaN (nuZero D' .sphere) 1)) h) (E.symm x) =
          (Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D' .sphere) 1) ≃+
            E2 H SphereSpectrum s t) h) E).symm x := by
      subst w₂
      rfl
    have hx : firstLabel D' .sphere s t x=c.symm x := by
      dsimp only [firstLabel,c,ClassicalObject.obj,nuZero]
      exact cast_symm (t+0) t (Int.add_zero t) (D'.firstQuotient SphereSpectrum 0 s t) x
    rw [hx,c.apply_symm_apply]
  have sphere_first_quotient_permanent {D' : AdamsComparison H M' Syn}
      (synthetic : SyntheticComparisonTheorems D') (s t : ℤ)
      (a : BiHom (t-s) t (S_0_0 : Syn)) :
      D'.sphereFirstQuotient s t (quotientClass 1 a) ∈
        PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := by
    let x := D'.sphereFirstQuotient s t (quotientClass 1 a)
    let e : nuZero D' .sphere ≅ (S_0_0 : Syn) :=
      SyntheticCategory.biShift_zero.app _ ≪≫ D'.nu.unitIso
    let q := (D'.quotientFunctoriality.functor 1).mapIso e
    apply (synthetic.permanent_lift .sphere s t x).mpr
    refine ⟨a≫e.inv,?_⟩
    apply (cancel_mono q.hom).mp
    have hx : firstLabel D' .sphere s t x≫q.hom=quotientClass 1 a := by
      apply (D'.sphereFirstQuotient s t).injective
      exact sphere_first_label_transport s t x
    rw [hx]
    change ((a≫e.inv)≫XModLambdaN.incl (nuZero D' .sphere) 1)≫XModLambdaN.map e.hom 1 = _
    rw [Category.assoc,Category.assoc,←XModLambdaN.incl_naturality]
    simp only [←Category.assoc,e.inv_hom_id,Category.comp_id,quotientClass]
  have permanent_d2_zero {H : Mod2EilenbergMacLane (C:=C)} (s t:ℤ) (x:E2 H SphereSpectrum s t)
      (hx:x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t)) :
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d 2 (s,t) x=0 := by
    let E:=adamsTowerInternalSpectralSequence H.unit SphereSpectrum
    have hc : x∈PageRepresentatives.cycles H SphereSpectrum 2 (s,t) :=
      PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (s,t) 2 hx
    obtain ⟨z,hz⟩ := hc
    have hh : PageRepresentatives.cycleMap H SphereSpectrum (↑(1:ℕ)) (s,t)≫E.d 2 (s,t)=0 := by
      apply comp_eq_zero_of_image_le_kernel
      rw [E.Z_succ 2 (s,t) (by change (2:ℤ)≤2; omega)]
      exact le_refl _
    change E.d 2 (s,t) x=0
    rw [←hz]
    simpa using congrArg (fun f => f z) hh
  have sphere_first_quotient_63_64_zero {D' : AdamsComparison H M' Syn}
      {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G) (synthetic:SyntheticComparisonTheorems D')
      (a:BiHom 63 64 (S_0_0:Syn)) : D'.sphereFirstQuotient 1 64 (quotientClass 1 a)=0 := by
    classical
    let E:=sequence D' .sphere
    let x:=D'.sphereFirstQuotient 1 64 (quotientClass 1 a)
    have hd : E.d 2 (1,64) x=0 := permanent_d2_zero 1 64 x (sphere_first_quotient_permanent synthetic 1 64 a)
    have h142 : HasDifferential E 2 (1,64) (3,65)
        (I'.interpretation.basis .sphere 1 64 0) (I'.interpretation.basis .sphere 3 65 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,1,64,[0],3,65,[0],"S0_AdamsE2_ss",401⟩ (by
        unfold Raw.claims
        iterate 142 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨a,ha,b,hb,hab⟩ := hrow
      change HasDifferential E 2 (1,64) (3,65) a b at hab
      have va : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0]=true := rfl
      have vb : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0]=true := rfl
      simp only [E2Interpretation.coordinateSum,va,vb,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
      rw [←ha,←hb] at hab
      exact hab
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 102 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 3 65 ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
    change ∀i:Fin 1,f.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 3 65 i.val at hf
    have hn:I'.interpretation.basis .sphere 3 65 0≠0 := by
      intro h
      have h0:=congrArg (fun z=>f z 0) ((hf 0).trans h)
      simp at h0
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,1,64,["69,1"]⟩ (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 1 64 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀i:Fin 1,e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 1 64 i.val at he
    have heq:e x=Finsupp.single 0 (e x 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hxe:x=e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc:e x 0=c at hxe
    change x=0
    fin_cases c
    · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
      exact hxe
    · change x=e.symm (Finsupp.single 0 1) at hxe
      rw [he] at hxe
      change x=I'.interpretation.basis .sphere 1 64 0 at hxe
      obtain ⟨hdeg,hh⟩ := h142.eq_on_page_two
      apply False.elim
      apply hn
      rw [←hxe,ConcreteCategory.comp_apply,hd,map_zero] at hh
      exact hh.symm
  have theta_b_right_indeterminacy_first_zero {D' : AdamsComparison H M' Syn}
      {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G) (synthetic:SyntheticComparisonTheorems D')
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
      (c:BiHom 63 64 (S_0_0:Syn)) (b:BiHom 62 70 (S_0_0:Syn)) :
      D'.sphereFirstQuotient 9 134 (quotientClass 1 (sphereProduct c b))=0 := by
    letI:=algebra.syntheticSymmetric
    have hm:=ab.first_quotient 1 64 8 70 (quotientClass 1 c) (quotientClass 1 b)
    change D'.sphereFirstQuotient 9 134
      (KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
        (quotientClass 1 c) (quotientClass 1 b)) = _ at hm
    have ha:=qb.sphere_action 1 (by decide) 63 64 62 70 c (quotientClass 1 b)
    change KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
      (quotientClass 1 c) (quotientClass 1 b)=sphereAction c (quotientClass 1 b) at ha
    rw [ha] at hm
    change D'.sphereFirstQuotient 9 134 (sphereAction c (quotientClass 1 b)) =
      Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
        (D'.sphereFirstQuotient 1 64 (quotientClass 1 c))
        (D'.sphereFirstQuotient 8 70 (quotientClass 1 b)) at hm
    have hz:D'.sphereFirstQuotient 9 134 (sphereAction c (quotientClass 1 b))=0 := by
      rw [hm,sphere_first_quotient_63_64_zero I' synthetic c]
      simp only [Sphere.Internal.product,map_zero,LinearMap.zero_apply]
    simpa only [sphereAction,sphereProduct,quotientClass,Category.assoc] using hz
  have theta_b_left_indeterminacy_first_zero {D' : AdamsComparison H M' Syn}
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
      (theta:BiHom 62 64 (S_0_0:Syn)) (htheta:ThetaChoice M' D'.toAdamsComparisonData theta)
      (hall:∀a:E2 H SphereSpectrum 7 70,
        Sphere.Internal.product H M' (s:=2) (t:=64) (s':=7) (t':=70) (Sphere.Internal.hiSquare H M' 5) a=0)
      (a:BiHom 63 70 (XModLambdaN (S_0_0:Syn) 1)) :
      D'.sphereFirstQuotient 9 134 (sphereAction theta a)=0 := by
    letI:=algebra.syntheticSymmetric
    have hm:=ab.first_quotient 2 64 7 70 (quotientClass 1 theta) a
    change D'.sphereFirstQuotient 9 134
      (KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
        (quotientClass 1 theta) a) = _ at hm
    have ha:=qb.sphere_action 1 (by decide) 62 64 63 70 theta a
    change KIP126.AdamsSynthetic.algebraProduct (algebra.quotients.algebra 1 (by decide))
      (quotientClass 1 theta) a=sphereAction theta a at ha
    rw [ha] at hm
    change D'.sphereFirstQuotient 9 134 (sphereAction theta a) =
      Sphere.Internal.product H M' (s:=2) (t:=64) (s':=7) (t':=70)
        (D'.sphereFirstQuotient 2 64 (quotientClass 1 theta))
        (D'.sphereFirstQuotient 7 70 a) at hm
    rw [hm,show D'.sphereFirstQuotient 2 64 (quotientClass 1 theta)=Sphere.Internal.hiSquare H M' 5 from htheta]
    exact hall _
  have theta_b_left_indeterminacy_normalize
      (coh:BiShiftCoherence Syn) (theta:BiHom 62 64 (S_0_0:Syn))
      {W:Syn} (y:(Smn (Syn:=Syn) 62 70)⟦(1:ℤ)⟧⟶W) :
      (tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70).hom≫
        ((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y =
      sphereAction theta
        ((SyntheticCategory.biShift_comp (62,70) (1,0)).inv.app (S_0_0:Syn)≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (Smn 62 70)≫y) := by
    have hc:=coh.associativity (62,64) (62,70) (1,0) (124,134) (63,70) (125,134)
      (by decide) (by decide) (by decide) (by decide) (S_0_0:Syn)
    have hi :
        ((SyntheticCategory.biShift (1,0)).mapIso
          ((SyntheticCategory.biShift_comp (62,64) (62,70)).app (S_0_0:Syn))) ≪≫
          (SyntheticCategory.biShift_comp (124,134) (1,0)).app (S_0_0:Syn) =
        (SyntheticCategory.biShift_comp (62,70) (1,0)).app (Smn (Syn:=Syn) 62 64) ≪≫
          (SyntheticCategory.biShift_comp (62,64) (63,70)).app (S_0_0:Syn) := by
      apply Iso.ext
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn,Functor.mapIso_hom,Iso.app_hom] using hc
    have hinv:=congrArg (fun e=>e.inv) hi
    simp only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] at hinv
    have hn:=(SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.naturality
      ((SyntheticCategory.biShift (62,70)).map theta)
    have hn':=(SyntheticCategory.biShift_comp (Syn:=Syn) (62,70) (1,0)).inv.naturality theta
    change ((SyntheticCategory.biShift_comp (124,134) (1,0)).inv.app (S_0_0:Syn) ≫
      (SyntheticCategory.biShift (1,0)).map
        ((SyntheticCategory.biShift_comp (62,64) (62,70)).inv.app (S_0_0:Syn)) ≫
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app
        ((SyntheticCategory.biShift (62,70)).obj (Smn 62 64))) ≫
      ((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y =
      (SyntheticCategory.biShift_comp (62,64) (63,70)).inv.app (S_0_0:Syn) ≫
        (SyntheticCategory.biShift (63,70)).map theta≫
        (SyntheticCategory.biShift_comp (62,70) (1,0)).inv.app (S_0_0:Syn)≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (Smn 62 70)≫y
    have hny:=congrArg (fun z=>z≫y) hn
    simp only [Category.assoc] at hny
    simp only [Category.assoc]
    rw [←hny]
    simp only [←Category.assoc]
    rw [hinv]
    simpa only [Category.assoc,Functor.comp_map,Prod.mk_add_mk,Int.reduceAdd,Smn] using congrArg (fun z =>
      (SyntheticCategory.biShift_comp (62,64) (63,70)).inv.app (S_0_0:Syn) ≫ z ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (Smn 62 70) ≫ y) hn'.symm
  have theta_b_quotient_toda_unique {D' : AdamsComparison H M' Syn}
      {L':SphereAdamsClasses H} {G:TmfDetectionClasses H} (I':AdamsComputationTheorems D' L' G) (synthetic:SyntheticComparisonTheorems D')
      (algebra:AdamsAlgebraStructures D') (qb:QuotientAlgebraCompatibility D' algebra) (ab:AlgebraDetectionCompatibility D' algebra)
      (theta:BiHom 62 64 (S_0_0:Syn)) (htheta:ThetaChoice M' D'.toAdamsComparisonData theta)
      (b:BiHom 62 70 (S_0_0:Syn))
      (hall:∀a:E2 H SphereSpectrum 7 70,
        Sphere.Internal.product H M' (s:=2) (t:=64) (s':=7) (t':=70) (Sphere.Internal.hiSquare H M' 5) a=0)
      (qz qz' : ((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=Syn) 62 64))⟦(1:ℤ)⟧⟶
        XModLambdaN (S_0_0:Syn) 1)
      (hz:Toda.Relation qz ((SyntheticCategory.biShift (62,70)).map theta)
        (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b))
      (hz':Toda.Relation qz' ((SyntheticCategory.biShift (62,70)).map theta)
        (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b)) : qz=qz' := by
    let src:=tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70
    obtain ⟨y,z,he⟩ := Toda.indeterminacy_complete hz hz'
    apply (cancel_epi src.hom).mp
    apply (D'.sphereFirstQuotient 9 134).injective
    apply sub_eq_zero.mp
    rw [←map_sub,←Preadditive.comp_sub,he,Preadditive.comp_add,map_add]
    have hy : D'.sphereFirstQuotient 9 134
        (src.hom≫((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y)=0 := by
      rw [theta_b_left_indeterminacy_normalize D'.shiftCoherence theta y]
      exact theta_b_left_indeterminacy_first_zero algebra qb ab theta htheta hall _
    let c:BiHom 63 64 (S_0_0:Syn) :=
      (susp_invariance 63 64 62 70 (S_0_0:Syn)).symm (src.hom≫z)
    have hc : (SyntheticCategory.biShift_comp (63,64) (62,70)).inv.app (S_0_0:Syn)≫
        (SyntheticCategory.biShift (62,70)).map c=src.hom≫z := by
      have hcc : susp_invariance 63 64 62 70 (S_0_0:Syn) c=src.hom≫z :=
        (susp_invariance 63 64 62 70 (S_0_0:Syn)).apply_symm_apply (src.hom≫z)
      dsimp only [susp_invariance] at hcc
      simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
        Iso.homCongr_apply,Iso.refl_hom,Category.comp_id] at hcc
      exact hcc
    have hright:src.hom≫(z≫quotientClass 1 b)=quotientClass 1 (sphereProduct c b) := by
      unfold sphereProduct quotientClass
      rw [←Category.assoc,←hc]
      simp only [Category.assoc]
    rw [hright,theta_b_right_indeterminacy_first_zero I' synthetic algebra qb ab c b,add_zero]
    exact hy
  have synthetic_theta_b_bracket_nonempty
      (coh : BiShiftCoherence Syn)
      (theta : BiHom 62 64 (S_0_0 : Syn)) (b : BiHom 62 70 (S_0_0 : Syn))
      (htheta : theta+theta=0) (hb : b+b=0) :
      ∃ z : BiHom 125 134 (S_0_0 : Syn), TripleToda theta syntheticTwo b z := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (62,70)
    let f := F.map theta
    let g := (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0:Syn) ≫ F.map syntheticTwo
    have hg : g=2 • 𝟙 (Smn 62 70 : Syn) := by
      have hc := coh.left_unit (62,70) (S_0_0:Syn)
      change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _=_ at hc
      have he : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0:Syn)=
          F.map (SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn)) := by
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,F] using hc
      dsimp only [g,syntheticTwo]
      rw [Functor.map_comp,←he,←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
      simp only [Functor.map_nsmul]
      change 2 • F.map (𝟙 (S_0_0 : Syn)) = 2 • 𝟙 (F.obj (S_0_0 : Syn))
      rw [CategoryTheory.Functor.map_id]
    have hfg : f≫g=0 := by
      rw [hg]
      simp only [two_smul,Preadditive.comp_add]
      erw [Category.comp_id]
      change F.map theta+F.map theta=0
      rw [←Functor.map_add,htheta,Functor.map_zero]
    have hgb : g≫b=0 := by
      rw [hg]
      simp only [two_smul,Preadditive.add_comp]
      erw [Category.id_comp]
      exact hb
    obtain ⟨v,hv⟩ := Toda.exists_relation f g b hfg hgb
    refine ⟨(tripleTodaSource 62 64 0 0 62 70).hom≫v,?_⟩
    unfold TripleToda
    rw [Iso.inv_hom_id_assoc]
    exact hv
  have sphere_permanent_first_quotient_lift {D' : AdamsComparison H M' Syn}
      (synthetic : SyntheticComparisonTheorems D') (s t : ℤ) (x : E2 H SphereSpectrum s t)
      (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x) :
      ∃ a : BiHom (t-s) t (S_0_0 : Syn), D'.sphereFirstQuotient s t (quotientClass 1 a)=x := by
    have hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := by
      exact hx
    obtain ⟨a,ha⟩ := (synthetic.permanent_lift .sphere s t x).mp hp
    let e := SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum) ≫ D'.nu.unitIso.hom
    refine ⟨a≫e,?_⟩
    have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
      unfold quotientClass
      simp only [Category.assoc]
      exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
    rw [hc,ha]
    exact sphere_first_label_transport s t x
  have b_permanent_from_inputs {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (V : SphereVanishingLine H) :
      IsPermanentCycle (sequence D' .sphere) (8,70) (I'.interpretation.sphere 8 70 B) := by
    have bLabel : I'.interpretation.sphere 8 70 (B) = I'.interpretation.basis .sphere 8 70 1 := by
      have hc := I'.monomials (⟨.sphere, 8, 70, ["83,1", "82,1", "0,6,18,2"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 155 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (1:Fin 3)
      have heq : (B)=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨82,by decide⟩ = projection (monomialOfString "82,1")
        have hp : (("82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [82,1] := by
          have hs : "82,1".splitOn "," = ["82","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [hs]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        norm_num [monomialOfString,show "82,1"≠"" by decide,hp,polynomialOfPowers,
          RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
      rw [heq]
      exact he
    rw [bLabel]
    apply permanent_cycle_of_reaches1000 V 8 70 (by norm_num) (by norm_num)
    have hrow := I'.adamsStatements ⟨.sphere, .reaches, 1000, 8, 70, [1], 8, 70, [], "S0_AdamsE2_ss", 509⟩ (by
      unfold Raw.claims
      iterate 193 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 70 [1]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at h
    exact h
  have synthetic_theta_b_first_label_bracket {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      {etaThetaB : BiHom 1 2 (S_0_0 : Syn)}
      (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D' etaThetaB G)
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (V : SphereVanishingLine H)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (htheta : ThetaChoice M' D'.toAdamsComparisonData theta) :
      ∃ (b : BiHom 62 70 (S_0_0 : Syn)) (z : BiHom 125 134 (S_0_0 : Syn)),
        D'.sphereFirstQuotient 8 70 (quotientClass 1 b) = I'.interpretation.sphere 8 70 B ∧
        TripleToda theta syntheticTwo b z := by
    obtain ⟨b,hb⟩ := sphere_permanent_first_quotient_lift A.synthetic 8 70
      (I'.interpretation.sphere 8 70 B) (b_permanent_from_inputs I' V)
    obtain ⟨z,hz⟩ := synthetic_theta_b_bracket_nonempty D'.shiftCoherence theta b
      (theta5_choice_order_two A I' theta htheta) (two_torsion_62_70 A I' V b)
    exact ⟨b,z,hb,hz⟩
  have family_map_data {D' : AdamsComparison H M' Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i = (D'.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D'.family.functor.map f).toSSDataMorphism
    let PX := (D'.family.functor.obj X).ssData i
    let PY := (D'.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D'.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D'.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D'.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D'.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _
  have family_page_comp {D' : AdamsComparison H M' Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i ≫ familyPageMap D'.family g r i = familyPageMap D'.family (f ≫ g) r i := by
    rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map {D' : AdamsComparison H M' Syn}
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D'.family.obj X).E₂ i) (e : ((D'.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D'.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D'.family.obj Y) 2 i
        (familyPageMap D'.family f 2 i y) ((D'.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D'.family.functor.obj X).ssData i).Z ⊤)
      (((D'.family.functor.obj X).ssData i).Z 0) _ ≫ ((D'.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D'.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D'.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D'.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  have sphere_quotient_label_to_nu {D' : AdamsComparison H M' Syn} (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k x) = finiteTargetLabel D' .sphere q s t k x := by
    let nx : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj
        (D'.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
      simpa only [ClassicalObject.obj,add_zero] using D'.nuE2 .sphere 0 s t k x
    let f := XModLambdaN.map D'.nu.unitIso.inv q
    have hbase : familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)=
        targetNuLabel D' .sphere s t k x := by
      have hc : familyPageMap D'.family
          (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k) nx =
          D'.sphereE2 s t k x := by
        convert D'.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
      calc
        _ = familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k)
            (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k)
              nx) := congrArg (fun y => familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
        _ = familyPageMap D'.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) ≫ D'.nu.unitIso.inv)
            2 (s,t,t-k) nx :=
          ConcreteCategory.congr_hom (family_page_comp (D':=D') (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
        _ = targetNuLabel D' .sphere s t k x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          dsimp only [targetNuLabel]
          congr 1
    have hlabel : familyPageMap D'.family f 2 (s,t,t-k) (D'.quotientLabel q s t k x)=
        finiteTargetLabel D' .sphere q s t k x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D'.nu.unitIso.inv q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp (D':=D') (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)) :=
          (ConcreteCategory.congr_hom (family_page_comp (D':=D') D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)).symm
        _ = finiteTargetLabel D' .sphere q s t k x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
    exact hlabel
  have finite_sphere_infinity_nonzero {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
      (e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
      (he : HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
        (D'.quotientLabel q s t 0 x) e) : e≠0 := by
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hh := family_infinity_representative_map g (s,t,t-0) _ _ he
    have hl := sphere_quotient_label_to_nu (D':=D') q 0 s t x
    change familyPageMap D'.family g 2 (s,t,t-0) (D'.quotientLabel q s t 0 x)=_ at hl
    rw [hl] at hh
    let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
      ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
    have hp := (BHS.labels.1 .sphere q hq (s,t) 0 hq y _).mp hh
    intro he0
    rw [he0,map_zero,map_zero] at hp
    have hm := (NestedQuotient.projection_eq_zero y).mp hp.symm
    have hb : (1:ℤ)+t-(t-0)=1 := by omega
    change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
    rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
    exact hne hm
  have sphere_zero_weight_nonzero_detection {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 8 70)
      (a : BiHom (70-8) 70 (S_0_0 : Syn))
      (ha : D'.sphereFirstQuotient 8 70 (quotientClass 1 a)=x) (hne : x≠0) :
      SphereDetected D' 8 70 0 x a := by
    have h0 : lambdaMultiply 0 a=a := by
      have hc := D'.shiftCoherence.right_unit (70-8,70) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (70-8,70) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn (70-8) 70 : Syn) := by
        change (biShiftAddIso (70-8,70) (0,0) (70-8,70) (by simp)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (70-8,70) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (70-8,70) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hd := D'.comparisonCompatible.homotopy_lambda 8 70 0 a
    rw [h0,ha] at hd
    refine ⟨hd,?_⟩
    obtain ⟨e,he,_⟩ := hd
    refine ⟨e,he,?_⟩
    let f := XModLambdaN.incl (S_0_0 : Syn) 1
    have hf := family_infinity_representative_map f (8,70,70-0) _ _ he
    have hcycle : x∈PageRepresentatives.cycles H SphereSpectrum 1 (8,70) := by
      rw [PageRepresentatives.cycles_one]
      exact Submodule.mem_top
    have hfn := finite_sphere_infinity_nonzero BHS 1 (by decide) 8 70 x hcycle hne _ hf
    intro hz
    apply hfn
    rw [hz,map_zero]
  have b_nonzero_from_inputs {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 8 70 B ≠ 0 := by
    have bLabel : I'.interpretation.sphere 8 70 (B) = I'.interpretation.basis .sphere 8 70 1 := by
      have hc := I'.monomials (⟨.sphere, 8, 70, ["83,1", "82,1", "0,6,18,2"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 155 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (1:Fin 3)
      have heq : (B)=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨82,by decide⟩ = projection (monomialOfString "82,1")
        have hp : (("82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [82,1] := by
          have hs : "82,1".splitOn "," = ["82","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [hs]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        norm_num [monomialOfString,show "82,1"≠"" by decide,hp,polynomialOfPowers,
          RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
      rw [heq]
      exact he
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,8,70,["83,1","82,1","0,6,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 155 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 8 70 ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 8 70 i.val at he
    have he1 : e.symm (Finsupp.single (1:Fin 3) 1)=I'.interpretation.basis .sphere 8 70 1 := he 1
    rw [bLabel,←he1]
    intro hz
    have hh := congrArg (fun z => e z (1:Fin 3)) hz
    simp at hh
  have synthetic_theta_b_detected_bracket {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      {etaThetaB : BiHom 1 2 (S_0_0 : Syn)}
      (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D' etaThetaB G)
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) (V : SphereVanishingLine H)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (htheta : ThetaChoice M' D'.toAdamsComparisonData theta) :
      ∃ (b : BiHom 62 70 (S_0_0 : Syn)) (z : BiHom 125 134 (S_0_0 : Syn)),
        SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b ∧
        TripleToda theta syntheticTwo b z := by
    obtain ⟨b,z,hb,hz⟩ := synthetic_theta_b_first_label_bracket A I' V theta htheta
    exact ⟨b,z,sphere_zero_weight_nonzero_detection A.synthetic.eInfty _ b hb
      (b_nonzero_from_inputs I'),hz⟩
  have sphere_zero_weight_nonzero_detection_9_134 {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 9 134)
      (a : BiHom (134-9) 134 (S_0_0 : Syn))
      (ha : D'.sphereFirstQuotient 9 134 (quotientClass 1 a)=x) (hne : x≠0) :
      SphereDetected D' 9 134 0 x a := by
    have h0 : lambdaMultiply 0 a=a := by
      have hc := D'.shiftCoherence.right_unit (134-9,134) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (134-9,134) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn (134-9) 134 : Syn) := by
        change (biShiftAddIso (134-9,134) (0,0) (134-9,134) (by simp)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (134-9,134) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (134-9,134) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hd := D'.comparisonCompatible.homotopy_lambda 9 134 0 a
    rw [h0,ha] at hd
    refine ⟨hd,?_⟩
    obtain ⟨e,he,_⟩ := hd
    refine ⟨e,he,?_⟩
    let f := XModLambdaN.incl (S_0_0 : Syn) 1
    have hf := family_infinity_representative_map f (9,134,134-0) _ _ he
    have hcycle : x∈PageRepresentatives.cycles H SphereSpectrum 1 (9,134) := by
      rw [PageRepresentatives.cycles_one]
      exact Submodule.mem_top
    have hfn := finite_sphere_infinity_nonzero BHS 1 (by decide) 9 134 x hcycle hne _ hf
    intro hz
    apply hfn
    rw [hz,map_zero]
  have h6b_nonzero_from_inputs {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
      Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
        (Sphere.Internal.hi H M' 6) (I'.interpretation.sphere 8 70 B) ≠ 0 := by
    have hbLabel : I'.interpretation.sphere 9 134 (mulAt dataH6 B) = I'.interpretation.basis .sphere 9 134 2 := by
      have hc := I'.monomials (⟨.sphere, 9, 134, ["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 173 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
      have heq : (mulAt dataH6 B)=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨69,by decide⟩*generator ⟨82,by decide⟩ = projection (monomialOfString "69,1,82,1")
        have hp : (("69,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1,82,1] := by
          have hs : "69,1,82,1".splitOn "," = ["69","1","82","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [hs]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        norm_num [monomialOfString,show "69,1,82,1"≠"" by decide,hp,polynomialOfPowers,
          RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
      rw [heq]
      exact he
    have hprod := I'.products ⟨1,64,8,70⟩ (by simp [Raw.products]) dataH6 B
    rw [I'.distinguishedClasses.h6] at hprod
    change I'.interpretation.sphere 9 134 (mulAt dataH6 B)=_ at hprod
    rw [←hprod,hbLabel]
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,9,134,["391,1","390,1","69,1,82,1","18,1,190,1","0,1,375,1"]⟩ (by
      unfold Raw.degrees
      iterate 173 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 9 134 ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 9 134 i.val at he
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1)=I'.interpretation.basis .sphere 9 134 2 := he 2
    rw [←he2]
    intro hz
    have hh := congrArg (fun z => e z (2:Fin 5)) hz
    simp at hh
  have theta_b_bracket_label_suffices {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
      (A : SyntheticComparisonTheorems D') (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (b : BiHom 62 70 (S_0_0 : Syn)) (z : BiHom 125 134 (S_0_0 : Syn))
      (hb : SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b)
      (htoda : TripleToda theta syntheticTwo b z)
      (hz : D'.sphereFirstQuotient 9 134 (quotientClass 1 z)=
        Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
          (Sphere.Internal.hi H M' 6) (I'.interpretation.sphere 8 70 B)) :
      SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b ∧
      SphereDetected D' 9 134 0
        (Sphere.Internal.product H M' (s:=1) (t:=64) (s':=8) (t':=70)
          (Sphere.Internal.hi H M' 6) (I'.interpretation.sphere 8 70 B)) z ∧
      TripleToda theta syntheticTwo b z := by
    exact ⟨hb,sphere_zero_weight_nonzero_detection_9_134 A.eInfty _ z hz
      (h6b_nonzero_from_inputs I'),htoda⟩
  obtain ⟨b,z,hb,hz⟩:=synthetic_theta_b_first_label_bracket A I' V theta htheta
  obtain ⟨q,hq,hql⟩:=theta_b_algebra_toda_candidate I' algebra qb ab A.may.toMayContext
    (zero_hom_nonzero_unique D' zero_nonzero_unique) A.toda.h0 theta A.toda.h0_label
    htheta A.toda.lambda_h0 (theta5_choice_order_two A I' theta htheta) b
  let src:=tripleTodaSource (Syn:=Syn) 62 64 0 0 62 70
  let F:=SyntheticCategory.biShift (Syn:=Syn) (62,70)
  have hg : (SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0:Syn)≫F.map syntheticTwo=
      2 • 𝟙 (Smn (Syn:=Syn) 62 70) := by
    have hc := D'.shiftCoherence.left_unit (62,70) (S_0_0:Syn)
    change (biShiftAddIso (0,0) (62,70) (62,70) (by decide)).hom.app _=_ at hc
    have he : (SyntheticCategory.biShift_comp (0,0) (62,70)).hom.app (S_0_0:Syn)=
        F.map (SyntheticCategory.biShift_zero.hom.app (S_0_0:Syn)) := by
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,F] using hc
    dsimp only [syntheticTwo]
    rw [Functor.map_comp,←he,←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    simp only [Functor.map_nsmul]
    change 2 • F.map (𝟙 (S_0_0 : Syn)) = 2 • 𝟙 (F.obj (S_0_0 : Syn))
    rw [CategoryTheory.Functor.map_id]
  have hzr:Toda.Relation (src.inv≫quotientClass 1 z) (F.map theta)
      (2 • 𝟙 (Smn (Syn:=Syn) 62 70)) (quotientClass 1 b) := by
    have ht:=hz
    change Toda.Relation (src.inv≫z) (F.map theta)
      ((SyntheticCategory.biShift_comp (0,0) (62,70)).inv.app (S_0_0:Syn)≫F.map syntheticTwo) b at ht
    rw [hg] at ht
    simpa only [quotientClass,Category.assoc] using Toda.postcompose ht (XModLambdaN.incl (S_0_0:Syn) 1)
  have hqz:quotientClass 1 z=q := by
    apply (cancel_epi src.inv).mp
    exact theta_b_quotient_toda_unique I' A.synthetic algebra qb ab theta htheta b hall _ _ hzr hq
  refine ⟨b,z,?_⟩
  apply theta_b_bracket_label_suffices A.synthetic I' theta b z
    (sphere_zero_weight_nonzero_detection A.synthetic.eInfty _ b hb (b_nonzero_from_inputs I')) hz
  rw [hqz,hql,hb]


end
end ThetaBSyntheticProof

/-- `lem:toda2ext`: a compatible synthetic bracket MEMBER and its actual
nonzero detector must be produced, not inferred from order two alone.
The proof constructs a bracket member using the synthetic λ cofiber,
May's multiplicative comparison and quotient Toda uniqueness, then proves
its detection from the low-degree sphere computations. -/
theorem synthetic_theta_b_toda
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice M (D).toAdamsComparisonData theta) :
    ∃ (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
      (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn)),
      SphereDetected D 8 70 0 eB b ∧ SphereDetected D 9 134 0 eH6B z ∧
      TripleToda theta syntheticTwo b z := by
  exact theta_b_complete_from_low_degrees literatureTheorems I sphereVanishing
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.quotientCompatibility
    literature.sources.sourceComparisons.algebraDetectionCompatibility
    (KIP126.Main.Computation.sphere_zero_nonzero_unique KIP126.Main.externalHypotheses)
    (h5_square_times_entire_770_zero I) theta htheta


end
end KIP126.Main.SectionSeven
