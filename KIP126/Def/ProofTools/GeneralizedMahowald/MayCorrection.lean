module
import all KIP126.Def.ProofTools.StretchingRepresentatives
import all KIP126.Def.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.GeneralizedMahowald.Signs
import all KIP126.Def.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.Def.ProofTools.GeneralizedMahowald.CommonShiftEdge
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingLabels

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/- A classical q-cycle need not lift to nu Y. Its image under this actual
map nevertheless becomes permanent because the outgoing target groups
vanish from page q+1 onward. This is the window needed for the octahedral
defect d after conjugating the common suspension/weight shift. -/
private theorem finite_cycle_image_infinity
    (Y X : ClassicalObject) (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (a b s t : ℤ) (hgap : (r:ℤ) ≤ q+b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶
      XModLambdaN ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r)
    (y : Ambient model Y (s,t)) (hy : y ∈ cycles model Y q (s,t)) :
    ∃ e, HasInfinityRepresentative
      (model.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r)) 2 (s,t,t+a-(0:ℕ))
      (familyPageMap model.family d 2 (s,t,t+a-(0:ℕ))
        (model.comparison.nuE2 Y a s t 0 y)) e := by
  let E := model.classical.obj (Y.obj model.auxiliary)
  have hpage : 2 ≤ (q+1:ℕ) := by omega
  have hy' : ReachesPage E (q+1) (s,t) y := by
    apply (isCycle_iff_reaches model Y (q+1) (by omega) (s,t) y).mp
    refine ⟨by omega,?_⟩
    simpa using hy
  obtain ⟨yr,hyr⟩ := hy'
  have hdeg : (s,t)+E.diffDeg (q+1:ℕ) = (s+(q+1:ℕ),t+(q+1:ℕ)-1) := by
    rw [model.classical.differentialDegree]
    ext <;> first | rfl | (dsimp; omega)
  let zr := (E.d (q+1:ℕ) (s,t) ≫ eqToHom (congrArg (E.Page (q+1:ℕ)) hdeg)) yr
  obtain ⟨z,hz⟩ := FinitePageCalculus.page_has_initial_representative (by omega : (2:ℤ)≤(q+1:ℕ)) zr
  have hc : HasDifferential E (q+1:ℕ) (s,t) (s+(q+1:ℕ),t+(q+1:ℕ)-1) y z :=
    ⟨hdeg,yr,zr,hyr,hz,rfl⟩
  obtain ⟨_,ys,zs,hys,hzs,hds⟩ :=
    (KIP126.Literature.Standard.bhs_differentials Y a s t (q+1) 0 hpage y z).mp hc
  have hm := syntheticRep_map (model.family.map d) hys
  apply syntheticRep_infty _ (q+1:ℕ) (s,t,t+a-(0:ℕ)) _ _ hm
  intro n hn
  have hdeg' : (s,t,t+a-(0:ℕ))+(model.family.obj (XModLambdaN
      ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r)).sequence.diffDeg n =
      (s+n,t+n-1,t+a-(0:ℕ)) := by
    change (s,t,t+a-(0:ℕ)) + (model.family.functor.obj _).diffDeg n = _
    rw [model.family.differentialDegree]
    simp only [syntheticAdamsRawShift,Prod.mk_add_mk,add_zero]
    ext <;> first | rfl | (dsimp; omega)
  have hs := shiftedFinitePageVanishing X r hr b n (s+n) (t+n-1) (t+a-(0:ℕ))
    (by omega) (Or.inr (by omega))
  have hsub : Subsingleton ((model.family.obj (XModLambdaN
      ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r)).Page n
      ((s,t,t+a-(0:ℕ))+(model.family.obj (XModLambdaN
        ((SyntheticCategory.biShift (0,b)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) r)).sequence.diffDeg n)) := by
    rw [hdeg']
    exact hs
  ext v
  exact @Subsingleton.elim _ hsub _ _

private theorem finite_cycle_image_correction
    (Y X : ClassicalObject) (q r i : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hi : 0 < i) (hir : i ≤ r)
    (a b s t : ℤ) (hgap : (r:ℤ) ≤ q+b-a) (hkill : (i:ℤ) ≤ b-a)
    (d : (SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶
      XModLambdaN ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r)
    (y : Ambient model Y (s,t)) (hy : y ∈ cycles model Y q (s,t)) :
    ∃ c : BiHom (t-s) (t+a-(0:ℕ)) (XModLambdaN ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) r),
      Detects (model.convergence (.quotient r (.shift (0,b) (.nu X)))) (s,t,t+a-(0:ℕ))
        (familyPageMap model.family d 2 (s,t,t+a-(0:ℕ))
          (model.comparison.nuE2 Y a s t 0 y)) c ∧
      c ≫ (model.quotients.tower ((SyntheticCategory.biShift (0,b)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).rho i r hir = 0 := by
  obtain ⟨e,he⟩ := finite_cycle_image_infinity Y X q r hq hr a b s t hgap d y hy
  let A : SyntheticObject := .quotient r (.shift (0,b) (.nu X))
  let B : SyntheticObject := .quotient i (.shift (0,b) (.nu X))
  let F := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  haveI : Epi (F.toAssociatedGraded s (t-s,t+a-(0:ℕ))) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t+a-(0:ℕ)))).mp
    inferInstance (((model.convergence A).identification (s,t,t+a-(0:ℕ))).hom e)
  let c' := (F.F s (t-s,t+a-(0:ℕ))).arrow c
  have hdetect : Detects (model.convergence A) (s,t,t+a-(0:ℕ)) _ c' := ⟨e,he,c,rfl,hc.symm⟩
  refine ⟨c',hdetect,?_⟩
  let rho := (model.quotients.tower ((SyntheticCategory.biShift (0,b)).obj
    (model.nu.functor.obj (X.obj model.auxiliary)))).rho i r hir
  have hfilc : FiltrationAtLeast model.syntheticTower s c' := by
    have hmem : c' ∈ ModuleCat.subobjectModule _ (F.F s (t-s,t+a-(0:ℕ))) := ⟨c,rfl⟩
    simpa only [F,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  have hfil : FiltrationAtLeast model.syntheticTower s (c'≫rho) :=
    map_preserves_filtration (model.convergentMap A B rho) (t-s,t+a-(0:ℕ)) s c'
      hfilc
  apply synthetic_homotopy_separated B (t-s) (t+a-(0:ℕ)) (c'≫rho)
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero (model.convergence B) s j (t-s) (t+a-(0:ℕ)) hj
      (fun k hk _ => shifted_quotient_eInfty_zero X i hi b k (t-s+k) (t+a-(0:ℕ)) (by omega))
        (c'≫rho)).mp hfil
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t+a-(0:ℕ)) (by omega) hfil


/-- Apply the image correction in the exact common-desuspended degrees of MH2.
The finite g witness supplies the required q-cycle without permanent-cycle
assumptions. The weight gap is i+ef, including ef=0. -/
private theorem mh2_actual_defect_correction
    (X Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (q i : ℕ) (hq : 0 < q) (hi : 0 < i)
    (ef m s t : ℤ) (hef : 0 ≤ ef)
    (y : Ambient model Y (s,t)) (yBar : Ambient model Z (s+m,t+m))
    (Wg : FiniteExtensionWitness model Y Z g (q+1) m s t y yBar)
    (d₀ : (extensionSourceObject model Y Z g).obj model.nu model.auxiliary ⟶
      XModLambdaN ((SyntheticCategory.biShift
        (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (i+q)) :
    ∃ cd : BiHom (t-s) (t+normalizedExponent model.classicalTower g-(0:ℕ))
        (XModLambdaN ((SyntheticCategory.biShift
          (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (i+q)),
      Detects (model.convergence (.quotient (i+q)
        (.shift (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g) (.nu X))))
        (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ))
        (familyPageMap model.family d₀ 2
          (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ))
          (model.comparison.nuE2 Y (normalizedExponent model.classicalTower g) s t 0 y)) cd ∧
      cd ≫ (model.quotients.tower ((SyntheticCategory.biShift
        (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).rho i (i+q) (by omega) = 0 := by
  have hy : y ∈ cycles model Y q (s,t) := by
    have hsource : ReachesPage (model.classical.obj (Y.obj model.auxiliary))
        ((q:ℤ)+1) (s,t) y := by
      simpa only [Nat.cast_add,Nat.cast_one] using Wg.source_cycle
    have h := (isCycle_iff_reaches model Y ((q:ℤ)+1) (by omega) (s,t) y).mpr hsource
    simpa only [add_sub_cancel_right] using h.2
  exact finite_cycle_image_correction Y X q (i+q) i hq (by omega) hi (by omega)
    (normalizedExponent model.classicalTower g)
    ((i:ℤ)+ef+normalizedExponent model.classicalTower g) s t
    (by omega) (by omega) d₀ y hy

/-- The positive-length Toda residual vanishes on the prescribed source y,
without identifying any λ-preimage of its finite extension image. -/
private theorem positive_extension_postcompose_e2_zero
    (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (r : ℕ) (m s t : ℤ) (hm : 0<m)
    (y : Ambient model Y (s,t)) (yBar : Ambient model Z (s+m,t+m))
    (Wg : FiniteExtensionWitness model Y Z g r m s t y yBar)
    (D : SyntheticSpectrum) (t₀ : model.nu.functor.obj (Z.obj model.auxiliary) ⟶ D) :
    familyPageMap model.family ((model.normalizedMap Y Z g).map ≫ t₀) 2
      (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
      (infiniteSourceForExtension model Y Z g s t y) = 0 := by
  rw [← family_page_comp,ModuleCat.comp_apply,
    positive_extension_map_e2_zero Y Z g r m s t hm y yBar Wg,map_zero]

/- This is the exact residual t₀ constructed in CommonShiftEdge. Its lower
weight transpose factors through the original lambda_i, without requiring
any equality between arbitrary choices of shift comparison. -/
private theorem common_desuspended_residual_transpose
    {B D₀ E U : SyntheticSpectrum} (i : ℕ)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀)
    (epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj D₀ ≅ E)
    (t : B⟦(1:ℤ)⟧ ⟶ U) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let t₀ : B ⟶ D₀ := ff.preimage ((biSuspensionIso (i:ℤ) B).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i B) ≫ t ≫ eD.hom)
    ∃ z : B ⟶ E,
      (SyntheticCategory.biShift (0,-(i:ℤ))).map t₀ ≫ epsilon.hom =
        lambdaPow i B ≫ z := by
  dsimp only
  let sf := Functor.FullyFaithful.ofFullyFaithful (shiftFunctor SyntheticSpectrum (1:ℤ))
  let z : B ⟶ E := sf.preimage (t ≫ eD.hom ≫
    (biSuspensionIso (i:ℤ) D₀).hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map epsilon.hom)
  refine ⟨z,?_⟩
  apply sf.map_injective
  simp only [Functor.map_comp, z, Functor.FullyFaithful.map_preimage]
  apply (cancel_epi (biSuspensionIso (i:ℤ) B).hom).mp
  simp only [←Category.assoc]
  rw [←biSuspensionIso_natural]
  simp only [Category.assoc,Functor.FullyFaithful.map_preimage]

/- The q=1 (zero-length g-extension) residual is allowed to have a
nonzero E2 label. Its actual transposed lambda_i map kills the infinity
class because the prescribed differential target lies in B_(i+1). -/
private theorem boundary_transposed_lambda_infinity_zero
    (X : ClassicalObject) (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (y : Ambient model X (s,t))
    (e : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,t)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel model X s t t (by omega) y) e)
    (hy : y ∈ boundaries model X (i+1) (s,t))
    (D : SyntheticObject)
    (h : model.nu.functor.obj (X.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift (0,(i:ℤ))).obj (D.obj model.nu model.auxiliary))
    (epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (0,(i:ℤ))).obj (D.obj model.nu model.auxiliary)) ≅
      D.obj model.nu model.auxiliary)
    (z : model.nu.functor.obj (X.obj model.auxiliary) ⟶ D.obj model.nu model.auxiliary)
    (hh : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ epsilon.hom =
      lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary)) ≫ z) :
    (model.family.map h).eInftyMap (s,t,t) e = 0 := by
  obtain ⟨hyp,heq⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y e).mp he
  have hzero : KIP126.Literature.Standard.infinityLambda (.nu X) i (s,t) t e = 0 := by
    apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) (t-i) (by omega)).injective
    rw [map_zero,KIP126.Literature.Standard.eInfinity_lambda_nu X i (s,t) t (by omega),heq]
    change subquotientClass (permanentCycles model X (s,t))
      (boundaries model X (1+t-(t-i)) (s,t)) ⟨y,hyp⟩ = 0
    apply (CrossingLabels.subquotient_zero_iff _ _ _).mpr
    convert hy using 1
    congr 1
    omega
  apply (weight_shift_lower_kernel_via_transpose (.nu X)
    (.shift (0,(i:ℤ)) D) D i (s,t) t h epsilon
      (lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary)) ≫ z) hh e).mp
  have hcomp := ConcreteCategory.congr_hom
    (SpectralSequenceMorphism.eInftyMap_comp
      (model.family.map (lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary))))
      (model.family.map z) (s,t,t-i))
    ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison (.nu X) i (s,t) t).hom e)
  rw [←SyntheticAdamsFamily.map_comp] at hcomp
  refine hcomp.trans ?_
  change (model.family.map z).eInftyMap (s,t,t-i)
    ((model.family.map (lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
      (s,t,t-i) ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison (.nu X) i (s,t) t).hom e)) = 0
  have hl : (model.family.map (lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
      (s,t,t-i)
      ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison (.nu X) i (s,t) t).hom e) = 0 := by
    simpa only [KIP126.Literature.Standard.infinityLambda,InfinityShiftCoordinates.lambdaMap,
      dif_neg (Nat.ne_of_gt hi),KIP126.Literature.Standard.infinityShiftData,
      InfinityShiftCoordinates.shift,ModuleCat.comp_apply,SyntheticObject.obj] using hzero
  rw [hl,map_zero]


/- A length-r differential target belongs to the paper's B_r, not merely
B_(r+1). This indexing is essential for q=1, where r=i+1. -/
private theorem differential_target_boundary (X : ClassicalObject)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ × ℤ)
    (x : Ambient model X p) (y : Ambient model X q)
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary)) r p q x y) :
    y ∈ boundaries model X r q := by
  have hlater := FinitePageCalculus.differential_target_later_zero
    (t := r+1) (by rw [model.classical.firstPage]; exact hr) (by omega) hd
  have hb := represents_zero_mem_boundary model X (r+1) q y hlater
  simpa only [add_sub_cancel_right] using hb

/- The q=1 residual lemma now consumes the actual MH2 differential and
permanence premises, rather than an extra boundary-membership assumption. -/
private theorem zero_length_differential_residual_zero
    (X : ClassicalObject) (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (p : ℤ×ℤ) (x : Ambient model X p) (y : Ambient model X (s,t))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (i+1) p (s,t) x y)
    (hy : y ∈ permanentCycles model X (s,t))
    (D : SyntheticObject)
    (h : model.nu.functor.obj (X.obj model.auxiliary) ⟶
      (SyntheticCategory.biShift (0,(i:ℤ))).obj (D.obj model.nu model.auxiliary))
    (epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (0,(i:ℤ))).obj (D.obj model.nu model.auxiliary)) ≅
      D.obj model.nu model.auxiliary)
    (z : model.nu.functor.obj (X.obj model.auxiliary) ⟶ D.obj model.nu model.auxiliary)
    (hh : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ epsilon.hom =
      lambdaPow i (model.nu.functor.obj (X.obj model.auxiliary)) ≫ z) :
    ∃ e, HasInfinityRepresentative _ 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) y) e ∧
      (model.family.map h).eInftyMap (s,t,t) e = 0 := by
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (permanentCycles model X (s,t))
      (boundaries model X (1+t-t) (s,t)) ⟨y,hy⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) y) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y e).mpr
    exact ⟨hy,AddEquiv.apply_symm_apply _ _⟩
  refine ⟨e,he,?_⟩
  exact boundary_transposed_lambda_infinity_zero X i hi s t y e he
    (differential_target_boundary X (i+1) (by omega) p (s,t) x y hd) D h epsilon z hh


/- At m=0 the exact Gt₀ E₂ label can be nonzero. The actual raw t₀ carries
lambda_i, so the specified differential target makes this residual detect
zero. This is the form needed to remove it from a second-image detection. -/
private theorem zero_length_actual_toda_residual_detects_zero
    (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (r i : ℕ) (hi : 0 < i) (s t : ℤ)
    (y : Ambient model Y (s,t)) (yBar : Ambient model Z (s+0,t+0))
    (Wg : FiniteExtensionWitness model Y Z g r 0 s t y yBar)
    (p : ℤ×ℤ) (xBar : Ambient model Z p)
    (hd : HasDifferential (model.classical.obj (Z.obj model.auxiliary))
      (i+1) p (s+0,t+0) xBar yBar)
    (hyBar : yBar ∈ permanentCycles model Z (s+0,t+0))
    (D : SyntheticObject) (U : SyntheticSpectrum)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj
      ((SyntheticObject.shift (0,(i:ℤ)) D).obj model.nu model.auxiliary))
    (epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticObject.shift (0,(i:ℤ)) D).obj model.nu model.auxiliary) ≅
      D.obj model.nu model.auxiliary)
    (raw : (model.nu.functor.obj (Z.obj model.auxiliary))⟦(1:ℤ)⟧ ⟶ U) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
        (model.nu.functor.obj (Z.obj model.auxiliary))).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (lambdaPow i (model.nu.functor.obj (Z.obj model.auxiliary))) ≫ raw ≫ eD.hom)
    Detects (model.convergence (.shift (0,(i:ℤ)) D)) (s+0,t+0,t+0)
      (familyPageMap model.family ((model.normalizedMap Y Z g).map ≫ t₀) 2 (s+0,t+0,t+0)
        (regradeE2 (by have := Wg.length_lower; ext <;> dsimp <;> omega)
          (infiniteSourceForExtension model Y Z g s t y))) 0 := by
  dsimp only
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
      (model.nu.functor.obj (Z.obj model.auxiliary))).hom ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (lambdaPow i (model.nu.functor.obj (Z.obj model.auxiliary))) ≫ raw ≫ eD.hom)
  obtain ⟨z,hz⟩ := common_desuspended_residual_transpose i eD epsilon raw
  obtain ⟨e,he,hzero⟩ := zero_length_differential_residual_zero Z i hi (s+0) (t+0)
    p xBar yBar hd hyBar D t₀ epsilon z hz
  have hrep := family_infinity_representative_map t₀ (s+0,t+0,t+0)
    (nuWeightLabel model Z (s+0) (t+0) (t+0) (by omega) yBar) e he
  have hrep0 : HasInfinityRepresentative _ 2 (s+0,t+0,t+0)
      (familyPageMap model.family t₀ 2 (s+0,t+0,t+0)
        (nuWeightLabel model Z (s+0) (t+0) (t+0) (by omega) yBar)) 0 := by
    exact hzero ▸ hrep
  have hlabel := zero_extension_map_e2_bottom_target Y Z g r s t y yBar Wg
  have hlabel' := congrArg (fun v => familyPageMap model.family t₀ 2 (s+0,t+0,t+0) v) hlabel
  rw [←ModuleCat.comp_apply,family_page_comp] at hlabel'
  have hrep' : HasInfinityRepresentative _ 2 (s+0,t+0,t+0)
      (familyPageMap model.family ((model.normalizedMap Y Z g).map ≫ t₀) 2 (s+0,t+0,t+0)
        (regradeE2 (by have := Wg.length_lower; ext <;> dsimp <;> omega)
          (infiniteSourceForExtension model Y Z g s t y))) 0 := by
    rw [hlabel']
    exact hrep0
  exact ⟨0,hrep',0,by simp,by simp⟩


/- Subtract the actual d₀ correction from the same actual May lift. This
retains its first rho_i image and records the exact change in the detected
second image. No assertion about Jedge or additive functoriality is used. -/
private theorem mh2_actual_defect_subtraction
    (X Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (q i : ℕ) (hq : 0 < q) (hi : 0 < i)
    (ef m s t : ℤ) (hef : 0 ≤ ef)
    (y : Ambient model Y (s,t)) (yBar : Ambient model Z (s+m,t+m))
    (Wg : FiniteExtensionWitness model Y Z g (q+1) m s t y yBar)
    (D : SyntheticObject) :
    let a : ℤ := normalizedExponent model.classicalTower g
    let b : ℤ := (i:ℤ)+ef+a
    let C := SyntheticObject.quotient (i+q) (.shift (0,b) (.nu X))
    ∀ (d₀ : (extensionSourceObject model Y Z g).obj model.nu model.auxiliary ⟶
        C.obj model.nu model.auxiliary)
      (h₀ : C.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
      (c : BiHom (t-s) (t+a-(0:ℕ)) (C.obj model.nu model.auxiliary))
      (beta : (model.family.obj (D.obj model.nu model.auxiliary)).E₂ (s,t,t+a-(0:ℕ))),
      Detects (model.convergence D) (s,t,t+a-(0:ℕ)) beta (c≫h₀) →
      ∃ c' : BiHom (t-s) (t+a-(0:ℕ)) (C.obj model.nu model.auxiliary),
        c' ≫ (model.quotients.tower ((SyntheticCategory.biShift (0,b)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))).rho i (i+q) (by omega) =
        c ≫ (model.quotients.tower ((SyntheticCategory.biShift (0,b)).obj
          (model.nu.functor.obj (X.obj model.auxiliary)))).rho i (i+q) (by omega) ∧
        Detects (model.convergence D) (s,t,t+a-(0:ℕ))
          (beta - familyPageMap model.family h₀ 2 (s,t,t+a-(0:ℕ))
            (familyPageMap model.family d₀ 2 (s,t,t+a-(0:ℕ))
              (model.comparison.nuE2 Y a s t 0 y))) (c'≫h₀) := by
  dsimp only
  intro d₀ h₀ c beta hc
  dsimp only [SyntheticObject.obj] at d₀ h₀ c hc ⊢
  change BiHom (t-s) (t+normalizedExponent model.classicalTower g-(0:ℕ))
    (XModLambdaN ((SyntheticCategory.biShift
      (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (i+q)) at c
  obtain ⟨cd,hcd,hcdRho⟩ := mh2_actual_defect_correction X Y Z g q i hq hi
    ef m s t hef y yBar Wg d₀
  have hh := detects_map (.quotient (i+q)
      (.shift (0,(i:ℤ)+ef+normalizedExponent model.classicalTower g) (.nu X))) D h₀
    (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ)) _ cd hcd
  have hsub := detects_add (model.convergence D)
    (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ)) hc (detects_neg hh)
  refine ⟨c-cd,?_,?_⟩
  · rw [Preadditive.sub_comp,hcdRho,sub_zero]
  · let label := familyPageMap model.family h₀ 2
      (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ))
      (familyPageMap model.family d₀ 2
        (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ))
        (model.comparison.nuE2 Y (normalizedExponent model.classicalTower g) s t 0 y))
    have hsub' : Detects (model.convergence D)
        (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ))
        (beta-label) ((c≫h₀)-(cd≫h₀)) := by
      have hs := (congrArg (fun z => Detects (model.convergence D)
        (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ)) z
        ((c≫h₀)+-(cd≫h₀))) (sub_eq_add_neg beta label).symm).mp hsub
      exact (congrArg (fun z => Detects (model.convergence D)
        (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ)) (beta-label) z)
        (sub_eq_add_neg (c≫h₀) (cd≫h₀)).symm).mp hs
    have hhom : (c-cd)≫h₀=(c≫h₀)-(cd≫h₀) := by rw [Preadditive.sub_comp]
    exact (congrArg (fun z => Detects (model.convergence D)
      (s,t,t+normalizedExponent model.classicalTower g-(0:ℕ)) (beta-label) z)
      hhom.symm).mp hsub'


/- Preserve the actual raw d and t choices behind the common edge. In
particular the very same t₀ in the edge equation has the lambda_i transpose
factor needed in the m=0 argument. No arbitrary choice of λ-preimage is used. -/
private theorem quotient_common_desuspended_boundary_defect_with_transpose
    {A B C₀ D₀ E : SyntheticSpectrum} (G : A ⟶ B)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (eC : XModLambdaN (HasFunctorialCofiber.cofib G) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj C₀)
    (eD : XModLambdaN (A⟦(1:ℤ)⟧) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj D₀)
    (epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj D₀ ≅ E) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let L := (model.quotients.tower B).triangle hi (show i < i+q by omega)
    let u := F.map (XModLambdaN.map G (i+q-i))
    let f := u≫L.lambdaMap
    let h := HasFunctorialCofiber.cofibδ G
    ∀ (φ : HasFunctorialCofiber.cofib f ⟶ XModLambdaN (HasFunctorialCofiber.cofib G) (i+q))
      (K : (F.obj (XModLambdaN A (i+q-i)))⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q)),
      HasFunctorialCofiber.cofibι f≫φ=XModLambdaN.map (HasFunctorialCofiber.cofibι G) (i+q) →
      HasFunctorialCofiber.cofibδ f≫K=φ≫XModLambdaN.map h (i+q) →
      let K₀ := ff.preimage ((biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom ≫ K ≫ eD.hom)
      let J₀ := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i A) ≫
          XModLambdaN.incl (A⟦(1:ℤ)⟧) (i+q) ≫ eD.hom)
      let h₀ := ff.preimage (eC.inv ≫ XModLambdaN.map h (i+q) ≫ eD.hom)
      ∃ (d : (F.obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN (HasFunctorialCofiber.cofib G) (i+q))
        (raw : B⟦(1:ℤ)⟧ ⟶ XModLambdaN (A⟦(1:ℤ)⟧) (i+q)),
        let d₀ : A ⟶ C₀ := ff.preimage ((biSuspensionIso (i:ℤ) A).hom ≫ d ≫ eC.hom)
        let t₀ : B ⟶ D₀ := ff.preimage ((biSuspensionIso (i:ℤ) B).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow i B) ≫ raw ≫ eD.hom)
        (XModLambdaN.incl A (i+q-i) ≫ K₀ - J₀ = d₀≫h₀ - G≫t₀) ∧
        ∃ z : B ⟶ E, (SyntheticCategory.biShift (0,-(i:ℤ))).map t₀ ≫ epsilon.hom =
          lambdaPow i B ≫ z := by
  dsimp only
  intro φ K hφ hK
  obtain ⟨d,raw,hedge⟩ := quotient_unquotiented_boundary_defect G i q hi hq φ K hφ hK
  refine ⟨d,raw,?_,?_⟩
  · let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    apply ff.map_injective
    simp only [Functor.map_sub,Functor.map_comp,Functor.FullyFaithful.map_preimage]
    rw [←Category.assoc _ (biSuspensionIso (i:ℤ) (XModLambdaN A (i+q-i))).hom,
      biSuspensionIso_natural]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    have hh := congrArg (fun z => (biSuspensionIso (i:ℤ) A).hom ≫ z ≫ eD.hom) hedge
    simp only [Preadditive.comp_sub,Preadditive.sub_comp,Category.assoc] at hh
    rw [common_shift_residual_factor G i (raw≫eD.hom)] at hh
    exact hh
  · exact common_desuspended_residual_transpose i eD epsilon raw

end
end KIP126.ProofTools.Internal.Mahowald
