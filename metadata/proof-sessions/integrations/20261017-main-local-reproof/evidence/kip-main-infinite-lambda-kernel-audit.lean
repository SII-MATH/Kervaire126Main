module
import KIP126.Main.Conditions
import all KIP126.Main.Internal.Choice.LambdaInjectivity
import KIP126.ProofTools.Operations
import KIP126.ProofTools.Representatives
import all KIP126.Main.Internal.Selected.LambdaOperations
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem route_mem_top_cycles (D : SSData (ModuleCat ℤ)) (a : D.V)
    (ha : ∀ n : ℕ, a ∈ ModuleCat.subobjectModule _ (D.Z n)) :
    a ∈ ModuleCat.subobjectModule _ (D.Z ⊤) := by
  have hspan : (ModuleCat.subobjectModule _).symm (Submodule.span ℤ {a}) ≤ D.Z ⊤ := by
    apply D.Z_top_greatest
    intro n
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    simp only [OrderIso.apply_symm_apply, Submodule.span_le, Set.singleton_subset_iff]
    exact ha n
  have h := (ModuleCat.subobjectModule D.V).monotone hspan
  apply h
  rw [OrderIso.apply_symm_apply]
  exact Submodule.subset_span (by simp)

private theorem route_common_cycle_of_finite_cycles
    (D : SSData (ModuleCat ℤ)) (x : D.page 0)
    (hx : ∀ n : ℕ, ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = x) :
    ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = x := by
  obtain ⟨z₀,hz₀⟩ := hx 0
  have hz₀' : D.pageπ 0 z₀ = x := by
    change (Subobject.ofLE (D.Z 0) (D.Z 0) (le_refl _) ≫ D.pageπ 0) z₀ = x at hz₀
    simpa only [Subobject.ofLE_refl, Category.id_comp] using hz₀
  have hall (n : ℕ) : (D.Z 0).arrow z₀ ∈ ModuleCat.subobjectModule _ (D.Z n) := by
    obtain ⟨z,hz⟩ := hx n
    let j := Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)
    have hkernel : D.pageπ 0 (z₀-j z)=0 := by
      rw [map_sub, hz₀']
      change x - (j ≫ D.pageπ 0) z = 0
      rw [hz, sub_self]
    have hk := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hkernel
    have hk' : (D.Z 0).arrow (z₀-j z) ∈ ModuleCat.subobjectModule _ (D.Z n) :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono le_top).trans ((D.B_le_Z ⊤).trans (D.Z_anti le_top))) hk
    have hj : (D.Z 0).arrow (j z) = (D.Z n).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti bot_le)) z
    have he : (D.Z 0).arrow z₀ =
        (D.Z 0).arrow (z₀-j z) + (D.Z n).arrow z := by
      rw [map_sub,hj]
      abel
    rw [he]
    exact Submodule.add_mem _ hk' ⟨z,rfl⟩
  obtain ⟨zInf,hzInf⟩ := route_mem_top_cycles D ((D.Z 0).arrow z₀) hall
  have he : (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le)) zInf = z₀ := by
    apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
    exact (ConcreteCategory.congr_hom
      (Subobject.ofLE_arrow (D.Z_anti (show (0:WithTop ℕ)≤⊤ from le_top))) zInf).trans hzInf
  refine ⟨zInf,?_⟩
  rw [ModuleCat.comp_apply,he,hz₀']

private theorem route_permanent_of_all_reaches
    (X : ClassicalObject) (p : ℤ×ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hx : ∀ n : ℕ, ReachesPage (model.classical.obj (X.obj model.auxiliary))
      ((n:ℤ)+2) p x) : ClassicalPermanentCycle model X p x := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let D := E.ssData p
  let e : D.page 0 ≅ E.Page 2 p := eqToIso (by
    dsimp only [Page, D, E]
    rw [model.classical.firstPage]
    rfl)
  have hall (n : ℕ) : ∃ z : (Subobject.underlying.obj (D.Z n) : ModuleCat ℤ),
      (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z = e.inv x := by
    have hc := ((KIP126.ProofTools.isCycle_iff_reaches model X ((n:ℤ)+2)
      (by omega) p x).mpr (hx n)).2
    have hn : (((n:ℤ)+2-1)-1).toNat=n := by omega
    change x ∈ LinearMap.range (cycleLabel model X (↑(((n:ℤ)+2-1)-1).toNat) p).hom at hc
    rw [hn] at hc
    obtain ⟨z,hz⟩ := hc
    refine ⟨z, ?_⟩
    apply e.toLinearEquiv.injective
    change e.hom ((Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0) z) = e.hom (e.inv x)
    rw [show e.hom (e.inv x)=x from e.toLinearEquiv.apply_symm_apply x]
    exact hz
  obtain ⟨z,hz⟩ := route_common_cycle_of_finite_cycles D (e.inv x) hall
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have normalize (n : WithTop ℕ) (hn : n=0) :
      Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n =
      Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0 ≫
        eqToHom (congrArg D.page hn.symm) := by
    subst n
    simp only [eqToHom_refl,Category.comp_id]
  refine ⟨z,?_⟩
  change (Subobject.ofLE (D.Z ⊤) (D.Z n₀) (D.Z_anti le_top) ≫ D.pageπ n₀) z=x
  rw [normalize n₀ hn₀]
  change (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0 ≫ e.hom) z=x
  have hz' := congrArg (fun y => e.hom y) hz
  simpa only [ModuleCat.comp_apply,show e.hom (e.inv x)=x from e.toLinearEquiv.apply_symm_apply x] using hz'


private theorem route_regrade_comp_zero_iff
    {m m' w w' : ℤ} {Y Z : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (b : BiHom m w Y) (f : Y ⟶ Z) :
    homotopyRegrade hm hw b ≫ f=0 ↔ b ≫ f=0 := by
  subst m'; subst w'; rfl

namespace KIP126.Main.Internal.High125
open CategoryTheory.Pretriangulated

private theorem route_invisible_lambda_kernel_nuzero
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj (nuZero model X)))
    (halambda : a ≫ SyntheticCategory.lam.app _ = 0)
    (haQ : ∀ n : ℕ, a ≫ (SyntheticCategory.biShift (0,-1)).map
      (XModLambdaN.incl (nuZero model X) n) = 0) : a=0 := by
  let V := nuZero model X
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hshift : F.map a ≫ F.map (lambdaPow 1 V) = 0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,halambda,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle V 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished V 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> dsimp <;> omega)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  let c : BiHom (m+1) w (XModLambdaN V 1) := eS.hom ≫ b
  have hboundary : c ≫ XModLambdaN.proj V 1 = eS.hom ≫ F.map a := by
    simpa [c,F,XModLambdaN.cofiberTriangle,Category.assoc] using
      congrArg (fun f => eS.hom ≫ f) hb.symm
  let s : ℤ := w-(m+1)
  let c' : BiHom (w-s) w (XModLambdaN V 1) := homotopyRegrade (by dsimp[s]; omega) rfl c
  obtain ⟨x,hx⟩ := Choice.nu_first_quotient_label_surjective X s w c'
  have hreach (n : ℕ) : ReachesPage
      (model.classical.obj (X.obj model.auxiliary)) ((n:ℤ)+2) (s,w) x := by
    cases n with
    | zero => simpa using (show ReachesPage _ 2 (s,w) x from ⟨x,RepresentsOnPage.self_two x⟩)
    | succ n =>
      let T := (model.quotients.tower V).triangle (by decide : 0<1)
        (show 1<n+2 by omega)
      have hproj : c' ≫ XModLambdaN.proj V 1 ≫
          F.map (G.map (XModLambdaN.incl V (n+2-1))) = 0 := by
        have h : c ≫ XModLambdaN.proj V 1 ≫
            F.map (G.map (XModLambdaN.incl V (n+2-1))) = 0 := by
          rw [←Category.assoc,hboundary,Category.assoc,←Functor.map_comp,haQ,Functor.map_zero,comp_zero]
        exact (route_regrade_comp_zero_iff (by dsimp[s]; omega) rfl c _).mpr h
      have hd : c' ≫ T.delta = 0 := by
        rw [Choice.lambda_zero_shift_delta_evaluation X 1 (n+2) (by decide) (by omega) (w-s) w c']
        exact hproj
      obtain ⟨d,hd⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₃ T.distinguished c' hd
      have hreach' := (KIP126.Literature.Standard.bhs_finite_lift X (n+2) (by omega) s w x).mpr
        ⟨d,by simpa only [T,Triangle.mk,(model.quotients.tower V).triangle_rho] using hd.symm.trans hx.symm⟩
      simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,add_assoc,Int.reduceAdd] using hreach'
  obtain ⟨z,hz⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s w x).mp
    (route_permanent_of_all_reaches X (s,w) x hreach)
  have hzero' : c' ≫ XModLambdaN.proj V 1 = 0 := by
    change z ≫ XModLambdaN.incl V 1 = firstLabel model X s w x at hz
    rw [←hx,←hz,Category.assoc,XModLambdaN.incl_comp_proj,comp_zero]
  have hzero : c ≫ XModLambdaN.proj V 1 = 0 := by
    exact (route_regrade_comp_zero_iff (by dsimp[s]; omega) rfl c _).mp hzero'
  have haz : F.map a = 0 := by
    apply (cancel_epi eS.hom).mp
    rw [←hboundary,hzero,comp_zero]
  exact F.map_injective (by simpa only [Functor.map_zero] using haz)


private theorem route_invisible_lambda_one_zero_nuzero
    (X : ClassicalObject) (m w : ℤ) (a : BiHom m w (nuZero model X))
    (halambda : lambdaMultiply 1 a=0)
    (haQ : ∀ n : ℕ, quotientClass n a=0) : a=0 := by
  let V := nuZero model X
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  letI : G.Additive := model.exactness.shiftAdditive (0,-1)
  let e : Smn (Syn:=SyntheticSpectrum) m (w-1) ≅ G.obj (Smn m w) :=
    eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
      ((SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0).symm
  let z : BiHom m (w-1) (G.obj V) := e.hom ≫ G.map a
  have hraw : SyntheticCategory.lam.app (Smn m w) ≫ a=0 := by
    simpa only [lambdaMultiply,lambdaPow_one model.quotients.coherence,
      comp_eq_zero_iff_of_epi] using halambda
  have hz : z ≫ SyntheticCategory.lam.app V=0 := by
    dsimp only [z]
    rw [Category.assoc,SyntheticCategory.lam.naturality]
    simp only [Functor.id_map,←Category.assoc,hraw,comp_zero]
  have hq (n : ℕ) : z ≫ G.map (XModLambdaN.incl V n)=0 := by
    dsimp only [z]
    rw [Category.assoc,←Functor.map_comp]
    change e.hom ≫ G.map (quotientClass n a)=0
    rw [haQ,Functor.map_zero,comp_zero]
  have hz0 := route_invisible_lambda_kernel_nuzero X m (w-1) z hz hq
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_injective
  apply (cancel_epi e.hom).mp
  simpa only [z,Functor.map_zero,comp_zero] using hz0

open KIP126.Main.Internal.Selected

private def lambdaAt (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) : BiHom m v X :=
  (biShiftAddIso (m,w) (0,-(n:ℤ)) (m,v) h).inv.app S_0_0 ≫
    lambdaPow n (Smn m w) ≫ a

private theorem lambdaAt_heq (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaAt m n w v h a) (lambdaMultiply n a) := by
  unfold lambdaAt lambdaMultiply
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    Category.assoc,eqToHom_comp_heq_iff,heq_eqToHom_comp_iff]
  rfl

private theorem multiply_heq {m w w' : ℤ} {X : SyntheticSpectrum} (n : ℕ)
    (h : w=w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    HEq (lambdaMultiply n a) (lambdaMultiply n b) := by
  subst w'
  cases hab
  rfl

private theorem lambda_multiply_compose {m w : ℤ} {X : SyntheticSpectrum}
    (k n : ℕ) (a : BiHom m w X) :
    HEq (lambdaMultiply n (lambdaMultiply k a)) (lambdaMultiply (k+n) a) := by
  let v := w-(k:ℤ)
  let u := v-(n:ℤ)
  let hk : (m,w)+(0,-(k:ℤ))=(m,v) := by ext <;> dsimp [v] <;> omega
  let hn : (m,v)+(0,-(n:ℤ))=(m,u) := by ext <;> dsimp [u] <;> omega
  let hkn : (m,w)+(0,-((k+n:ℕ):ℤ))=(m,u) := by ext <;> dsimp [u,v] <;> omega
  have ha := shift_assoc_inv model.quotients.coherence (m,w) (0,-(k:ℤ)) (0,-(n:ℤ))
    (m,v) (0,-((k+n:ℕ):ℤ)) (m,u)
    hk (by ext <;> dsimp <;> omega) hn hkn (S_0_0 : SyntheticSpectrum)
  have heq : lambdaAt m n v u hn (lambdaAt m k w v hk a) =
      lambdaAt m (k+n) w u hkn a := by
    unfold lambdaAt
    erw [←reassoc_of% (lambdaPow_naturality n
      ((biShiftAddIso (m,w) (0,-(k:ℤ)) (m,v) hk).inv.app (S_0_0 : SyntheticSpectrum)))]
    erw [←reassoc_of% (lambdaPow_naturality n (lambdaPow k (Smn m w)))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add model.quotients.coherence k n (k+n) rfl (Smn m w)]
    simp only [lambdaShiftAddIso, lambdaDegree, Category.assoc]
    rfl
  have houter := lambdaAt_heq m n v u hn (lambdaAt m k w v hk a)
  have hinner := multiply_heq n (by rfl : v=w-(k:ℤ)) (lambdaAt_heq m k w v hk a)
  exact (houter.trans hinner).symm.trans ((heq_of_eq heq).trans (lambdaAt_heq m (k+n) _ _ hkn a))



private theorem route_invisible_lambda_torsion_zero_nuzero
    (X : ClassicalObject) (m w : ℤ) (a : BiHom m w (nuZero model X))
    (haQ : ∀ n : ℕ, quotientClass n a=0)
    (htorsion : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  obtain ⟨k,hk⟩ := htorsion
  induction k generalizing w with
  | zero =>
    simpa only [lambdaMultiply,lambdaPow,Category.assoc,comp_eq_zero_iff_of_epi] using hk
  | succ k ih =>
    let b := lambdaMultiply k a
    have hbQ (n : ℕ) : quotientClass n b=0 := by
      simpa only [quotientClass,b,lambdaMultiply,Category.assoc,comp_zero] using
        congrArg (fun z => lambdaMultiply k z) (haQ n)
    have hbOne : lambdaMultiply 1 b=0 := by
      have he := lambda_multiply_compose k 1 a
      rw [hk] at he
      have zero_heq (u v : ℤ) (h:u=v) :
          HEq (0:BiHom m u (nuZero model X)) (0:BiHom m v (nuZero model X)) := by
        subst v
        rfl
      exact eq_of_heq (he.trans (zero_heq _ _ (by omega)))
    have hb0 := route_invisible_lambda_one_zero_nuzero X m (w-k) b hbOne hbQ
    exact ih w a haQ hb0


private theorem nu_infinite_filtration_lambda_torsion_zero
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let e : nuZero model X ≅ V := SyntheticCategory.biShift_zero.app V
  let b : BiHom m w (nuZero model X) := a ≫ e.inv
  have haQ (n : ℕ) : quotientClass n a=0 := by
    apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated (.nu X) n m w
      (quotientClass n a)
    intro s
    exact KIP126.ProofTools.Operations.map_preserves_filtration
      (model.convergentMap (.nu X) (.quotient n (.nu X)) (XModLambdaN.incl V n))
      (m,w) s a (ha s)
  have hbQ (n : ℕ) : quotientClass n b=0 := by
    dsimp only [quotientClass,b]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    change quotientClass n a ≫ XModLambdaN.map e.inv n=0
    rw [haQ,zero_comp]
  have hbT : ∃ k : ℕ, lambdaMultiply k b=0 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    change lambdaMultiply k (a≫e.inv)=0
    have h := congrArg (fun z => z≫e.inv) hk
    simpa only [lambdaMultiply,Category.assoc,zero_comp] using h
  have hb0 := route_invisible_lambda_torsion_zero_nuzero X m w b hbQ hbT
  apply (cancel_mono e.inv).mp
  simpa only [b,zero_comp] using hb0

private theorem sphere_infinite_filtration_lambda_torsion_zero
    (m w : ℤ) (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0 := by
  let b := a ≫ model.nu.unitIso.inv
  have hbF (s : ℕ) : FiltrationAtLeast model.syntheticTower s b :=
    KIP126.ProofTools.Operations.map_preserves_filtration
      (model.convergentMap .sphere (.nu .sphere) model.nu.unitIso.inv) (m,w) s a (ha s)
  have hbT : ∃ k : ℕ, lambdaMultiply k b=0 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    have h := congrArg (fun z => z≫model.nu.unitIso.inv) hk
    simpa only [b,lambdaMultiply,Category.assoc,zero_comp] using h
  have hb0 := nu_infinite_filtration_lambda_torsion_zero .sphere m w b hbF hbT
  apply (cancel_mono model.nu.unitIso.inv).mp
  simpa only [b,zero_comp] using hb0

#print axioms route_common_cycle_of_finite_cycles
#print axioms route_permanent_of_all_reaches
#print axioms route_invisible_lambda_kernel_nuzero
#print axioms route_invisible_lambda_torsion_zero_nuzero
#print axioms nu_infinite_filtration_lambda_torsion_zero
#print axioms sphere_infinite_filtration_lambda_torsion_zero
end KIP126.Main.Internal.High125
