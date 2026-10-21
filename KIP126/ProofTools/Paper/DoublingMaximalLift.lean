module
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary
import all KIP126.ProofTools.GeneralizedMahowald.BottomNuInjection

import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels
import KIP126.Literature.Standard.Filtration

/-! Actual maximal zero-image lifts in the fixed 14-stem. Every declaration
is private. Strict vanishing is proved from the actual quotient boundary,
odd-scalar correction, and restricted lambda-torsion separation. -/
@[expose] section
namespace KIP126.ProofTools.Internal.DoublingKernelGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 5000000

private theorem lambda_multiply_zero_iff_source {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A) :
    lambdaMultiply k a=0 ↔ lambdaPow k (Smn m w)≫a=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi]

private theorem lambda_kernel_actual_boundary {A : SyntheticSpectrum}
    (m w : ℤ) (a : BiHom m w A) (ha : lambdaMultiply 1 a=0) :
    ∃ c : BiHom (m+1) (w-1) (XModLambdaN A 1),
      homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv (m+1) (w-1) 1 A (c≫XModLambdaN.proj A 1))=a := by
  let a' : BiHom ((m+1)-1) ((w-1)+1) A := homotopyRegrade (by omega) (by omega) a
  let d := (biSuspensionHomEquiv (m+1) (w-1) 1 A).symm a'
  have hl : lambdaPow 1 (Smn m w)≫a=0 := (lambda_multiply_zero_iff_source m w 1 a).mp ha
  have hla' : lambdaMultiply 1 a'=0 := by
    dsimp only [a']
    rw [lambda_regrade,ha]
    simp only [regrade_precomp,comp_zero]
  have hmap : (SyntheticCategory.biShift (0,-1)).map a'≫lambdaPow 1 A=0 :=
    (lambdaPow_naturality 1 a').trans
      ((lambda_multiply_zero_iff_source ((m+1)-1) ((w-1)+1) 1 a').mp hla')
  have hd : d≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow 1 A)=0 :=
    (shifted_representative_zero_iff (m+1) (w-1) 1 A A (lambdaPow 1 A) a').mpr hmap
  obtain ⟨c,hc⟩ := (XModLambdaN.cofiberTriangle A 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished A 1) d hd
  change BiHom (m+1) (w-1) (XModLambdaN A 1) at c
  change d=c≫XModLambdaN.proj A 1 at hc
  refine ⟨c,?_⟩
  rw [←hc]
  change homotopyRegrade _ _
    ((biSuspensionHomEquiv (m+1) (w-1) 1 A)
      ((biSuspensionHomEquiv (m+1) (w-1) 1 A).symm a'))=a
  rw [AddEquiv.apply_symm_apply]
  simp only [a',normalized_homotopy_regrade_trans]
  rfl

private theorem absolute_boundary_lambda_power_zero (A : SyntheticSpectrum)
    (m w : ℤ) (q : ℕ) (c : BiHom m w (XModLambdaN A q)) :
    lambdaMultiply q (biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q))=0 := by
  let α := biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q)
  have hδ : ((biSuspensionHomEquiv m w q A).symm α)≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 := by
    simp only [α,AddEquiv.symm_apply_apply,Category.assoc]
    have hz := comp_distTriang_mor_zero₃₁ (XModLambdaN.cofiberTriangle A q)
      (XModLambdaN.cofiberTriangle_distinguished A q)
    change XModLambdaN.proj A q≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 at hz
    rw [hz,comp_zero]
  have hmap := (shifted_representative_zero_iff m w q A A (lambdaPow q A) α).mp hδ
  apply (lambda_multiply_zero_iff_source (m-1) (w+q) q α).mpr
  exact (lambdaPow_naturality q α).symm.trans hmap

private theorem permanent_native_full_lift_generic (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x∈permanentCycles model X (s,t)) :
    ∃ b : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      b≫XModLambdaN.incl _ 1=firstLabel model X s t x≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hp := permanent_cycle_of_member X (s,t) x hx
  obtain ⟨b,hb⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s t x).mp hp
  refine ⟨b≫SyntheticCategory.biShift_zero.hom.app _,?_⟩
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
  exact congrArg (fun z => z≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hb

private theorem first_boundary_zero_of_permanent_label (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x∈permanentCycles model X (s,t))
    (c : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hc : c=firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    biSuspensionHomEquiv (t-s) t 1 (model.nu.functor.obj (X.obj model.auxiliary))
      (c≫XModLambdaN.proj _ 1)=0 := by
  obtain ⟨b,hb⟩ := permanent_native_full_lift_generic X s t x hx
  rw [←hc] at hb
  rw [←hb,Category.assoc,XModLambdaN.incl_comp_proj,comp_zero,map_zero]

private theorem labelled_lambda_kernel_boundary (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s-1) (t+1) (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : lambdaMultiply 1 a=0) :
    ∃ (x : Ambient model X (s,t))
      (c : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)),
      c=firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      biSuspensionHomEquiv (t-s) t 1 (model.nu.functor.obj (X.obj model.auxiliary))
        (c≫XModLambdaN.proj _ 1)=a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let d := (biSuspensionHomEquiv (t-s) t 1 A).symm a
  have hl := (lambda_multiply_zero_iff_source (t-s-1) (t+1) 1 a).mp ha
  have hmap : (SyntheticCategory.biShift (0,-1)).map a≫lambdaPow 1 A=0 :=
    (lambdaPow_naturality 1 a).trans hl
  have hd : d≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow 1 A)=0 :=
    (shifted_representative_zero_iff (t-s) t 1 A A (lambdaPow 1 A) a).mpr hmap
  obtain ⟨c,hc⟩ := (XModLambdaN.cofiberTriangle A 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished A 1) d hd
  change BiHom (t-s) t (XModLambdaN A 1) at c
  change d=c≫XModLambdaN.proj A 1 at hc
  obtain ⟨x,hx⟩ := quotient_first_label_exists X 1 (by decide) s t c
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hx
  refine ⟨x,c,hx,?_⟩
  rw [←hc]
  exact (biSuspensionHomEquiv (t-s) t 1 A).apply_symm_apply a

private def infiniteFiltration (A : SyntheticObject) {m w : ℤ}
    (a : BiHom m w (A.obj model.nu model.auxiliary)) : Prop :=
  ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a

private theorem infiniteFiltration_lambda (A : SyntheticObject) (m w : ℤ) (k : ℕ)
    (a : BiHom m w (A.obj model.nu model.auxiliary)) (ha : infiniteFiltration A a) :
    infiniteFiltration A (lambdaMultiply k a) := by
  intro s
  have hs := (shift_filtration_iff A (0,-(k:ℤ)) (m,w) s a).mpr (ha s)
  have hm := map_preserves_filtration
    (model.convergentMap (.shift (0,-(k:ℤ)) A) A (lambdaPow k _))
    ((m,w)+(0,-(k:ℤ))) s (shiftHomotopyClass (0,-(k:ℤ)) (m,w) a) hs
  have he : lambdaMultiply k a=homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
      (shiftHomotopyClass (0,-(k:ℤ)) (m,w) a≫lambdaPow k _) := by
    simp only [lambdaMultiply,shiftHomotopyClass,regrade_precomp,←lambdaPow_naturality,Category.assoc]
  rw [he]
  exact (regrade_filtration_iff _ _ s _).mpr hm

private theorem lambda_one_reduce_exponent {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A)
    (ha : lambdaMultiply (k+1) a=0) :
    lambdaMultiply k (lambdaMultiply 1 a)=0 := by
  have hz := (lambda_multiply_zero_iff_source m w (k+1) a).mp ha
  apply (lambda_multiply_zero_iff_source m (w-1) k (lambdaMultiply 1 a)).mpr
  let S := Smn (Syn:=SyntheticSpectrum) m w
  let P : Smn (Syn:=SyntheticSpectrum) m (w-1) ⟶
      (SyntheticCategory.biShift (0,-((1:ℕ):ℤ))).obj S :=
    eqToHom (by congr 1; simp) ≫
      (SyntheticCategory.biShift_comp (m,w) (0,-((1:ℕ):ℤ))).inv.app S_0_0
  have he : lambdaMultiply 1 a=P≫lambdaPow 1 S≫a := by
    simp only [lambdaMultiply,P,S,Category.assoc]
  rw [he,←Category.assoc (lambdaPow k _) P,←lambdaPow_naturality k P]
  rw [Category.assoc,←Category.assoc (lambdaPow k _) (lambdaPow 1 S),
    ←lambdaPow_naturality k (lambdaPow 1 S)]
  have hc := lambdaPow_add_comparison model.quotients.coherence 1 k (k+1) (by omega) S
  dsimp only [lambdaDegree] at hc
  rw [←hc]
  simp only [Category.assoc]
  dsimp only [S]
  rw [hz,comp_zero,comp_zero]

private theorem torsion_infiniteFiltration_zero_of_kernel
    (A : SyntheticObject) (m wmax : ℤ)
    (hkernel : ∀ (w : ℤ), w≤wmax →
      ∀ (a : BiHom m w (A.obj model.nu model.auxiliary)),
        infiniteFiltration A a → lambdaMultiply 1 a=0 → a=0)
    (w : ℤ) (hw : w≤wmax) (a : BiHom m w (A.obj model.nu model.auxiliary))
    (ha : infiniteFiltration A a) (ht : ∃ k : ℕ,lambdaMultiply k a=0) : a=0 := by
  obtain ⟨k,hk⟩ := ht
  induction k generalizing w with
  | zero =>
    have hz := (lambda_multiply_zero_iff_source m w 0 a).mp hk
    simpa only [lambdaPow,comp_eq_zero_iff_of_epi] using hz
  | succ k ih =>
    have hmul : lambdaMultiply 1 a=0 := ih (w-1) (by omega) (lambdaMultiply 1 a)
      (infiniteFiltration_lambda A m w 1 a ha) (lambda_one_reduce_exponent m w k a hk)
    exact hkernel w hw a ha hmul

end
end KIP126.ProofTools.Internal.DoublingKernelGeometry
end
@[expose] section
namespace KIP126.ProofTools.Internal.KernelClassical
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem archive_zero (s t : ℕ) (ht : t ≤ 261)
    (hc : archive.basisCount s t=0) (x : model.classical.sphere.Page 2 (s,t)) : x=0 := by
  let e := coordinates s t ht
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by rw [hc]; infer_instance
  exact e.injective (Subsingleton.elim _ _)

private theorem stem14_e2_zero (s : ℤ) (hs : 7 ≤ s)
    (x : model.classical.sphere.Page 2 (s,s+14)) : x=0 := by
  by_cases h9 : 9≤s
  · haveI := KIP126.Literature.Standard.sphereVanishing s (s+14) (by omega) (by omega)
    exact Subsingleton.elim _ _
  · have hh : s=7∨s=8 := by omega
    rcases hh with rfl | rfl
    · exact archive_zero 7 21 (by decide) (by decide) x
    · exact archive_zero 8 22 (by decide) (by decide) x

private theorem stem14_page_zero (s r : ℤ) (hs : 7≤s) (hr : 2≤r)
    (x : model.classical.sphere.Page r (s,s+14)) : x=0 := by
  obtain ⟨x2,hx⟩ := page_has_initial_representative hr x
  have hz := stem14_e2_zero s hs x2
  rw [hz] at hx
  exact hx.unique (RepresentsOnPage.zero hr)

private theorem stem15_high_all_outgoing_zero (s r : ℤ) (hs : 5≤s) (hr : 2≤r) :
    model.classical.sphere.d r (s,s+15)=0 := by
  have hd : (s,s+15)+model.classical.sphere.diffDeg r=(s+r,s+r+14) := by
    rw [model.classical.differentialDegree]
    ext <;> dsimp; omega
  haveI : Subsingleton (model.classical.sphere.Page r
      ((s,s+15)+model.classical.sphere.diffDeg r)) := by
    rw [hd]
    exact ⟨fun x y => (stem14_page_zero (s+r) r (by omega) hr x).trans
      (stem14_page_zero (s+r) r (by omega) hr y).symm⟩
  ext x
  exact Subsingleton.elim _ _

private theorem stem15_high_permanent (s : ℤ) (hs : 5≤s)
    (x : model.classical.sphere.Page 2 (s,s+15)) :
    x∈permanentCycles model .sphere (s,s+15) := by
  apply permanent_member_of_cycle .sphere (s,s+15) x
  apply isPermanentCycle_of_reachesPage model.classical.sphere 2
    (by rw [model.classical.firstPage]) (s,s+15) x
    ⟨x,RepresentsOnPage.self_two x⟩
  exact fun r hr => stem15_high_all_outgoing_zero s r hs hr

private def h0sqh4 : model.classical.sphere.Page 2 (3,18) :=
  product h0 (KIP126.Literature.Standard.hiProduct 0 4)
private def h0cuh4 : model.classical.sphere.Page 2 (4,19) := product h0 h0sqh4
private def h0sqd0 : model.classical.sphere.Page 2 (6,20) := product h0 h0d0

private def h4Word : SourceMonomial archive.generators 1 16 :=
  regradeMonomial rfl rfl (.generator (archive.atomIndex .h4))
private theorem h4Word_value : h4Word.value sourceData sourceGenerator=sourceData.atom .h4 :=
  sourceAtom_agrees .h4
private theorem h0h4_basis :
    (coordinates 2 17 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=
      KIP126.Literature.Standard.hiProduct 0 4 := by
  rw [coordinates_basis]
  change comparison 2 17 _ (sourceData.product 1 1 1 16
    (h0Word.value sourceData sourceGenerator) (h4Word.value sourceData sourceGenerator))=_
  rw [h0Word_value,h4Word_value]
  have h := comparison_product 1 1 1 16 (by decide)
    (sourceData.atom .h0) (sourceData.atom .h4)
  rw [comparison_h0,comparison_h4] at h
  exact h
private theorem h0sqh4_basis :
    (coordinates 3 18 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=h0sqh4 := by
  rw [coordinates_basis]
  change comparison 3 18 _ (sourceData.product 1 1 2 17
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word h4Word).value sourceData sourceGenerator))=_
  have h := comparison_product 1 1 2 17 (by decide)
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word h4Word).value sourceData sourceGenerator)
  rw [h0Word_value,comparison_h0] at h
  have hi := h0h4_basis
  rw [coordinates_basis] at hi
  change comparison 2 17 _ ((SourceMonomial.mul h0Word h4Word).value sourceData sourceGenerator)=_ at hi
  rw [hi] at h
  simpa [h0sqh4,product,hiDegree,h0Word_value] using h
private theorem h0cuh4_basis :
    (coordinates 4 19 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=h0cuh4 := by
  rw [coordinates_basis]
  change comparison 4 19 _ (sourceData.product 1 1 3 18
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word (SourceMonomial.mul h0Word h4Word)).value sourceData sourceGenerator))=_
  have h := comparison_product 1 1 3 18 (by decide)
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word (SourceMonomial.mul h0Word h4Word)).value sourceData sourceGenerator)
  rw [h0Word_value,comparison_h0] at h
  have hi := h0sqh4_basis
  rw [coordinates_basis] at hi
  change comparison 3 18 _ ((SourceMonomial.mul h0Word (SourceMonomial.mul h0Word h4Word)).value sourceData sourceGenerator)=_ at hi
  rw [hi] at h
  simpa [h0cuh4,product,h0Word_value] using h
private theorem h0sqd0_basis :
    (coordinates 6 20 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=h0sqd0 := by
  rw [coordinates_basis]
  change comparison 6 20 _ (sourceData.product 1 1 5 19
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word d0Word).value sourceData sourceGenerator))=_
  have h := comparison_product 1 1 5 19 (by decide)
    (h0Word.value sourceData sourceGenerator)
    ((SourceMonomial.mul h0Word d0Word).value sourceData sourceGenerator)
  rw [h0Word_value,comparison_h0] at h
  have hi := h0d0_basis
  rw [coordinates_basis] at hi
  change comparison 5 19 _ ((SourceMonomial.mul h0Word d0Word).value sourceData sourceGenerator)=_ at hi
  rw [hi] at h
  simpa [h0sqd0,product,h0Word_value] using h

private theorem classical_rep_map
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (f : E ⟶ E') {r : ℤ} {i : Bidegree} {x : E.Page 2 i} {xr : E.Page r i}
    (hx : RepresentsOnPage E r i x xr) :
    RepresentsOnPage E' r i (f.pageMap 2 i x) (f.pageMap r i xr) := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨hr,z,hz,he⟩ := hx
  let n : WithTop ℕ := ↑(2-r₀).toNat
  let m : WithTop ℕ := ↑(r-r₀).toNat
  let F := f.toSSDataMorphism
  have hnm : n≤m := by dsimp [n,m]; exact_mod_cast (show (2-r₀).toNat≤(r-r₀).toNat by omega)
  refine ⟨hr,F.cycleMap i m z,?_,?_⟩
  · have hs := F.cycleMap_ofLE_assoc i hnm ((D' i).pageπ n)
    have hp := F.pageπ_pageMap i n
    have eqn : (Subobject.ofLE ((D i).Z m) ((D i).Z n) ((D i).Z_anti hnm)≫
        (D i).pageπ n)≫F.pageMap i n =
      F.cycleMap i m≫Subobject.ofLE ((D' i).Z m) ((D' i).Z n) ((D' i).Z_anti hnm)≫(D' i).pageπ n := by
      rw [Category.assoc,hp]; exact hs
    have hh := congrArg (fun a=>a z) eqn
    simpa only [ModuleCat.comp_apply,hz,SpectralSequenceMorphism.pageMap,
      SpectralSequenceMorphism.toPreSSMorphism,PreSSMorphism.pageMap,SSDataMorphism.pageMapAt,
      eqToHom_refl,Category.comp_id,n,m,F] using hh.symm
  · have hh := congrArg (fun a=>a z) (F.pageπ_pageMap i m)
    simpa only [ModuleCat.comp_apply,he,SpectralSequenceMorphism.pageMap,
      SpectralSequenceMorphism.toPreSSMorphism,PreSSMorphism.pageMap,SSDataMorphism.pageMapAt,
      eqToHom_refl,Category.comp_id,n,m,F] using hh.symm

private theorem classical_differential_map
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (f : E ⟶ E') {r : ℤ} {p q : Bidegree} {x : E.Page 2 p} {y : E.Page 2 q}
    (hd : HasDifferential E r p q x y) :
    HasDifferential E' r p q (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  obtain ⟨hdeg,xr,yr,hxr,hyr,heq⟩ := hd
  have hdeg' : p+E'.diffDeg r=q := by rw [←f.diffDeg_eq]; exact hdeg
  refine ⟨hdeg',f.pageMap r p xr,f.pageMap r q yr,
    classical_rep_map f hxr,classical_rep_map f hyr,?_⟩
  have H : f.pageMap r (p+E.diffDeg r)≫
        eqToHom (congrArg (E'.Page r) (by rw [f.diffDeg_eq]))≫
        eqToHom (congrArg (E'.Page r) hdeg') =
      eqToHom (congrArg (E.Page r) hdeg)≫f.pageMap r q := by
    subst q
    simp only [eqToHom_trans,eqToHom_refl,Category.id_comp,Category.comp_id]
  change (f.pageMap r p≫E'.d r p≫eqToHom (congrArg (E'.Page r) hdeg')) xr=_
  rw [SpectralSequenceMorphism.pageMap_comm_d_assoc,H]
  exact congrArg (fun z=>f.pageMap r q z) heq

private theorem pairing_rep_three
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (P : SSPairing E E E) (hE : E.r₀≤2) (p q : Bidegree)
    {x : E.Page 2 p} {y : E.Page 2 q} {xr : E.Page 3 p} {yr : E.Page 3 q}
    (hx : RepresentsOnPage E 3 p x xr) (hy : RepresentsOnPage E 3 q y yr) :
    RepresentsOnPage E 3 (p+q) (P.pair 2 p q x y) (P.pair 3 p q xr yr) := by
  obtain ⟨_,zx,hzx,hpx⟩ := hx
  obtain ⟨_,zy,hzy,hpy⟩ := hy
  have hxN : NextPageRelation E 2 p x xr := ⟨zx,hzx,hpx⟩
  have hyN : NextPageRelation E 2 q y yr := ⟨zy,hzy,hpy⟩
  obtain ⟨z,hz,hp⟩ := P.nextPage_compatible 2 p q hE hE hE x xr y yr hxN hyN
  exact ⟨by decide,z,hz,hp⟩

private theorem pairing_d3_with_cycle
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (P : SSPairing E E E) (hE : E.r₀≤2) (p q : Bidegree)
    (hp : P.parity p=0)
    (x : E.Page 2 p) (xr : E.Page 3 p)
    (hx : RepresentsOnPage E 3 p x xr) (hdx : E.d 3 p xr=0)
    (y : E.Page 2 q) (z : E.Page 2 (q+E.diffDeg 3))
    (hd : HasDifferential E 3 q (q+E.diffDeg 3) y z) :
    HasDifferential E 3 (p+q) (p+(q+E.diffDeg 3))
      (P.pair 2 p q x y) (P.pair 2 p (q+E.diffDeg 3) x z) := by
  obtain ⟨_,yr,zr,hy,hz,heq⟩ := hd
  have heq : E.d 3 q yr=zr := by simpa only [eqToHom_refl,Category.comp_id] using heq
  refine ⟨by abel,P.pair 3 p q xr yr,P.pair 3 p (q+E.diffDeg 3) xr zr,
    pairing_rep_three P hE p q hx hy,pairing_rep_three P hE p (q+E.diffDeg 3) hx hz,?_⟩
  have h := P.leibniz 3 p q xr yr
  simp only [hdx,map_zero,LinearMap.zero_apply,transportPage,hp,zero_ne_one,↓reduceIte,one_smul,zero_add] at h
  change (E.d 3 (p+q)≫eqToHom (congrArg (E.Page 3) (show p+q+E.diffDeg 3=p+(q+E.diffDeg 3) by abel))) (P.pair 3 p q xr yr)=_
  rw [ModuleCat.comp_apply,h,←ModuleCat.comp_apply,eqToHom_trans]
  simp only [eqToHom_refl,ModuleCat.id_apply,heq]

private theorem page_cycle_map
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (f : E ⟶ E') {r : ℤ} {p : Bidegree} (x : E.Page r p)
    (hx : E.d r p x=0) : E'.d r p (f.pageMap r p x)=0 := by
  have h := ConcreteCategory.congr_hom (f.pageMap_comm_d r p) x
  simpa only [ModuleCat.comp_apply,hx,map_zero] using h

private theorem sphere_iso_cancel (r : ℤ) (p : Bidegree)
    (x : model.classical.sphere.Page r p) :
    (sphereMappingAdamsIso closedBackground model.classical).hom.pageMap r p
      ((sphereMappingAdamsIso closedBackground model.classical).inv.pageMap r p x)=x := by
  have h := congrArg (fun f=>f x) (congrArg (fun f=>f.pageMap r p)
    (sphereMappingAdamsIso closedBackground model.classical).inv_hom_id)
  simpa only [SpectralSequenceMorphism.pageMap_comp,SpectralSequenceMorphism.pageMap_id,
    ModuleCat.comp_apply,ModuleCat.id_apply] using h

private theorem sphere_product_d2_zero (p q : Bidegree)
    (x : model.classical.sphere.Page 2 p) (y : model.classical.sphere.Page 2 q)
    (hx : model.classical.sphere.d 2 p x=0) (hy : model.classical.sphere.d 2 q y=0) :
    model.classical.sphere.d 2 (p+q) (model.sphereAlgebra.product p q x y)=0 := by
  let S : FiniteSpectrum := ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  let e := sphereMappingAdamsIso closedBackground model.classical
  let P := (mapping_pairing S S S).ssPairing
  let xx := e.inv.pageMap 2 p x
  let yy := e.inv.pageMap 2 q y
  have hxx := page_cycle_map e.inv x hx
  have hyy := page_cycle_map e.inv y hy
  change (mappingSystem.hom S S).underlying.E.d 2 p xx=0 at hxx
  change (mappingSystem.hom S S).underlying.E.d 2 q yy=0 at hyy
  have h := P.leibniz 2 p q xx yy
  simp only [hxx,hyy,map_zero,LinearMap.zero_apply,transportPage] at h
  have hhzero : (mappingSystem.hom S S).underlying.E.d 2 (p+q) (P.pair 2 p q xx yy)=0 := by
    split_ifs at h <;> simpa using h
  have hh := page_cycle_map e.hom (P.pair 2 p q xx yy) hhzero
  have he := mapping_sphere_product p q xx yy
  change e.hom.pageMap 2 (p+q) (P.pair 2 p q xx yy)=
    model.sphereAlgebra.product p q (e.hom.pageMap 2 p (e.inv.pageMap 2 p x))
      (e.hom.pageMap 2 q (e.inv.pageMap 2 q y)) at he
  rw [sphere_iso_cancel,sphere_iso_cancel] at he
  rw [he] at hh
  exact hh

private theorem h0_d2_zero : model.classical.sphere.d 2 (1,1) h0=0 := by
  have hd : (1,1)+model.classical.sphere.diffDeg 2=(3,2) := by
    rw [model.classical.differentialDegree]; rfl
  haveI : Subsingleton (model.classical.sphere.Page 2 ((1,1)+model.classical.sphere.diffDeg 2)) := by
    rw [hd]
    exact ⟨fun x y=>(archive_zero 3 2 (by decide) (by decide) x).trans
      (archive_zero 3 2 (by decide) (by decide) y).symm⟩
  exact Subsingleton.elim _ _

private theorem h0h4_d2_zero : model.classical.sphere.d 2 (2,17)
    (KIP126.Literature.Standard.hiProduct 0 4)=0 := by
  obtain ⟨z,hz,_⟩ := paper6_8_classical_d3.source_survives
  exact represents_d_zero_of_later (by rw [model.classical.firstPage])
    (by decide) (RepresentsOnPage.self_two _) ⟨z,hz⟩

private theorem h0sqh4_d2_zero : model.classical.sphere.d 2 (3,18) h0sqh4=0 := by
  simpa [h0sqh4,product,hiDegree] using
    sphere_product_d2_zero (1,1) (2,17) h0 (KIP126.Literature.Standard.hiProduct 0 4)
      h0_d2_zero h0h4_d2_zero

private theorem h0cuh4_d2_zero : model.classical.sphere.d 2 (4,19) h0cuh4=0 := by
  simpa [h0cuh4,product] using
    sphere_product_d2_zero (1,1) (3,18) h0 h0sqh4 h0_d2_zero h0sqh4_d2_zero

private theorem stem15_s3_d2_zero : model.classical.sphere.d 2 (3,18)=0 := by
  ext x
  change model.classical.sphere.d 2 (3,18) x=0
  obtain hx|hx := one_coordinate_label_cases rfl (coordinates 3 18 (by decide))
    h0sqh4 h0sqh4_basis x
  · simp only [hx,map_zero]
  · simpa only [hx] using h0sqh4_d2_zero

private theorem stem15_s4_d2_zero : model.classical.sphere.d 2 (4,19)=0 := by
  ext x
  change model.classical.sphere.d 2 (4,19) x=0
  obtain hx|hx := one_coordinate_label_cases rfl (coordinates 4 19 (by decide))
    h0cuh4 h0cuh4_basis x
  · simp only [hx,map_zero]
  · simpa only [hx] using h0cuh4_d2_zero

private theorem h4_basis :
    (coordinates 1 16 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=h4 := by
  rw [coordinates_basis]
  change comparison 1 16 _ (h4Word.value sourceData sourceGenerator)=_
  rw [h4Word_value,comparison_h4]

private theorem h4_cases (x : model.classical.sphere.Page 2 (1,16)) : x=0∨x=h4 :=
  one_coordinate_label_cases rfl (coordinates 1 16 (by decide)) h4 h4_basis x

private theorem h0h4_cases (x : model.classical.sphere.Page 2 (2,17)) :
    x=0∨x=KIP126.Literature.Standard.hiProduct 0 4 :=
  one_coordinate_label_cases rfl (coordinates 2 17 (by decide))
    (KIP126.Literature.Standard.hiProduct 0 4) h0h4_basis x

private theorem boundaries_two_of_B_one_eq_B_zero (p : Bidegree)
    (hB : ((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).ssData p).B 1=
      ((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).ssData p).B 0) :
    boundaries model .sphere 2 p=⊥ := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    let D := (model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).ssData p
    let i := Subobject.ofLE (D.B 1) (D.B 0) hB.le
    have hi : i≫boundaryLabel model .sphere 0 p=boundaryLabel model .sphere 1 p := by
      dsimp only [i,boundaryLabel,D]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    have hz : boundaryLabel model .sphere 0 p (i z)∈boundaries model .sphere 1 p := ⟨i z,rfl⟩
    rw [KIP126.ProofTools.Internal.Mahowald.boundaries_one] at hz
    change boundaryLabel model .sphere 1 p z=0
    rw [←hi,ModuleCat.comp_apply]
    simpa only [Submodule.mem_bot] using hz
  · exact bot_le

private theorem stem14_s5_boundaries_two : boundaries model .sphere 2 (5,19)=⊥ := by
  have hB := boundaries_succ_of_zero model.classical.sphere 2
    (by rw [model.classical.firstPage]) (3,18) stem15_s3_d2_zero
  have hd : (3,18)+model.classical.sphere.diffDeg 2=(5,19) := by
    rw [model.classical.differentialDegree]; rfl
  rw [hd,model.classical.firstPage] at hB
  exact boundaries_two_of_B_one_eq_B_zero (5,19) hB

private theorem stem14_s6_boundaries_two : boundaries model .sphere 2 (6,20)=⊥ := by
  have hB := boundaries_succ_of_zero model.classical.sphere 2
    (by rw [model.classical.firstPage]) (4,19) stem15_s4_d2_zero
  have hd : (4,19)+model.classical.sphere.diffDeg 2=(6,20) := by
    rw [model.classical.differentialDegree]; rfl
  rw [hd,model.classical.firstPage] at hB
  exact boundaries_two_of_B_one_eq_B_zero (6,20) hB

private theorem permanent_reaches {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    {p : Bidegree} {x : E.Page 2 p} (h : IsPermanentCycle E p x)
    (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
  obtain ⟨z,hz⟩ := h
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let z' := Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z
  refine ⟨D.pageπ n z',hr,z',?_,rfl⟩
  dsimp only [z']
  rw [←ModuleCat.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem pairing_d3_with_cycle_at
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Bidegree}
    (P : SSPairing E E E) (hE : E.r₀≤2) (p q q' : Bidegree)
    (hp : P.parity p=0)
    (x : E.Page 2 p) (xr : E.Page 3 p)
    (hx : RepresentsOnPage E 3 p x xr) (hdx : E.d 3 p xr=0)
    (y : E.Page 2 q) (z : E.Page 2 q')
    (hd : HasDifferential E 3 q q' y z) :
    HasDifferential E 3 (p+q) (p+q')
      (P.pair 2 p q x y) (P.pair 2 p q' x z) := by
  have hqq := hd.target_degree
  subst q'
  exact pairing_d3_with_cycle P hE p q hp x xr hx hdx y z hd

private theorem h0sqh4_has_d3 : HasDifferential model.classical.sphere 3
    (3,18) (6,20) h0sqh4 h0sqd0 := by
  let S : FiniteSpectrum := ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  let e := sphereMappingAdamsIso closedBackground model.classical
  let P := (mapping_pairing S S S).ssPairing
  have hp : P.parity (1,1)=0 := by
    change (mapping_pairing S S S).ssPairing.parity (1,1)=0
    rw [mapping_parity]
    rfl
  have hE : (mappingSystem.hom S S).underlying.E.r₀≤2 := by
    change (model.classical.obj (mappingSpectrum closedBackground SphereSpectrum SphereSpectrum)).r₀≤2
    rw [model.classical.firstPage]
  have h0perm : IsPermanentCycle model.classical.sphere (1,1) h0 := by
    obtain ⟨z,hz,_⟩ := KIP126.Literature.Standard.two_detection
    exact ⟨z,hz⟩
  obtain ⟨h03,hh03⟩ := permanent_reaches h0perm 3 (by decide)
  have hd03 : model.classical.sphere.d 3 (1,1) h03=0 :=
    represents_d_zero_of_later (by rw [model.classical.firstPage]; norm_num) (by decide)
      hh03 (permanent_reaches h0perm 4 (by decide))
  have hd := classical_differential_map e.inv paper6_8_classical_d3.toHasDifferential
  have h := pairing_d3_with_cycle_at P hE (1,1) (2,17) (5,19) hp
    (e.inv.pageMap 2 (1,1) h0) (e.inv.pageMap 3 (1,1) h03)
    (classical_rep_map e.inv hh03) (page_cycle_map e.inv h03 hd03)
    (e.inv.pageMap 2 (2,17) (KIP126.Literature.Standard.hiProduct 0 4))
    (e.inv.pageMap 2 (5,19) h0d0) hd
  have hh := classical_differential_map e.hom h
  have hs := mapping_sphere_product (1,1) (2,17)
    (e.inv.pageMap 2 (1,1) h0)
    (e.inv.pageMap 2 (2,17) (KIP126.Literature.Standard.hiProduct 0 4))
  have ht := mapping_sphere_product (1,1) (5,19)
    (e.inv.pageMap 2 (1,1) h0) (e.inv.pageMap 2 (5,19) h0d0)
  change e.hom.pageMap 2 ((1,1)+(2,17))
      (P.pair 2 (1,1) (2,17) (e.inv.pageMap 2 (1,1) h0)
        (e.inv.pageMap 2 (2,17) (KIP126.Literature.Standard.hiProduct 0 4))) =
    model.sphereAlgebra.product (1,1) (2,17)
      (e.hom.pageMap 2 (1,1) (e.inv.pageMap 2 (1,1) h0))
      (e.hom.pageMap 2 (2,17) (e.inv.pageMap 2 (2,17)
        (KIP126.Literature.Standard.hiProduct 0 4))) at hs
  change e.hom.pageMap 2 ((1,1)+(5,19))
      (P.pair 2 (1,1) (5,19) (e.inv.pageMap 2 (1,1) h0)
        (e.inv.pageMap 2 (5,19) h0d0)) =
    model.sphereAlgebra.product (1,1) (5,19)
      (e.hom.pageMap 2 (1,1) (e.inv.pageMap 2 (1,1) h0))
      (e.hom.pageMap 2 (5,19) (e.inv.pageMap 2 (5,19) h0d0)) at ht
  rw [sphere_iso_cancel,sphere_iso_cancel] at hs ht
  have hs' : e.hom.pageMap 2 ((1,1)+(2,17))
      (P.pair 2 (1,1) (2,17) (e.inv.pageMap 2 (1,1) h0)
        (e.inv.pageMap 2 (2,17) (KIP126.Literature.Standard.hiProduct 0 4)))=h0sqh4 := by
    simpa [h0sqh4,product,hiDegree] using hs
  have ht' : e.hom.pageMap 2 ((1,1)+(5,19))
      (P.pair 2 (1,1) (5,19) (e.inv.pageMap 2 (1,1) h0)
        (e.inv.pageMap 2 (5,19) h0d0))=h0sqd0 := by
    simpa [h0sqd0,product] using ht
  rw [hs',ht'] at hh
  exact hh

private theorem h0sqd0_ne_zero : h0sqd0≠0 := by
  intro hz
  have hh := congrArg (coordinates 6 20 (by decide)) h0sqd0_basis
  rw [LinearEquiv.apply_symm_apply,hz,map_zero] at hh
  have hv := congrArg (fun f=>f ⟨0,by decide⟩) hh
  norm_num [Finsupp.single_eq_same,Finsupp.zero_apply] at hv

private theorem h0sqh4_nonzero_d3 : HasNonzeroDifferential model.classical.sphere 3
    (3,18) (6,20) h0sqh4 h0sqd0 := by
  obtain ⟨hdeg,xr,yr,hxr,hyr,heq⟩ := h0sqh4_has_d3
  refine ⟨hdeg,xr,yr,hxr,hyr,heq,?_⟩
  exact represents_next_nonzero_of_incoming_zero_at
    (by rw [model.classical.firstPage]) (by decide) stem15_s4_d2_zero
    hyr (RepresentsOnPage.self_two h0sqd0) h0sqd0_ne_zero
    (by rw [model.classical.differentialDegree]; rfl)

private theorem h0sqd0_mem_boundaries_three : h0sqd0∈boundaries model .sphere 3 (6,20) := by
  have hz := differential_target_later_zero
    (by rw [model.classical.firstPage]; norm_num) (by decide : (3:ℤ)<4) h0sqh4_has_d3
  exact KIP126.ProofTools.Internal.Mahowald.represents_zero_mem_boundary model .sphere 4
    (6,20) h0sqd0 hz

private theorem stem14_s6_all_boundaries_three (x : model.classical.sphere.Page 2 (6,20)) :
    x∈boundaries model .sphere 3 (6,20) := by
  obtain hx|hx := one_coordinate_label_cases rfl (coordinates 6 20 (by decide))
    h0sqd0 h0sqd0_basis x
  · rw [hx]; exact Submodule.zero_mem _
  · rw [hx]; exact h0sqd0_mem_boundaries_three

end
end KIP126.ProofTools.Internal.KernelClassical
end
@[expose] section
namespace KIP126.ProofTools.Internal.DoublingKernel
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem nu_detects_not_next_filtration
    (X : ClassicalObject) (s t w : ℤ) (hw : w≤t)
    (x : Ambient model X (s,t))
    (hx : x∉boundaries model X (1+t-w) (s,t))
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) a) :
    ¬ FiltrationAtLeast model.syntheticTower (s+1) a := by
  intro hnext
  obtain ⟨e,he,b,hb,hgr⟩ := ha
  change ((model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).F
    s (t-s,w)).arrow b=a at hb
  change ((model.convergence (.nu X)).identification (s,t,w)).hom e=
    (model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).toAssociatedGraded
      s (t-s,w) b at hgr
  have hzero : (model.syntheticTower.filtration
      (model.nu.functor.obj (X.obj model.auxiliary))).toAssociatedGraded s (t-s,w) b=0 := by
    apply ((model.syntheticTower.filtration _).toAssociatedGraded_eq_zero_iff _ _ _).mpr
    rw [hb]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hnext
  have hezero : e=0 := by
    apply (ModuleCat.mono_iff_injective ((model.convergence (.nu X)).identification (s,t,w)).hom).mp inferInstance
    rw [hgr,hzero,map_zero]
  obtain ⟨hp,hclass⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw x e).mp he
  apply hx
  apply (CrossingLabels.subquotient_zero_iff _ _ ⟨x,hp⟩).mp
  rw [←hclass,hezero,map_zero]

private theorem h4_first_boundary_not_f4 :
    ¬ FiltrationAtLeast model.syntheticTower 4
      (biSuspensionHomEquiv 15 16 1
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (nativeFirstLabel .sphere 1 16 h4≫XModLambdaN.proj _ 1)) := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 1 (by decide) 1 16 h4 h0h3Square paper_d2_h4
  have hc : c=nativeFirstLabel .sphere 1 16 h4 := by
    simpa only [(model.quotients.tower _).rho_id,Category.comp_id,nativeFirstLabel] using hc
  rw [hc] at hβ
  let β := biSuspensionHomEquiv 15 16 1
    (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
      (nativeFirstLabel .sphere 1 16 h4≫XModLambdaN.proj _ 1)
  have hb : β≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square := by
    simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  have hp := first_label_lift_permanent .sphere 3 17 h0h3Square β hb
  have hd := nu_first_label_detects .sphere 3 17 h0h3Square hp β hb
  have hn : h0h3Square≠0 := nonzero_differential_target_label_ne_zero
    (KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide))
  apply nu_detects_not_next_filtration .sphere 3 17 17 (by omega) h0h3Square _ β hd
  simpa only [show (1:ℤ)+17-17=1 by omega,boundaries_one,Submodule.mem_bot] using hn

private theorem h0h4_first_boundary_not_f6
    (hb2 : boundaries model .sphere 2 (5,19)=⊥) :
    ¬ FiltrationAtLeast model.syntheticTower 6
      (biSuspensionHomEquiv 15 17 1
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4)≫
          XModLambdaN.proj _ 1)) := by
  obtain ⟨β,hβ,hδβ⟩ := target_h0h4_boundary
  have hp := first_label_lift_permanent .sphere 5 19 h0d0 β hβ
  have hd := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hp β hβ
  rw [hδβ]
  apply nu_detects_not_next_filtration .sphere 5 19 18 (by omega) h0d0 _ (lambdaMultiply 1 β) hd
  simpa only [show (1:ℤ)+19-18=2 by omega,hb2,Submodule.mem_bot] using h0d0_ne_zero

private theorem third_source_first_boundary_not_f7
    (x : Ambient model .sphere (3,18)) (y : Ambient model .sphere (6,20))
    (hd : HasDifferential model.classical.sphere 3 (3,18) (6,20) x y)
    (hy : y∉boundaries model .sphere 2 (6,20)) :
    ¬ FiltrationAtLeast model.syntheticTower 7
      (biSuspensionHomEquiv 15 18 1
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (nativeFirstLabel .sphere 3 18 x≫XModLambdaN.proj _ 1)) := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 2 (by decide) 3 18 x y hd
  let β : BiHom 14 20 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    biSuspensionHomEquiv 15 18 2 _ (c≫XModLambdaN.proj _ 2)
  have hb : β≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 6 20 y := by
    simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  have hδβ : biSuspensionHomEquiv 15 18 1
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
      (nativeFirstLabel .sphere 3 18 x≫XModLambdaN.proj _ 1)=lambdaMultiply 1 β := by
    have hres := absolute_boundary_restriction .sphere 1 2 (by decide) 15 18 c
    change c≫(model.quotients.tower _).rho 1 2 _=nativeFirstLabel .sphere 3 18 x at hc
    rw [hc] at hres
    simpa [β,homotopyRegrade] using hres
  have hp := first_label_lift_permanent .sphere 6 20 y β hb
  have hdet := nu_lambda_detects .sphere 1 (by decide) 6 20 y hp β hb
  rw [hδβ]
  exact nu_detects_not_next_filtration .sphere 6 20 19 (by omega) y
    (by simpa only [show (1:ℤ)+20-19=2 by omega] using hy) (lambdaMultiply 1 β) hdet

private def kernelH4Word : SourceMonomial archive.generators 1 16 :=
  regradeMonomial rfl rfl (.generator (archive.atomIndex .h4))
private theorem kernelH4Word_value :
    kernelH4Word.value sourceData sourceGenerator=sourceData.atom .h4 := sourceAtom_agrees .h4
private theorem kernel_h4_basis :
    (coordinates 1 16 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=h4 := by
  rw [coordinates_basis]
  change comparison 1 16 _ (kernelH4Word.value sourceData sourceGenerator)=h4
  rw [kernelH4Word_value,comparison_h4]
private theorem kernel_h0h4_basis :
    (coordinates 2 17 (by decide)).symm (Finsupp.single ⟨0,by decide⟩ 1)=
      KIP126.Literature.Standard.hiProduct 0 4 := by
  rw [coordinates_basis]
  change comparison 2 17 _ (sourceData.product 1 1 1 16
    (h0Word.value sourceData sourceGenerator) (kernelH4Word.value sourceData sourceGenerator))=_
  rw [h0Word_value,kernelH4Word_value]
  have h := comparison_product 1 1 1 16 (by decide)
    (sourceData.atom .h0) (sourceData.atom .h4)
  rw [comparison_h0,comparison_h4] at h
  exact h
private theorem kernel_h4_label_cases (x : Ambient model .sphere (1,16)) :
    x=0∨x=h4 :=
  one_coordinate_label_cases rfl (coordinates 1 16 (by decide)) h4 kernel_h4_basis x
private theorem kernel_h0h4_label_cases (x : Ambient model .sphere (2,17)) :
    x=0∨x=KIP126.Literature.Standard.hiProduct 0 4 :=
  one_coordinate_label_cases rfl (coordinates 2 17 (by decide))
    (KIP126.Literature.Standard.hiProduct 0 4) kernel_h0h4_basis x

private theorem kernel_nonpositive_label_zero (s : ℤ) (hs : s≤0)
    (x : Ambient model .sphere (s,s+15)) : x=0 := by
  by_cases hn : s<0
  · haveI := KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere 2 s (s+15) hn
    exact Subsingleton.elim _ _
  · have hz : s=0 := by omega
    subst s
    haveI : Subsingleton (Ambient model .sphere (0,15)) :=
      KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 2 15 (by decide)
    exact @Subsingleton.elim (Ambient model .sphere (0,15)) inferInstance x 0

end
end KIP126.ProofTools.Internal.DoublingKernel
end

@[expose] section
namespace KIP126.ProofTools.Internal.DoublingKernel
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
open KIP126.ProofTools.Internal.DoublingKernelGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 5000000

private theorem low_labelled_boundary_zero
    (hb2 : boundaries model .sphere 2 (5,19)=⊥)
    (s : ℤ) (hs : s≤2) (x : Ambient model .sphere (s,s+15))
    (c : BiHom ((s+15)-s) (s+15)
      (XModLambdaN (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) 1))
    (hc : c=nativeFirstLabel .sphere s (s+15) x)
    (ha : infiniteFiltration (.nu .sphere)
      (biSuspensionHomEquiv ((s+15)-s) (s+15) 1
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (c≫XModLambdaN.proj _ 1))) :
    biSuspensionHomEquiv ((s+15)-s) (s+15) 1
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
      (c≫XModLambdaN.proj _ 1)=0 := by
  by_cases hn : s≤0
  · have hx := kernel_nonpositive_label_zero s hn x
    apply first_boundary_zero_of_permanent_label .sphere s (s+15) x _ c hc
    rw [hx]
    exact Submodule.zero_mem _
  · have hcases : s=1∨s=2 := by omega
    rcases hcases with h1|h2
    · subst s
      rcases kernel_h4_label_cases x with hx|hx
      · apply first_boundary_zero_of_permanent_label .sphere 1 16 x _ c hc
        rw [hx]
        exact Submodule.zero_mem _
      · subst x
        rw [hc] at ha
        exact False.elim (h4_first_boundary_not_f4 (ha 4))
    · subst s
      rcases kernel_h0h4_label_cases x with hx|hx
      · apply first_boundary_zero_of_permanent_label .sphere 2 17 x _ c hc
        rw [hx]
        exact Submodule.zero_mem _
      · subst x
        rw [hc] at ha
        exact False.elim (h0h4_first_boundary_not_f6 hb2 (ha 6))

private theorem restricted_kernel_infiniteFiltration_zero
    (hb2 : boundaries model .sphere 2 (5,19)=⊥)
    (w : ℤ) (hw : w≤18)
    (a : BiHom 14 w (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : infiniteFiltration (.nu .sphere) a) (hlambda : lambdaMultiply 1 a=0) : a=0 := by
  let s := w-16
  let a' : BiHom ((s+15)-s-1) ((s+15)+1)
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    homotopyRegrade (by omega) (by dsimp [s]; omega) a
  have ha' : infiniteFiltration (.nu .sphere) a' := by
    intro k
    exact (regrade_filtration_iff _ _ _ a).mpr (ha k)
  have hlambda' : lambdaMultiply 1 a'=0 := by
    dsimp only [a']
    rw [lambda_regrade,hlambda]
    simp only [regrade_precomp,comp_zero]
  obtain ⟨x,c,hc,hd⟩ := labelled_lambda_kernel_boundary .sphere s (s+15) a' hlambda'
  have hb : infiniteFiltration (.nu .sphere)
      (biSuspensionHomEquiv ((s+15)-s) (s+15) 1 _ (c≫XModLambdaN.proj _ 1)) := by
    intro k
    change FiltrationAtLeast model.syntheticTower k
      (biSuspensionHomEquiv ((s+15)-s) (s+15) 1
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (c≫XModLambdaN.proj _ 1))
    exact hd.symm ▸ (ha' k)
  have hz := low_labelled_boundary_zero hb2 s (by dsimp [s]; omega) x c hc hb
  have hz' : a'=0 := hd.symm.trans hz
  simpa only [a',regrade_precomp,comp_eq_zero_iff_of_epi] using hz'

private theorem restricted_torsion_infiniteFiltration_zero
    (hb2 : boundaries model .sphere 2 (5,19)=⊥)
    (w : ℤ) (hw : w≤18)
    (a : BiHom 14 w (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : infiniteFiltration (.nu .sphere) a)
    (ht : ∃ k : ℕ,lambdaMultiply k a=0) : a=0 :=
  torsion_infiniteFiltration_zero_of_kernel (.nu .sphere) 14 18
    (restricted_kernel_infiniteFiltration_zero hb2) w hw a ha ht

end
end KIP126.ProofTools.Internal.DoublingKernel
end

@[expose] section
namespace KIP126.ProofTools.Internal.DoublingKernel
open KIP126.ProofTools.Internal.KernelClassical KIP126.ProofTools.Internal.DoublingKernelGeometry
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route
private theorem kernel_infiniteFiltration_zero_weight_le18
    (w : ℤ) (hw : w≤18)
    (a : BiHom 14 w (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : infiniteFiltration (.nu .sphere) a) (hk : lambdaMultiply 1 a=0) : a=0 :=
  restricted_kernel_infiniteFiltration_zero stem14_s5_boundaries_two w hw a ha hk

private theorem torsion_infiniteFiltration_zero_weight_le18
    (w : ℤ) (hw : w≤18)
    (a : BiHom 14 w (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : infiniteFiltration (.nu .sphere) a)
    (ht : ∃ k : ℕ,lambdaMultiply k a=0) : a=0 :=
  restricted_torsion_infiniteFiltration_zero stem14_s5_boundaries_two w hw a ha ht

private theorem weight18_torsion_infiniteFiltration_zero
    (a : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : ∀ s : ℕ,FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ,lambdaMultiply k a=0) : a=0 :=
  torsion_infiniteFiltration_zero_weight_le18 18 (by decide) a ha ht
end KIP126.ProofTools.Internal.DoublingKernel
end


@[expose] section
namespace KIP126.ProofTools.Paper.OddLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.Computation.Standard
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

private theorem infinity_zero_of_finite_zero
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ×ℤ))
    (r : ℤ) (p : ℤ×ℤ) (x : E.Page 2 p)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat ℤ))
    (hz : (Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top) ≫
      (E.ssData p).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x)
    (hzero : RepresentsOnPage E r p x 0) : (E.ssData p).pageπ ⊤ z = 0 := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let zn := (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top)) z
  have hrep : RepresentsOnPage E r p x (D.pageπ n zn) := by
    refine ⟨hzero.1,zn,?_,rfl⟩
    dsimp only [zn]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have hn0 := hrep.unique hzero
  have hnmem := (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) zn).mp hn0
  have htop := (ModuleCat.subobjectModule D.V).monotone (D.B_mono le_top) hnmem
  apply (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) _ ≫ (D.Z n).arrow) z ∈ _ at htop
  rwa [Subobject.ofLE_arrow] at htop

private theorem classical_infinity_zero_of_all_represent_zero
    (p : ℤ×ℤ) (r : ℤ)
    (hR : ∀ x : Ambient model .sphere p, RepresentsOnPage model.classical.sphere r p x 0) :
    IsZero ((model.classical.sphere.ssData p).eInfty) := by
  let D := model.classical.sphere.ssData p
  have he (e : D.eInfty) : e=0 := by
    haveI : Epi (D.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ⊤)).mp inferInstance e
    let x : Ambient model .sphere p :=
      (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ (↑(2-model.classical.sphere.r₀).toNat : WithTop ℕ)) z
    exact infinity_zero_of_finite_zero model.classical.sphere r p x z rfl (hR x)
  haveI : Subsingleton D.eInfty := ⟨fun a b=>(he a).trans (he b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

private theorem classical_infinity_zero_of_ambient_zero
    (p : ℤ×ℤ) (hx : ∀ x : Ambient model .sphere p, x=0) :
    IsZero ((model.classical.sphere.ssData p).eInfty) := by
  apply classical_infinity_zero_of_all_represent_zero p 2
  intro x
  rw [hx x]
  exact RepresentsOnPage.zero (by decide)

private theorem ordinary_stem14_infinity_zero
    (h6 : ∀ x : Ambient model .sphere (6,20), RepresentsOnPage model.classical.sphere 4 (6,20) x 0)
    (hhigh : ∀ s : ℤ, 7≤s → ∀ x : Ambient model .sphere (s,14+s), x=0)
    (s : ℤ) (hs : 6≤s) :
    IsZero ((model.classical.sphere.ssData (s,14+s)).eInfty) := by
  by_cases hs6 : s=6
  · subst s
    exact classical_infinity_zero_of_all_represent_zero (6,20) 4 h6
  · exact classical_infinity_zero_of_ambient_zero (s,14+s) (hhigh s (by omega))

private theorem classical_detected_hit_next
    (r : ℤ) (hr : 2≤r) (p q : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p) (y : model.classical.sphere.Page 2 q)
    (hd : HasDifferential model.classical.sphere r p q x y)
    (a : HomotopyGroup (C:=Spectrum) (q.2-q.1) SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) q y a) :
    a ∈ (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtrationSubmodule (q.1+1) (q.2-q.1) := by
  obtain ⟨z,hz,b,hb,hgrade⟩ := ha
  have hy0 := FinitePageCalculus.differential_target_later_zero (by rw [model.classical.firstPage]; exact hr) (show r<r+1 by omega) hd
  have hz0 := infinity_zero_of_finite_zero model.classical.sphere (r+1) q y z hz hy0
  have hgb : (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtration.toAssociatedGraded
      q.1 (q.2-q.1) b = 0 := by
    exact hgrade.symm.trans ((congrArg
      (fun z => (model.classicalConvergence .sphere).identification q |>.hom z) hz0).trans (map_zero _))
  have hmem := ((model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtration.toAssociatedGraded_eq_zero_iff
    q.1 (q.2-q.1) b).mp hgb
  rw [hb] at hmem
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hmem

private theorem classical_filtration_promote
    (m s t : ℤ) (hst : s≤t)
    (hz : ∀ j, s≤j → j<t → IsZero ((model.classical.sphere.ssData (j,m+j)).eInfty))
    (a : HomotopyGroup (C:=Spectrum) m SphereSpectrum) :
    (a ∈ (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtrationSubmodule s m) ↔
      a ∈ (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtrationSubmodule t m := by
  let F := (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtration
  have hgraded (j : ℤ) (hj : s≤j) (hjt : j<t) : IsZero (F.associatedGraded j m) := by
    let I := (model.classicalConvergence .sphere).identification (j,m+j) ≪≫
      eqToIso (congrArg (fun k : ℤ => F.associatedGraded j k) (show (m+j)-j=m by omega))
    exact (hz j hj hjt).of_iso I.symm
  have he := F.eq_of_associatedGraded_isZero s t m hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (AbstractAdamsTower.homotopy SphereSpectrum m)) Q) he
  simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply,ClassicalObject.obj] using Iff.of_eq he'

private theorem ordinary_five_detected_h0d0_all_filtration
    (hz : ∀ j : ℤ, 6≤j → IsZero ((model.classical.sphere.ssData (j,14+j)).eInfty))
    (a : HomotopyGroup (C:=Spectrum) 14 SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (5,19) h0d0 a) :
    ∀ s : ℕ, a ∈ (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtrationSubmodule s 14 := by
  have h6 := classical_detected_hit_next 3 (by decide) (2,17) (5,19)
    (KIP126.Literature.Standard.hiProduct 0 4) h0d0 paper6_8_classical_d3.toHasDifferential a ha
  intro s
  by_cases hs : 6≤(s:ℤ)
  · exact (classical_filtration_promote 14 6 s hs (fun j hj _ => hz j hj) a).mp h6
  · exact (model.classicalTower.tower (ClassicalObject.sphere.obj model.auxiliary)).filtrationSubmodule_antitone 14 (by omega) h6

private theorem ordinary_twice_d0_odd_torsion
    (hz : ∀ j : ℤ, 6≤j → IsZero ((model.classical.sphere.ssData (j,14+j)).eInfty))
    (a : HomotopyGroup (C:=Spectrum) 14 SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (4,18) d0 a) :
    IsOddTorsionMap (2 • a) := by
  have hp := KIP126.Literature.Standard.classical_product_detection 1 1 4 18
    (model.standardClasses.standardHi 0) d0 (classicalTwo (C:=Spectrum)) a
    KIP126.Literature.Standard.two_detection ha
  have hp : ClassicalDetects (model.classicalConvergence .sphere) (5,19) h0d0
      (classicalSphereProduct (classicalTwo (C:=Spectrum)) a) := by
    simpa [h0d0,KIP126.Computation.Standard.product] using hp
  have hinfty := ordinary_five_detected_h0d0_all_filtration hz _ hp
  obtain ⟨N,hN,hNpos,hNz⟩ := KIP126.AdamsSynthetic.Standard.classical_sphere_separated 14 _ hinfty
  let U : Sphere (C:=Spectrum) 14 ≅ Sphere 14 :=
    (shiftFunctorAdd Spectrum (0:ℤ) (14:ℤ)).app SphereSpectrum ≪≫
      (shiftFunctor Spectrum (14:ℤ)).mapIso ((shiftFunctorZero Spectrum ℤ).app SphereSpectrum)
  have heq : classicalSphereProduct (classicalTwo (C:=Spectrum)) a=U.hom≫(2 • a) := by
    change (shiftFunctorAdd Spectrum (0:ℤ) (14:ℤ)).hom.app SphereSpectrum ≫
      (shiftFunctor Spectrum (14:ℤ)).map
        (((shiftFunctorZero Spectrum ℤ).app SphereSpectrum).hom ≫ (2 • 𝟙 SphereSpectrum)) ≫ a =
      (((shiftFunctorAdd Spectrum (0:ℤ) (14:ℤ)).app SphereSpectrum).hom ≫
        (shiftFunctor Spectrum (14:ℤ)).map ((shiftFunctorZero Spectrum ℤ).app SphereSpectrum).hom) ≫ (2 • a)
    simp only [Functor.map_comp,Functor.map_nsmul,Category.assoc,
      Preadditive.nsmul_comp,Preadditive.comp_nsmul]
    have hI := CategoryTheory.Functor.map_id (shiftFunctor Spectrum (14:ℤ)) SphereSpectrum
    have hI2 : (shiftFunctor Spectrum (14:ℤ)).map (𝟙 SphereSpectrum) ≫ a = a := by
      exact (congrArg (fun f => f ≫ a) hI).trans (Category.id_comp a)
    have hh := congrArg (fun f => (2:ℕ) •
      (((shiftFunctorAdd Spectrum (0:ℤ) (14:ℤ)).app SphereSpectrum).hom ≫
      (shiftFunctor Spectrum (14:ℤ)).map ((shiftFunctorZero Spectrum ℤ).app SphereSpectrum).hom ≫ f)) hI2
    simpa only [Iso.app_hom,Category.assoc] using hh
  refine ⟨N,hN,hNpos,?_⟩
  apply (cancel_epi U.hom).mp
  rw [comp_zero,Preadditive.comp_nsmul,←heq]
  exact hNz

private def realizeNativeHom :
    BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) →+
      HomotopyGroup (C:=Spectrum) 14 SphereSpectrum := by
  letI := KIP126.Literature.Standard.realizationData.additive
  exact {
    toFun := fun a => (KIP126.Literature.Standard.realizationData.sphere 14 18).hom ≫
      model.recovery.realization.map a ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
    map_zero' := by simp
    map_add' := by intros; simp [Preadditive.comp_add,Preadditive.add_comp] }

private theorem realizeNative_eq_zero_realizeNu
    (a : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
    realizeNativeHom a = KIP126.Literature.Standard.realizeNu .sphere
      (a≫SyntheticCategory.biShift_zero.inv.app _) := by
  let Z : nuZero model .sphere ≅ model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary) :=
    SyntheticCategory.biShift_zero.app _
  have hcomp : (a≫Z.inv)≫Z.hom=a := by simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hR := congrArg (fun f => model.recovery.realization.map f) hcomp
  simp only [Functor.map_comp] at hR
  have hfinal := congrArg (fun f => (KIP126.Literature.Standard.realizationData.sphere 14 18).hom≫f≫
    model.recovery.nuRealizationIso.hom.app SphereSpectrum) hR.symm
  change (KIP126.Literature.Standard.realizationData.sphere 14 18).hom≫model.recovery.realization.map a≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum =
      KIP126.Literature.Standard.realizeNu .sphere (a≫Z.inv)
  unfold KIP126.Literature.Standard.realizeNu realizeNuZero
  simpa only [Functor.map_comp,Category.assoc,Z,Functor.id_obj,ClassicalObject.obj,Iso.app_hom] using hfinal

private theorem native_d0_realization_detects
    (hd0 : NonzeroSurvival model.classical.sphere (4,18) d0)
    (a : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 4 18 d0) :
    ClassicalDetects (model.classicalConvergence .sphere) (4,18) d0 (realizeNativeHom a) := by
  rw [realizeNative_eq_zero_realizeNu]
  apply KIP126.Literature.Standard.selected_realization_detection .sphere 4 18 d0 _ hd0
  dsimp only [quotientClass]
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,ha]
  dsimp only [nativeFirstLabel]
  rw [Category.assoc,←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,
    model.quotients.functoriality.map_id,Category.comp_id]

private theorem realizeNative_zero_iff
    (a : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
    realizeNativeHom a=0 ↔ model.recovery.realization.map a=0 := by
  let E := Iso.homCongr (KIP126.Literature.Standard.realizationData.sphere 14 18).symm
    (model.recovery.nuRealizationIso.app SphereSpectrum)
  have hE : E (model.recovery.realization.map a)=realizeNativeHom a := by rfl
  have hE0 : E 0=0 := by simp only [E,Iso.homCongr_apply,comp_zero,zero_comp]
  constructor
  · intro h
    apply E.injective
    exact hE.trans (h.trans hE0.symm)
  · intro h
    rw [←hE,h,hE0]

private theorem one_coordinate_nonzero_cases
    {A : Type} [AddCommGroup A] [Module ℤ A]
    (e : A ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2)) (a : A) (ha : a ≠ 0) (x : A) :
    x = 0 ∨ x = a := by
  have ea : e a = Finsupp.single 0 1 := by
    rcases one_coordinate_cases (e a) with h | h
    · exact False.elim (ha (e.injective (h.trans e.map_zero.symm)))
    · exact h
  rcases one_coordinate_cases (e x) with h | h
  · exact Or.inl (e.injective (h.trans e.map_zero.symm))
  · exact Or.inr (e.injective (h.trans ea.symm))

private theorem d0_nonzero : d0 ≠ 0 := by
  have hne := nonzero_differential_target_label_ne_zero paper6_8_classical_d3
  intro hz
  apply hne
  change model.sphereAlgebra.product (1,1) (4,18) h0 d0 = 0
  rw [hz, map_zero]

private theorem h0h4_nonzero : KIP126.Literature.Standard.hiProduct 0 4 ≠ 0 := by
  obtain ⟨a,ha,hne⟩ := paper6_8_classical_d3.source_survives
  intro hz
  rw [hz] at ha
  exact hne (ha.unique (RepresentsOnPage.zero ha.1))

private theorem odd_h0h4_d2_zero :
    model.classical.sphere.d 2 (2,17) (KIP126.Literature.Standard.hiProduct 0 4) = 0 := by
  obtain ⟨a,ha,_⟩ := paper6_8_classical_d3.source_survives
  exact represents_d_zero_of_later
    (by rw [model.classical.firstPage]) (by decide)
    (RepresentsOnPage.self_two _) ⟨a,ha⟩

private theorem degree_2_17_d2_zero : model.classical.sphere.d 2 (2,17) = 0 := by
  ext x
  change model.classical.sphere.d 2 (2,17) x = 0
  rcases one_coordinate_nonzero_cases (coordinates 2 17 (by decide))
    (KIP126.Literature.Standard.hiProduct 0 4) h0h4_nonzero x with hz | he
  · simp only [hz, map_zero]
  · simpa only [he] using odd_h0h4_d2_zero

private theorem h4_d2_nonzero : model.classical.sphere.d 2 (1,16) h4 ≠ 0 := by
  obtain ⟨hdeg,a,b,ha,hb,hd,hne⟩ :=
    KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide)
  have haa : a = h4 := ha.eq_on_page_two.symm
  intro hz
  apply hne
  rw [←hd]
  change (eqToHom (congrArg (model.classical.sphere.Page 2) hdeg))
    (model.classical.sphere.d 2 (1,16) a) = 0
  rw [haa,hz,map_zero]

private theorem degree_1_16_e3_zero :
    Subsingleton (model.classical.sphere.Page 3 (1,16)) := by
  have h4ne : h4 ≠ 0 := by
    intro hz
    exact h4_d2_nonzero (by rw [hz,map_zero])
  apply choice_next_zero_of_single_frame_nonzero_differential
    (r := 2) (by decide) (by rw [model.classical.firstPage]) h4 h4_d2_nonzero
  exact one_coordinate_nonzero_cases (coordinates 1 16 (by decide)) h4 h4ne

private theorem d0_no_incoming (r : ℤ) (hr : 2 ≤ r) :
    model.classical.sphere.d r (((4:ℤ),18)-model.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hq : ((4:ℤ),18)-model.classical.sphere.diffDeg 2 = (2,17) := by
      rw [model.classical.differentialDegree]
      decide
    rw [hq]
    exact degree_2_17_d2_zero
  by_cases h3 : r = 3
  · subst r
    have hq : ((4:ℤ),18)-model.classical.sphere.diffDeg 3 = (1,16) := by
      rw [model.classical.differentialDegree]
      decide
    rw [hq]
    letI := degree_1_16_e3_zero
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha,map_zero]
  by_cases h4 : r = 4
  · subst r
    have hq : ((4:ℤ),18)-model.classical.sphere.diffDeg 4 = (0,15) := by
      rw [model.classical.differentialDegree]
      decide
    rw [hq]
    letI := KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 4 15 (by decide)
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha,map_zero]
  · let q := ((4:ℤ),18)-model.classical.sphere.diffDeg r
    have hs : q.1 < 0 := by
      dsimp only [q]
      rw [model.classical.differentialDegree]
      change 4-r < 0
      omega
    letI : Subsingleton (model.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 hs
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha,map_zero]

private theorem d0_nonzero_survival :
    NonzeroSurvival model.classical.sphere (4,18) d0 := by
  exact nonzeroSurvival_of_survivesTo model.classical.sphere 2
    (by rw [model.classical.firstPage]) (4,18) d0
    ⟨d0,RepresentsOnPage.self_two d0,d0_nonzero⟩
    d0_all_outgoing_zero d0_no_incoming


private theorem d0_add_self_zero : d0 + d0 = 0 := by
  apply (coordinates 4 18 (by decide)).injective
  rw [map_add,map_zero]
  ext i
  exact (by decide : ∀ c : ZMod 2, c+c=0) ((coordinates 4 18 (by decide)) d0 i)

private theorem odd_nsmul_d0 (N : ℕ) (hN : Odd N) : N • d0 = d0 := by
  obtain ⟨k,rfl⟩ := hN
  rw [Nat.mul_comm 2 k,add_nsmul,mul_nsmul,one_nsmul,two_nsmul,
    ←nsmul_add,d0_add_self_zero,nsmul_zero,zero_add]

private theorem native_first_label_nsmul
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t)) (N : ℕ) :
    nativeFirstLabel X s t (N • x) = N • nativeFirstLabel X s t x := by
  have regrade_nsmul {A : SyntheticSpectrum} (m w w' : ℤ) (hw : w=w')
      (a : BiHom m w A) :
      homotopyRegrade rfl hw (N • a) = N • homotopyRegrade rfl hw a := by
    subst w'
    rfl
  simp only [nativeFirstLabel,first_label_inline,map_nsmul,regrade_nsmul,
    Preadditive.nsmul_comp]

private theorem odd_nsmul_native_d0 (N : ℕ) (hN : Odd N) :
    N • nativeFirstLabel .sphere 4 18 d0 = nativeFirstLabel .sphere 4 18 d0 := by
  rw [←native_first_label_nsmul,odd_nsmul_d0 N hN]

private theorem odd_nsmul_d0_lift_first_label
    (N : ℕ) (hN : Odd N)
    (D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hD : D ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 4 18 d0) :
    (N • D) ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 4 18 d0 := by
  rw [Preadditive.nsmul_comp,hD,odd_nsmul_native_d0 N hN]


private theorem odd_torsion_kills_actual_two_image
    (D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hD : D ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 4 18 d0)
    (hT : IsOddTorsionMap (realizeNativeHom (2 • D))) :
    ∃ D' : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      D' ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 4 18 d0 ∧
      model.recovery.realization.map (D' ≫ model.nu.functor.map twoMap) = 0 := by
  obtain ⟨N,hN,_,hNz⟩ := hT
  refine ⟨N • D,odd_nsmul_d0_lift_first_label N hN D hD,?_⟩
  apply (realizeNative_zero_iff _).mp
  have htwo : model.nu.functor.map twoMap =
      2 • 𝟙 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) := by
    letI := model.nu.additive
    change model.nu.functor.map (2 • 𝟙 SphereSpectrum) =
      2 • 𝟙 (model.nu.functor.obj SphereSpectrum)
    rw [Functor.map_nsmul,model.nu.functor.map_id]
  have he : (N • D) ≫ model.nu.functor.map twoMap = N • (2 • D) := by
    rw [htwo,Preadditive.comp_nsmul,Category.comp_id]
    exact smul_comm 2 N D
  rw [he,map_nsmul]
  exact hNz




private theorem ordinary_stem14_all_infinity_zero (s : ℤ) (hs : 6≤s) :
    IsZero ((model.classical.sphere.ssData (s,14+s)).eInfty) := by
  apply ordinary_stem14_infinity_zero ?_ ?_ s hs
  · intro x
    rcases one_coordinate_nonzero_cases (coordinates 6 20 (by decide))
      KIP126.ProofTools.Internal.KernelClassical.h0sqd0 KIP126.ProofTools.Internal.KernelClassical.h0sqd0_ne_zero x with hx | hx
    · rw [hx]
      exact RepresentsOnPage.zero (by decide)
    · rw [hx]
      exact differential_target_later_zero
        (by rw [model.classical.firstPage]; decide) (by decide : (3:ℤ)<4)
        KIP126.ProofTools.Internal.KernelClassical.h0sqh4_nonzero_d3.toHasDifferential
  · intro j hj
    have hz := KIP126.ProofTools.Internal.KernelClassical.stem14_e2_zero j hj
    change ∀ x : Ambient model .sphere (j,j+14), x=0 at hz
    have hp : (j,j+14)=(j,14+j) := by ext; dsimp; omega
    exact (congrArg (fun p : ℤ×ℤ => ∀ x : Ambient model .sphere p, x=0) hp).mp hz

private theorem d0_full_lift_with_actual_two_realization_zero :
    ∃ D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      D ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 4 18 d0 ∧
      model.recovery.realization.map (D ≫ model.nu.functor.map twoMap) = 0 := by
  obtain ⟨D,hD⟩ := d0_full_lift
  apply odd_torsion_kills_actual_two_image D hD
  rw [map_nsmul]
  apply ordinary_twice_d0_odd_torsion ordinary_stem14_all_infinity_zero
  exact native_d0_realization_detects d0_nonzero_survival D hD

end
end KIP126.ProofTools.Paper.OddLift
end

@[expose] section
namespace KIP126.ProofTools.Paper.DoublingMaximalLift
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem lambda_multiply_zero_iff_source {A : SyntheticSpectrum}
    (m w : ℤ) (k : ℕ) (a : BiHom m w A) :
    lambdaMultiply k a=0 ↔ lambdaPow k (Smn m w)≫a=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi]


private theorem absolute_boundary_lambda_power_zero (A : SyntheticSpectrum)
    (m w : ℤ) (q : ℕ) (c : BiHom m w (XModLambdaN A q)) :
    lambdaMultiply q (biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q))=0 := by
  let α := biSuspensionHomEquiv m w q A (c≫XModLambdaN.proj A q)
  have hδ : ((biSuspensionHomEquiv m w q A).symm α)≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 := by
    simp only [α,AddEquiv.symm_apply_apply,Category.assoc]
    have hz := comp_distTriang_mor_zero₃₁ (XModLambdaN.cofiberTriangle A q)
      (XModLambdaN.cofiberTriangle_distinguished A q)
    change XModLambdaN.proj A q≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q A)=0 at hz
    rw [hz,comp_zero]
  have hmap := (shifted_representative_zero_iff m w q A A (lambdaPow q A) α).mp hδ
  apply (lambda_multiply_zero_iff_source (m-1) (w+q) q α).mpr
  exact (lambdaPow_naturality q α).symm.trans hmap

private theorem full_two_boundary_representatives :
    ∃ a : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      ∃ β : BiHom 14 19 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
        a≫XModLambdaN.incl _ 1 = (model.firstQuotient .sphere 1 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 5 19 h0d0 ∧
        a≫selectedTwoNormalized = lambdaMultiply 1 β ∧
        lambdaMultiply 1 a = 0 := by
  obtain ⟨β0,hβ0,hβunit⟩ := base_h4_boundary
  obtain ⟨β,hβ,hδβ⟩ := target_h0h4_boundary
  obtain ⟨κ,hκ,σ,hγ⟩ := two_degree_boundary_shift (S_0_0:SyntheticSpectrum) h4Q1
  let cunit := shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv
  let c := cunit≫XModLambdaN.map positiveTwoSphereIso.inv 1
  let γ := biSuspensionHomEquiv 15 17 1 (Smn (Syn:=SyntheticSpectrum) 0 1)
    (cunit≫XModLambdaN.proj _ 1)
  let a : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :=
    biSuspensionHomEquiv 15 17 1 _ (c≫XModLambdaN.proj _ 1)
  have ha : a=γ≫positiveTwoSphereIso.inv :=
    quotient_boundary_evaluation_natural positiveTwoSphereIso.inv 1 15 17 cunit
  have hγ' : γ=shiftHomotopyClass (0,1) (14,17) (σ.hom≫β0≫model.nu.unitIso.hom) := by
    rw [←hβunit]
    exact hγ
  have hafirst : a≫XModLambdaN.incl _ 1 =
      shiftHomotopyClass (0,1) (14,17) β0≫XModLambdaN.incl _ 1 := by
    rw [ha]
    exact two_geometric_boundary_source_first_quotient β0 γ σ hγ'
  refine ⟨a,β,?_,hβ,?_,?_⟩
  · rw [hafirst]
    exact positive_shift_full_first_label .sphere 3 17 h0h3Square β0 hβ0
  · have hcimage := h4_actual_two_source_quotient_image κ hκ
    have hcimage : c≫XModLambdaN.map selectedTwoNormalized 1=
        nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4) := by
      simpa only [c,cunit,Category.assoc] using hcimage
    rw [←hδβ,←hcimage]
    exact (quotient_boundary_evaluation_natural selectedTwoNormalized 1 15 17 c).symm

  · exact absolute_boundary_lambda_power_zero _ 15 17 1 c

private theorem positive_lambda_of_shift_source_auto
    (A : SyntheticSpectrum) (D : BiHom 14 18 A) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) 14 18 ≅ Smn 14 18,
      lambdaMultiply 1 (shiftHomotopyClass (0,1) (14,18) D) =
        u.hom≫D≫lambdaToPositivePow 1 A := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let H : 𝟭 SyntheticSpectrum ≅ F⋙L :=
    SyntheticCategory.biShift_zero.symm ≪≫
      eqToIso (congrArg SyntheticCategory.biShift
        (show ((0:ℤ),(0:ℤ))=(0,1)+(0,-1) by decide)) ≪≫
      (SyntheticCategory.biShift_comp (0,1) (0,-1)).symm
  let S : Smn (Syn:=SyntheticSpectrum) 14 18 ≅ (F⋙L).obj (Smn 14 18) :=
    ((SyntheticCategory.biShift_comp (14,19) (0,-1)).app S_0_0).symm ≪≫
      L.mapIso ((SyntheticCategory.biShift_comp (14,18) (0,1)).app S_0_0).symm
  let u := S ≪≫ (H.app (Smn 14 18)).symm
  refine ⟨u,?_⟩
  have hfactor : lambdaToPositivePow 1 A=H.hom.app A≫lambdaPow 1 (F.obj A) := by
    simp [H,lambdaToPositivePow,F,Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,
      Category.assoc]
  have hn := lambdaPow_naturality 1 (shiftHomotopyClass (0,1) (14,18) D)
  have hstep : lambdaMultiply 1 (shiftHomotopyClass (0,1) (14,18) D)=
      S.hom≫L.map (F.map D)≫lambdaPow 1 (F.obj A) := by
    calc
      _ = (SyntheticCategory.biShift_comp (14,19) (0,-1)).inv.app S_0_0≫
          (lambdaPow 1 (Smn 14 19)≫shiftHomotopyClass (0,1) (14,18) D) := by
        simp [lambdaMultiply]
      _ = (SyntheticCategory.biShift_comp (14,19) (0,-1)).inv.app S_0_0≫
          (L.map (shiftHomotopyClass (0,1) (14,18) D)≫lambdaPow 1 (F.obj A)) := by
        exact congrArg (fun z => (SyntheticCategory.biShift_comp (14,19) (0,-1)).inv.app S_0_0≫z) hn.symm
      _ = _ := by
        simp only [shiftHomotopyClass,S,F,L,Iso.trans_hom,Iso.symm_hom,
          Functor.mapIso_hom,Iso.app_inv,Functor.map_comp,Category.assoc]
  rw [hstep,hfactor]
  have hH := H.hom.naturality D
  have hH' := congrArg (fun z => H.inv.app (Smn 14 18)≫z≫lambdaPow 1 (F.obj A)) hH
  simp only [Functor.id_map,Functor.comp_map,Category.assoc,Iso.inv_hom_id_app_assoc] at hH'
  simpa only [u,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,Category.assoc] using
    congrArg (fun z => S.hom≫z) hH'.symm

private theorem corrected_short_image_realization_zero
    (D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hD : model.recovery.realization.map (D≫model.nu.functor.map twoMap)=0) :
    model.recovery.realization.map
      ((lambdaMultiply 1 (shiftHomotopyClass (0,1) (14,18) D))≫selectedTwoNormalized)=0 := by
  obtain ⟨u,hu⟩ := positive_lambda_of_shift_source_auto _ D
  have hf : lambdaToPositivePow 1
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))≫
      selectedTwoNormalized=model.nu.functor.map twoMap := selectedTwoNormalized_factorization
  calc
    _ = model.recovery.realization.map (u.hom≫(D≫model.nu.functor.map twoMap)) := by
      rw [hu]
      simp only [Category.assoc,hf]
    _ = 0 := by rw [Functor.map_comp,hD,comp_zero]

private theorem nu_infinity_zero_of_permanent_le_boundary
    (X : ClassicalObject) (s t w : ℤ) (hw : w≤t)
    (hzero : permanentCycles model X (s,t) ≤ boundaries model X (1+t-w) (s,t)) :
    IsZero (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) := by
  have he (e : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) : e=0 := by
    obtain ⟨x,hx,_,hz⟩ := CrossingLabels.nu_grade_label X s t w hw e
    exact hz.mp (hzero hx)
  haveI : Subsingleton (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
    ⟨fun a b => (he a).trans (he b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

private theorem stem14_weight18_infinity_zero
    (h6 : ∀ x : Ambient model .sphere (6,20), x∈boundaries model .sphere 3 (6,20))
    (hhigh : ∀ s : ℤ, 7≤s → ∀ x : Ambient model .sphere (s,14+s), x=0)
    (s : ℤ) (hs : 6≤s) :
    IsZero (((model.family.nu model.nu (ClassicalObject.sphere.obj model.auxiliary)).sequence.ssData
      (s,14+s,18)).eInfty) := by
  by_cases hs6 : s=6
  · subst s
    exact nu_infinity_zero_of_permanent_le_boundary .sphere 6 20 18 (by decide)
      (fun x hx => h6 x)
  · exact sphere_nu_infinity_zero_of_ambient_zero s (14+s) 18 (hhigh s (by omega))

private theorem infinite_filtration_of_six
    (h6 : ∀ x : Ambient model .sphere (6,20), x∈boundaries model .sphere 3 (6,20))
    (hhigh : ∀ s : ℤ, 7≤s → ∀ x : Ambient model .sphere (s,14+s), x=0)
    (z : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hz : FiltrationAtLeast model.syntheticTower 6 z) :
    ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s z := by
  intro s
  by_cases hs : (s:ℤ)≤6
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (14,18) hs hz
  · apply (filtration_iff_of_infinity_zero (model.convergence (.nu .sphere))
      6 s 14 18 (by omega) ?_ z).mp hz
    intro k hk hk'
    exact stem14_weight18_infinity_zero h6 hhigh k hk

private theorem strict_zero_corrected_source
    (h6 : ∀ x : Ambient model .sphere (6,20), x∈boundaries model .sphere 3 (6,20))
    (hhigh : ∀ s : ℤ, 7≤s → ∀ x : Ambient model .sphere (s,14+s), x=0)
    (hzero : ∀ z : BiHom 14 18
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      (∀ s : ℕ, FiltrationAtLeast model.syntheticTower s z) →
      (∃ k : ℕ,lambdaMultiply k z=0) → z=0)
    (D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hD : D≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 4 18 d0)
    (hDreal : model.recovery.realization.map (D≫model.nu.functor.map twoMap)=0) :
    ∃ a' : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      Detects (model.convergence (.shift (0,1) (.nu .sphere))) (3,17,18)
        (regradeE2 (by simp) (model.comparison.nuE2 .sphere 1 3 17 0 h0h3Square)) a' ∧
      a'≫selectedTwoNormalized=0 := by
  letI := KIP126.Literature.Standard.realization_additive
  obtain ⟨a,β,hafirst,hβ,heq,halambda⟩ := full_two_boundary_representatives
  let d : BiHom 14 19 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :=
    shiftHomotopyClass (0,1) (14,18) D
  let b : BiHom 14 19 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary)) := d≫selectedTwoNormalized
  let q : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) := lambdaMultiply 1 d
  let a' := a-q
  have hbp := first_label_lift_permanent .sphere 5 19 h0d0 b
    (d0_positive_normalized_image D hD)
  have hβp := first_label_lift_permanent .sphere 5 19 h0d0 β hβ
  have ht := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hβp β hβ
  have ht' := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hbp b
    (d0_positive_normalized_image D hD)
  have hdifference := detects_sub_filtration (model.convergence (.nu .sphere))
    (5,19,18) ht ht'
  have hq : FiltrationAtLeast model.syntheticTower 4 q :=
    shifted_full_first_kernel_filtration .sphere 1 3 17 q
      (lambdaMultiply_quotient_zero _ 1 14 19 d)
  have has := shifted_full_source_detects_of_first .sphere 1 3 17 h0h3Square
    h0h3Square_permanent a hafirst
  have hsource := detects_of_high_difference (.shift (0,1) (.nu .sphere)) (3,17,18)
    _ a a' has (by
      have he : a'-a = -q := by dsimp only [a']; abel
      rw [he]
      exact (model.syntheticTower.filtrationSubmodule _ _ _).neg_mem hq)
  have himage : a'≫selectedTwoNormalized=lambdaMultiply 1 β-lambdaMultiply 1 b := by
    dsimp only [a',q,b]
    rw [Preadditive.sub_comp,heq]
    simp only [lambdaMultiply,Category.assoc]
  have hhighimage : FiltrationAtLeast model.syntheticTower 6 (a'≫selectedTwoNormalized) := by
    rw [himage]
    exact hdifference
  have hFalambda : lambdaMultiply 1 (a≫selectedTwoNormalized)=0 := by
    simpa only [lambdaMultiply,Category.assoc,zero_comp] using
      congrArg (fun z => z≫selectedTwoNormalized) halambda
  have hFareal : model.recovery.realization.map (a≫selectedTwoNormalized)=0 :=
    (KIP126.Literature.Standard.selected_realization_kernel (.nu .sphere)
      14 18 (a≫selectedTwoNormalized)).mpr ⟨1,hFalambda⟩
  have hqreal : model.recovery.realization.map (q≫selectedTwoNormalized)=0 :=
    corrected_short_image_realization_zero D hDreal
  have hreal : model.recovery.realization.map (a'≫selectedTwoNormalized)=0 := by
    dsimp only [a']
    rw [Preadditive.sub_comp,Functor.map_sub,hFareal,hqreal,sub_zero]
  have htorsion := (KIP126.Literature.Standard.selected_realization_kernel (.nu .sphere)
    14 18 (a'≫selectedTwoNormalized)).mp hreal
  refine ⟨a',?_,hzero _ (infinite_filtration_of_six h6 hhigh _ hhighimage) htorsion⟩
  simpa using hsource

private theorem native_source_of_positive_strict_zero
    (a' : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))))
    (hsource : Detects (model.convergence (.shift (0,1) (.nu .sphere))) (3,17,18)
      (regradeE2 (by simp) (model.comparison.nuE2 .sphere 1 3 17 0 h0h3Square)) a')
    (hzero : a'≫selectedTwoNormalized=0) :
    ∃ a : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square ∧
      Detects (model.convergence (.nu .sphere)) (3,17,17)
        (nuWeightLabel model .sphere 3 17 17 (by decide) h0h3Square) a ∧
      shiftHomotopyClass (0,1) (14,17) a≫selectedTwoNormalized=0 := by
  let E := suspInvarianceAddEquiv 14 17 0 1
    (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
  let a := E.symm a'
  have hE (b : BiHom 14 17
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
      E b=shiftHomotopyClass (0,1) (14,17) b := by
    simp [E,suspInvarianceAddEquiv,susp_invariance,shiftHomotopyClass,Iso.homCongr]
  have ha : shiftHomotopyClass (0,1) (14,17) a=a' := by
    rw [←hE]
    exact E.apply_symm_apply a'
  have hafirst := shifted_nu_source_first .sphere 1 3 17 (Or.inr rfl) h0h3Square a (by
    have h := hsource
    rw [←ha] at h
    convert h using 1 <;> norm_num [homotopyRegrade]
    rfl)
  refine ⟨a,hafirst,?_,?_⟩
  · exact nu_first_label_detects .sphere 3 17 h0h3Square h0h3Square_permanent a hafirst
  · rw [ha,hzero]

private theorem sphere_unit_zero_image_lift
    (a : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square)
    (hz : shiftHomotopyClass (0,1) (14,17) a≫selectedTwoNormalized=0) :
    ∃ aS : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      aS≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square≫
        XModLambdaN.map model.nu.unitIso.hom 1 ∧
      shiftHomotopyClass (0,1) (14,17) aS≫KIP126.Literature.Standard.syntheticH0=0 ∧
      ∀ q : ℕ,∃ b : BiHom 14 (18+(q:ℤ)) (S_0_0:SyntheticSpectrum),
        homotopyRegrade rfl (by dsimp; omega) (lambdaMultiply q b)=
          shiftHomotopyClass (0,1) (14,17) aS≫KIP126.Literature.Standard.syntheticH0 := by
  let aS := a≫model.nu.unitIso.hom
  have hfirst : aS≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square≫
      XModLambdaN.map model.nu.unitIso.hom 1 := by
    dsimp only [aS]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,ha]
  have hzero : shiftHomotopyClass (0,1) (14,17) aS≫
      KIP126.Literature.Standard.syntheticH0=0 := by
    have h := congrArg (fun z => z≫model.nu.unitIso.hom) hz
    rw [selectedTwoNormalized_eq_h0] at h
    simpa only [h0NormalizedMap,shiftHomotopyClass,aS,Functor.map_comp,
      Category.assoc,Iso.inv_hom_id,Category.comp_id,zero_comp] using h
  refine ⟨aS,hfirst,hzero,?_⟩
  intro q
  refine ⟨0,?_⟩
  rw [hzero]
  simp only [lambdaMultiply,regrade_precomp,comp_zero]

/-- The fixed d0 lift is adjusted only by an odd integer, retaining its exact
first-quotient label while killing the realization of its actual twice-image. -/
private theorem paper6_10_native_actual_zero_image :
    ∃ a : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square ∧
      Detects (model.convergence (.nu .sphere)) (3,17,17)
        (nuWeightLabel model .sphere 3 17 17 (by decide) h0h3Square) a ∧
      shiftHomotopyClass (0,1) (14,17) a≫selectedTwoNormalized=0 := by
  obtain ⟨D,hD,hDreal⟩ := KIP126.ProofTools.Paper.OddLift.d0_full_lift_with_actual_two_realization_zero
  have hhigh : ∀ s : ℤ, 7≤s → ∀ x : Ambient model .sphere (s,14+s), x=0 := by
    intro s hs
    have h := KIP126.ProofTools.Internal.KernelClassical.stem14_e2_zero s hs
    change ∀ x : Ambient model .sphere (s,s+14),x=0 at h
    have hp : (s,s+14)=(s,14+s) := by ext; dsimp; omega
    exact (congrArg (fun p : ℤ×ℤ => ∀ x : Ambient model .sphere p,x=0) hp).mp h
  obtain ⟨a',hsource,hzero⟩ := strict_zero_corrected_source
    KIP126.ProofTools.Internal.KernelClassical.stem14_s6_all_boundaries_three hhigh
    KIP126.ProofTools.Internal.DoublingKernel.weight18_torsion_infiniteFiltration_zero D hD hDreal
  exact native_source_of_positive_strict_zero a' hsource hzero

/-- Actual zero image under the specified synthetic h0 map, on the fixed
synthetic sphere. In particular its image admits a q-fold lambda division
for every q, the maximal-image assertion of the remark. -/
private theorem paper6_10_actual_maximal_zero_image_lift :
    ∃ a : BiHom 14 17 (S_0_0:SyntheticSpectrum),
      a≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 3 17 h0h3Square≫
        XModLambdaN.map model.nu.unitIso.hom 1 ∧
      shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0=0 ∧
      ∀ q : ℕ,∃ b : BiHom 14 (18+(q:ℤ)) (S_0_0:SyntheticSpectrum),
        homotopyRegrade rfl (by dsimp; omega) (lambdaMultiply q b)=
          shiftHomotopyClass (0,1) (14,17) a≫KIP126.Literature.Standard.syntheticH0 := by
  obtain ⟨a,ha,_,hz⟩ := paper6_10_native_actual_zero_image
  exact sphere_unit_zero_image_lift a ha hz

end
end KIP126.ProofTools.Paper.DoublingMaximalLift
end
