module
import all KIP126.Literature.Standard.FiniteQuotientGhosts
import all KIP126.Literature.Standard.FiniteQuotientPositive
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import all KIP126.Literature.Standard.FiniteQuotientWhitehead
import all KIP126.Literature.Standard.FiniteQuotientSuspension
import all KIP126.Literature.Standard.FiniteQuotientAdditivity
import Mathlib.Tactic.Abel

/-! Construction and correction of the middle suspension comparison.
The same comparison preserves the inclusion and the first-map square.
No target horizontal row or global sphere detection is assumed. -/
@[expose] section
namespace KIP126.Literature.Standard.Internal.GhostResearch
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route KIP126.Literature
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

private theorem finite_c_middle_inclusion_defect_factors
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ)
    (kA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (kB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (hA : XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q ≫ kA.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (hf : XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫ kB.hom =
      kA.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₁ q))
    (hneg : ∀ z : (SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₃ ⟶
      XModLambdaN N.obj₂ q, z=0) :
    ∃ u : XModLambdaN N.obj₃ q ⟶ XModLambdaN N.obj₂ q,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q ≫ kB.hom -
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ≫
          ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₂ q) ≫
            (shiftFunctor SyntheticSpectrum (1:ℤ)).map u) := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let d := XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q ≫ kB.hom -
    S.map (XModLambdaN.incl N.obj₂ q)
  have hfd : S.map N.mor₁ ≫ d=0 := by
    dsimp only [d]
    rw [Preadditive.comp_sub,←Category.assoc,XModLambdaN.incl_naturality,
      Category.assoc,hf,←Category.assoc,hA,←Functor.map_comp,
      ←XModLambdaN.incl_naturality,Functor.map_comp,sub_self]
  let d0 := S.preimage d
  have hd0 : S.map d0=d := S.map_preimage _
  have hfd0 : N.mor₁ ≫ d0=0 := S.map_injective (by
    rw [Functor.map_comp,hd0,hfd,Functor.map_zero])
  obtain ⟨r,hr⟩ := N.yoneda_exact₂ hN d0 hfd0
  have hrzero : lambdaPow q N.obj₃ ≫ r=0 := hneg _
  obtain ⟨u,hu⟩ := (XModLambdaN.cofiberTriangle N.obj₃ q).yoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished N.obj₃ q) r hrzero
  change r = XModLambdaN.incl N.obj₃ q ≫ u at hu
  refine ⟨u,?_⟩
  change d = S.map (XModLambdaN.incl N.obj₂ q) ≫
    (S.map (XModLambdaN.map N.mor₂ q) ≫ S.map u)
  rw [←hd0,hr,hu,Functor.map_comp,Functor.map_comp,←Category.assoc,
    ←Functor.map_comp,XModLambdaN.incl_naturality,Functor.map_comp,Category.assoc]

section Jacobson
universe u v
private theorem jacobson_postcomp_bijective_transfer
    {Cat : Type u} [Category.{v} Cat] [Preadditive Cat]
    {S B C : Cat} (g : B ⟶ C) (u : C ⟶ B)
    (hB : Function.Bijective (fun t : S ⟶ B => t ≫ (𝟙 B + g ≫ u))) :
    Function.Bijective (fun t : S ⟶ C => t ≫ (𝟙 C + u ≫ g)) := by
  constructor
  · intro x y hxy
    have hxu : x ≫ u = y ≫ u := hB.1 (by
      simpa only [comp_add, add_comp, Category.assoc, Category.comp_id,
        Category.id_comp] using congrArg (fun t => t ≫ u) hxy)
    have hxy' : x + (x ≫ u) ≫ g = y + (y ≫ u) ≫ g := by
      simpa only [comp_add, Category.comp_id, Category.assoc] using hxy
    rw [hxu] at hxy'
    exact add_right_cancel hxy'
  · intro z
    obtain ⟨b, hb⟩ := hB.2 (z ≫ u)
    have hbg : b ≫ g + b ≫ g ≫ u ≫ g = z ≫ u ≫ g := by
      simpa only [comp_add, add_comp, Category.comp_id, Category.assoc]
        using congrArg (fun t => t ≫ g) hb
    refine ⟨z - b ≫ g, ?_⟩
    simp only [comp_add, sub_comp, Category.comp_id, Category.assoc]
    rw [← hbg]
    abel

/-- The same transfer for all bigraded synthetic spheres, without claiming
that these spheres detect isomorphisms in the category. -/
private theorem jacobson_sphere_bijective_transfer
    {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {B C : Syn} (g : B ⟶ C) (u : C ⟶ B)
    (hB : ∀ m w : ℤ, Function.Bijective
      (fun t : BiHom m w B => t ≫ (𝟙 B + g ≫ u))) :
    ∀ m w : ℤ, Function.Bijective
      (fun t : BiHom m w C => t ≫ (𝟙 C + u ≫ g)) := by
  intro m w
  exact jacobson_postcomp_bijective_transfer g u (hB m w)

/-- The categorical Jacobson lemma, with its explicit inverse. -/
private theorem jacobson_isIso_transfer
    {Cat : Type u} [Category.{v} Cat] [Preadditive Cat]
    {B C : Cat} (g : B ⟶ C) (u : C ⟶ B)
    [IsIso (𝟙 C + u ≫ g)] : IsIso (𝟙 B + g ≫ u) := by
  let q : C ⟶ C := inv (𝟙 C + u ≫ g)
  let k : B ⟶ B := 𝟙 B - g ≫ q ≫ u
  have hqL : q + u ≫ g ≫ q = 𝟙 C := by
    simpa only [add_comp, Category.id_comp, Category.assoc] using
      (IsIso.hom_inv_id (𝟙 C + u ≫ g))
  have hqR : q + q ≫ u ≫ g = 𝟙 C := by
    simpa only [comp_add, Category.comp_id, Category.assoc] using
      (IsIso.inv_hom_id (𝟙 C + u ≫ g))
  have hL : g ≫ q ≫ u + g ≫ u ≫ g ≫ q ≫ u = g ≫ u := by
    simpa only [comp_add, add_comp, Category.assoc, Category.comp_id,
      Category.id_comp] using
      congrArg (fun t => g ≫ t ≫ u) hqL
  have hR : g ≫ q ≫ u + g ≫ q ≫ u ≫ g ≫ u = g ≫ u := by
    simpa only [comp_add, add_comp, Category.assoc, Category.comp_id,
      Category.id_comp] using
      congrArg (fun t => g ≫ t ≫ u) hqR
  refine ⟨⟨k, ?_, ?_⟩⟩
  · dsimp [k]
    simp only [comp_sub, add_comp, Category.id_comp, Category.comp_id,
      Category.assoc]
    rw [hL]
    abel
  · dsimp [k]
    simp only [sub_comp, comp_add, Category.id_comp, Category.comp_id,
      Category.assoc]
    calc
      _ = 𝟙 B + g ≫ u - (g ≫ q ≫ u + g ≫ q ≫ u ≫ g ≫ u) := by abel
      _ = 𝟙 B := by rw [hR]; abel

end Jacobson

private theorem finite_c_normalize_middle_iso
    {X U S T F : SyntheticSpectrum} (L : ℕ) (hF : SphereCells F L)
    (i : X ⟶ S) (j : X ⟶ T) (k0 k : S ≅ T)
    (g : T ⟶ F) (u : F ⟶ T) (fS : U ⟶ S) (fT : U ⟶ T)
    (hinc : i ≫ k.hom=j ≫ (𝟙 T+g≫u))
    (hf : fS≫k.hom=fT) (hfg : fT≫g=0)
    (hghost : SphereGhost ((k0.inv≫k.hom)-(𝟙 T+g≫u))) :
    ∃ k' : S ≅ T, i≫k'.hom=j ∧ fS≫k'.hom=fT := by
  let eta : T ≅ T := k0.symm ≪≫ k
  have hB : ∀ m w : ℤ, Function.Bijective
      (fun b : BiHom m w T => b≫(𝟙 T+g≫u)) := by
    intro m w
    have heq : (fun b : BiHom m w T => b≫(𝟙 T+g≫u)) =
        (fun b : BiHom m w T => b≫eta.hom) := by
      funext b
      have hz := hghost m w b
      rw [Preadditive.comp_sub,sub_eq_zero] at hz
      exact hz.symm
    rw [heq]
    constructor
    · intro b c hbc
      exact (cancel_mono eta.hom).mp hbc
    · intro b
      exact ⟨b≫eta.inv, by simp only [Category.assoc,eta.inv_hom_id,Category.comp_id]⟩
  have hC := jacobson_sphere_bijective_transfer g u hB
  letI : IsIso (𝟙 F+u≫g) := finite_cells_reflect_spherewise_iso hF hF _ hC
  letI : IsIso (𝟙 T+g≫u) := jacobson_isIso_transfer g u
  let beta := asIso (𝟙 T+g≫u)
  have hfBeta : fT≫beta.hom=fT := by
    change fT≫(𝟙 T+g≫u)=fT
    rw [Preadditive.comp_add,Category.comp_id,←Category.assoc,hfg,zero_comp,add_zero]
  have hfInv : fT≫beta.inv=fT := by
    apply (cancel_mono beta.hom).mp
    rw [Category.assoc,beta.inv_hom_id,Category.comp_id]
    exact hfBeta.symm
  refine ⟨k ≪≫ beta.symm, ?_, ?_⟩
  · change i≫(k.hom≫beta.inv)=j
    rw [←Category.assoc,hinc]
    change (j≫beta.hom)≫beta.inv=j
    rw [Category.assoc,beta.hom_inv_id,Category.comp_id]
  · change fS≫(k.hom≫beta.inv)=fT
    rw [←Category.assoc,hf,hfInv]

/-- Desuspend the already proved finite-source window. This is strict
map vanishing for a finite literal source; no global detection is used. -/
private theorem finite_c_unsuspended_negative_hom
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-(r.2-r.1)≤0)
    {A B : SyntheticSpectrum}
    (aCoord : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (bCoord : B ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (z : (SyntheticCategory.biShift (0,-(q:ℤ))).obj A ⟶ XModLambdaN B q) : z=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI := model.exactness.shiftCommShift (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let e : (F.obj (A⟦(-1:ℤ)⟧))⟦(1:ℤ)⟧ ≅ F.obj A :=
    S.mapIso ((F.commShiftIso (-1:ℤ)).app A) ≪≫
      (shiftFunctorCompIsoId SyntheticSpectrum (-1) 1 (by omega)).app (F.obj A)
  let eA := (shiftFunctor SyntheticSpectrum (-1:ℤ)).mapIso aCoord
  let eB := bCoord ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _
  have hz : e.hom≫z=0 :=
    suspension_finite_source_to_quotient_vanishing_of_shifted_coordinates X Y hX
      p r (-1) 0 q hq (by omega) eA eB _
  exact (cancel_epi e.hom).mp (by simpa only [comp_zero] using hz)

private theorem finite_c_shifted_quotient_endomorphism_ghost
    (Y : ClassicalObject) (q : ℕ) (hq : 0<q)
    (a : (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)⟦(1:ℤ)⟧ ⟶
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)⟦(1:ℤ)⟧)
    (ha : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q)≫a=0) :
    SphereGhost a := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let a0 := S.preimage a
  have ha0 : S.map a0=a := S.map_preimage _
  have hinc0 : XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q≫a0=0 :=
    S.map_injective (by rw [Functor.map_comp,ha0,ha,Functor.map_zero])
  have hghost0 := quotient_nu_endomorphism_sphere_ghost Y q hq a0 hinc0
  intro m w c
  let e : S.obj (Smn (Syn:=SyntheticSpectrum) (m-1) w) ≅ Smn m w :=
    ghost_sphere_suspension_iso (m-1) w ≪≫ eqToIso (by congr 1; omega)
  let b := S.preimage (e.hom≫c)
  have hb : S.map b=e.hom≫c := S.map_preimage _
  have hb0 := hghost0 (m-1) w b
  have hs : S.map b≫S.map a0=0 := by rw [←Functor.map_comp,hb0,Functor.map_zero]
  rw [hb,ha0,Category.assoc] at hs
  exact (cancel_epi e.hom).mp (by simpa only [comp_zero] using hs)

section MiddleTR3
universe u v
variable {Cat : Type u} [Category.{v} Cat] [Preadditive Cat]
  [HasZeroObject Cat] [HasShift Cat ℤ]
  [∀ n : ℤ, (shiftFunctor Cat n).Additive] [Pretriangulated Cat]

/-- Prescribed end isomorphisms and the actual boundary square produce a
middle isomorphism, while preserving both specified head squares. -/
private theorem middleTR3_endpoints
    (T₁ T₂ : Triangle Cat) (hT₁ : T₁ ∈ distTriang Cat)
    (hT₂ : T₂ ∈ distTriang Cat)
    (eA : T₁.obj₁ ≅ T₂.obj₁) (eC : T₁.obj₃ ≅ T₂.obj₃)
    (hh : T₁.mor₃ ≫ eA.hom⟦(1:ℤ)⟧' = eC.hom ≫ T₂.mor₃) :
    ∃ eB : T₁.obj₂ ≅ T₂.obj₂,
      T₁.mor₁ ≫ eB.hom = eA.hom ≫ T₂.mor₁ ∧
      T₁.mor₂ ≫ eC.hom = eB.hom ≫ T₂.mor₂ := by
  obtain ⟨b, hb₁, hb₂⟩ :=
    complete_distinguished_triangle_morphism₂ T₁ T₂ hT₁ hT₂ eA.hom eC.hom hh
  let φ : T₁ ⟶ T₂ := Triangle.homMk _ _ eA.hom b eC.hom hb₁ hb₂ hh
  haveI : IsIso b := isIso₂_of_isIso₁₃ φ hT₁ hT₂
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)
  exact ⟨asIso b, hb₁, hb₂⟩

/-- Standard suspension expressed with positive first and second maps.
Mathlib's suspension multiplies all three maps by -1; conjugating the
middle vertex by -id leaves exactly the negative boundary. -/
private theorem middleTR3_raw_shift_distinguished
    (T : Triangle Cat) (hT : T ∈ distTriang Cat) :
    Triangle.mk (T.mor₁⟦(1:ℤ)⟧') (T.mor₂⟦(1:ℤ)⟧')
      (-(T.mor₃⟦(1:ℤ)⟧')) ∈ distTriang Cat := by
  let U := Triangle.mk (T.mor₁⟦(1:ℤ)⟧') (T.mor₂⟦(1:ℤ)⟧')
    (-(T.mor₃⟦(1:ℤ)⟧'))
  apply isomorphic_distinguished _ (Triangle.shift_distinguished T hT (1:ℤ)) U
  refine Triangle.isoMk U (T⟦(1:ℤ)⟧) (Iso.refl _)
    (-(Iso.refl _)) (Iso.refl _) ?_ ?_ ?_
  all_goals simp [U, Triangle.shiftFunctor, shiftFunctorComm_eq_refl]

/-- Compare an arbitrary distinguished row to the signed suspension row.
The hypothesis is the complete third square, with its necessary minus sign. -/
private theorem middleTR3_raw_shift
    (T₀ T₁ : Triangle Cat) (hT₀ : T₀ ∈ distTriang Cat)
    (hT₁ : T₁ ∈ distTriang Cat)
    (eA : T₁.obj₁ ≅ T₀.obj₁⟦(1:ℤ)⟧)
    (eC : T₁.obj₃ ≅ T₀.obj₃⟦(1:ℤ)⟧)
    (hh : T₁.mor₃ ≫ eA.hom⟦(1:ℤ)⟧' =
      eC.hom ≫ (-(T₀.mor₃⟦(1:ℤ)⟧'))) :
    ∃ eB : T₁.obj₂ ≅ T₀.obj₂⟦(1:ℤ)⟧,
      T₁.mor₁ ≫ eB.hom = eA.hom ≫ T₀.mor₁⟦(1:ℤ)⟧' ∧
      T₁.mor₂ ≫ eC.hom = eB.hom ≫ T₀.mor₂⟦(1:ℤ)⟧' := by
  exact middleTR3_endpoints T₁
    (Triangle.mk (T₀.mor₁⟦(1:ℤ)⟧') (T₀.mor₂⟦(1:ℤ)⟧')
      (-(T₀.mor₃⟦(1:ℤ)⟧'))) hT₁
    (middleTR3_raw_shift_distinguished T₀ hT₀) eA eC hh

/-- Objectwise shift comparisons at the two ends produce the middle
comparison for Q. The raw suspended row has negative boundary. -/
private theorem middleTR3_quotient_suspension
    (Q : Cat ⥤ Cat) {A B C : Cat}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ A⟦(1:ℤ)⟧)
    (eA : Q.obj (A⟦(1:ℤ)⟧) ≅ (Q.obj A)⟦(1:ℤ)⟧)
    (eC : Q.obj (C⟦(1:ℤ)⟧) ≅ (Q.obj C)⟦(1:ℤ)⟧)
    (eSA : Q.obj ((A⟦(1:ℤ)⟧)⟦(1:ℤ)⟧) ≅
      (Q.obj (A⟦(1:ℤ)⟧))⟦(1:ℤ)⟧)
    (h_strict : Q.map (h⟦(1:ℤ)⟧') ≫ eSA.hom =
      eC.hom ≫ (Q.map h)⟦(1:ℤ)⟧')
    (hR₀ : Triangle.mk (Q.map f) (Q.map g) (Q.map h ≫ eA.hom) ∈ distTriang Cat)
    (hR₁ : Triangle.mk (Q.map (f⟦(1:ℤ)⟧')) (Q.map (g⟦(1:ℤ)⟧'))
      (-(Q.map (h⟦(1:ℤ)⟧') ≫ eSA.hom)) ∈ distTriang Cat) :
    ∃ κB : Q.obj (B⟦(1:ℤ)⟧) ≅ (Q.obj B)⟦(1:ℤ)⟧,
      Q.map (f⟦(1:ℤ)⟧') ≫ κB.hom = eA.hom ≫ (Q.map f)⟦(1:ℤ)⟧' ∧
      Q.map (g⟦(1:ℤ)⟧') ≫ eC.hom = κB.hom ≫ (Q.map g)⟦(1:ℤ)⟧' := by
  apply middleTR3_raw_shift
    (Triangle.mk (Q.map f) (Q.map g) (Q.map h ≫ eA.hom))
    (Triangle.mk (Q.map (f⟦(1:ℤ)⟧')) (Q.map (g⟦(1:ℤ)⟧'))
      (-(Q.map (h⟦(1:ℤ)⟧') ≫ eSA.hom))) hR₀ hR₁ eA eC
  dsimp
  simp only [neg_comp, Functor.map_comp, comp_neg, Category.assoc, h_strict]

end MiddleTR3

/-- Both rows and finite-C input produce a middle comparison that is
simultaneously inclusion-compatible and strictly natural on f. The middle
comparison is constructed, rather than assumed from the caller. -/
private theorem finite_c_middle_suspension_comparison
    (Y : ClassicalObject) {A C : SyntheticSpectrum}
    (f : A ⟶ model.nu.functor.obj (Y.obj model.auxiliary))
    (g : model.nu.functor.obj (Y.obj model.auxiliary) ⟶ C)
    (h : C ⟶ A⟦(1:ℤ)⟧)
    (hN : Triangle.mk f g h ∈ distTriang SyntheticSpectrum)
    (q : ℕ) (hq : 0<q) (L : ℕ)
    (hCells : SphereCells ((XModLambdaN C q)⟦(1:ℤ)⟧) L)
    (hneg : ∀ z : (SyntheticCategory.biShift (0,-(q:ℤ))).obj C ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q, z=0)
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (eC : XModLambdaN (C⟦(1:ℤ)⟧) q ≅ (XModLambdaN C q)⟦(1:ℤ)⟧)
    (eSA : XModLambdaN ((A⟦(1:ℤ)⟧)⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (A⟦(1:ℤ)⟧) q)⟦(1:ℤ)⟧)
    (hstrict : XModLambdaN.map (h⟦(1:ℤ)⟧') q≫eSA.hom=
      eC.hom≫(XModLambdaN.map h q)⟦(1:ℤ)⟧')
    (hR0 : Triangle.mk (XModLambdaN.map f q) (XModLambdaN.map g q)
      (XModLambdaN.map h q≫eA.hom) ∈ distTriang SyntheticSpectrum)
    (hR1 : Triangle.mk (XModLambdaN.map (f⟦(1:ℤ)⟧') q)
      (XModLambdaN.map (g⟦(1:ℤ)⟧') q)
      (-(XModLambdaN.map (h⟦(1:ℤ)⟧') q≫eSA.hom)) ∈ distTriang SyntheticSpectrum) :
    ∃ eB : XModLambdaN ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q ≅
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)⟦(1:ℤ)⟧,
      XModLambdaN.incl ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q≫eB.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q) ∧
      XModLambdaN.map (f⟦(1:ℤ)⟧') q≫eB.hom=
        eA.hom≫(XModLambdaN.map f q)⟦(1:ℤ)⟧' := by
  let N := Triangle.mk f g h
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  obtain ⟨k,hkf,_hkg⟩ := middleTR3_quotient_suspension Q f g h eA eC eSA hstrict hR0 hR1
  dsimp only [Q, LambdaQuotientFunctoriality.functor] at k hkf _hkg
  obtain ⟨u,hu⟩ := finite_c_middle_inclusion_defect_factors N hN q eA k heA hkf hneg
  dsimp only [N, Triangle.mk] at u hu
  obtain ⟨k0,hk0⟩ := finite_quotient_suspension_comparison q
    (model.nu.functor.obj (Y.obj model.auxiliary))
  let i := XModLambdaN.incl ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q
  let j := S.map (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q)
  let vg := S.map (XModLambdaN.map g q)
  let vu := S.map u
  have hinc : i≫k.hom=j≫(𝟙 _+vg≫vu) := by
    change i≫k.hom-j=j≫(vg≫vu) at hu
    rw [Preadditive.comp_add,Category.comp_id]
    exact (sub_eq_iff_eq_add.mp hu).trans (add_comm _ _)
  have hEta : j≫(k0.inv≫k.hom)=i≫k.hom := by
    change (S.map (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q))≫(k0.inv≫k.hom)=i≫k.hom
    rw [←hk0]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hghost : SphereGhost ((k0.inv≫k.hom)-(𝟙 _+vg≫vu)) := by
    apply finite_c_shifted_quotient_endomorphism_ghost Y q hq
    change j≫((k0.inv≫k.hom)-(𝟙 _+vg≫vu))=0
    rw [Preadditive.comp_sub,hEta,hinc,sub_self]
  have hfgQ : Q.map f≫Q.map g=0 := by
    have hfg0 : f≫g=0 := comp_distTriang_mor_zero₁₂ (Triangle.mk f g h) hN
    rw [←Functor.map_comp,hfg0,Functor.map_zero]
  have hfg : (eA.hom≫S.map (XModLambdaN.map f q))≫vg=0 := by
    change (eA.hom≫S.map (Q.map f))≫S.map (Q.map g)=0
    rw [Category.assoc,←Functor.map_comp,hfgQ,Functor.map_zero,comp_zero]
  exact finite_c_normalize_middle_iso L hCells i j k0 k vg vu
    (XModLambdaN.map (S.map f) q) (eA.hom≫S.map (XModLambdaN.map f q))
    hinc hkf hfg hghost

/-- On the finite third-vertex branch all finite-cell, negative-Hom and
strict-tail requirements are produced from the actual normalized coordinates.
Only the two distinguished mapped rows remain inputs from the finite-first
construction and its suspended instance. -/
private theorem finite_c_middle_suspension_comparison_of_coordinates
    (X Y Z : ClassicalObject) (hZ : ghost_cells_literal_finite_source_case Z)
    (ef eg : ℕ) {A C : SyntheticSpectrum}
    (aCoord : A ≅ (SyntheticCategory.biShift (0,(ef:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (cCoord : C ≅ (SyntheticCategory.biShift (0,-(eg:ℤ))).obj
      (model.nu.functor.obj (Z.obj model.auxiliary)))
    (f : A ⟶ model.nu.functor.obj (Y.obj model.auxiliary))
    (g : model.nu.functor.obj (Y.obj model.auxiliary) ⟶ C)
    (h : C ⟶ A⟦(1:ℤ)⟧)
    (hN : Triangle.mk f g h ∈ distTriang SyntheticSpectrum)
    (q : ℕ) (hq : 0<q)
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (eC : XModLambdaN (C⟦(1:ℤ)⟧) q ≅ (XModLambdaN C q)⟦(1:ℤ)⟧)
    (heC : XModLambdaN.incl (C⟦(1:ℤ)⟧) q≫eC.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl C q))
    (eSA : XModLambdaN ((A⟦(1:ℤ)⟧)⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (A⟦(1:ℤ)⟧) q)⟦(1:ℤ)⟧)
    (heSA : XModLambdaN.incl ((A⟦(1:ℤ)⟧)⟦(1:ℤ)⟧) q≫eSA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl (A⟦(1:ℤ)⟧) q))
    (hR0 : Triangle.mk (XModLambdaN.map f q) (XModLambdaN.map g q)
      (XModLambdaN.map h q≫eA.hom) ∈ distTriang SyntheticSpectrum)
    (hR1 : Triangle.mk (XModLambdaN.map (f⟦(1:ℤ)⟧') q)
      (XModLambdaN.map (g⟦(1:ℤ)⟧') q)
      (-(XModLambdaN.map (h⟦(1:ℤ)⟧') q≫eSA.hom)) ∈ distTriang SyntheticSpectrum) :
    ∃ eB : XModLambdaN ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q ≅
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)⟦(1:ℤ)⟧,
      XModLambdaN.incl ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q≫eB.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) q) ∧
      XModLambdaN.map (f⟦(1:ℤ)⟧') q≫eB.hom=
        eA.hom≫(XModLambdaN.map f q)⟦(1:ℤ)⟧' := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let bCoord : model.nu.functor.obj (Y.obj model.auxiliary) ≅
      (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (Y.obj model.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  have hneg : ∀ z : (SyntheticCategory.biShift (0,-(q:ℤ))).obj C ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q, z=0 := by
    intro z
    exact finite_c_unsuspended_negative_hom Z Y hZ (0,-(eg:ℤ)) (0,0) q hq
      (by dsimp only; omega) cCoord bCoord z
  let saCoord : A⟦(1:ℤ)⟧ ≅ (SyntheticCategory.biShift (1,(ef:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) :=
    S.mapIso aCoord ≪≫ (SyntheticCategory.biShift_compat 1).symm.app _ ≪≫
      (biShiftAddIso (0,(ef:ℤ)) (1,0) (1,(ef:ℤ)) (by ext <;> simp)).app _
  have hstrict : XModLambdaN.map (h⟦(1:ℤ)⟧') q≫eSA.hom=
      eC.hom≫(XModLambdaN.map h q)⟦(1:ℤ)⟧' :=
    finite_quotient_suspension_naturality_finite_source Z X hZ
      (0,-(eg:ℤ)) (1,(ef:ℤ)) q hq (by dsimp only; omega) cCoord saCoord
      eC eSA heC heSA h
  have hCL : ∃ L : ℕ, SphereCells ((XModLambdaN C q)⟦(1:ℤ)⟧) L := by
    rcases sphereCells_literal_finite_source Z hZ with h1 | h2
    · exact ⟨2, sphereCells_ordinaryShift 1 (sphereCells_quotient q
        (SphereCells.iso cCoord (sphereCells_biShift (0,-(eg:ℤ)) h1)))⟩
    · exact ⟨4, sphereCells_ordinaryShift 1 (sphereCells_quotient q
        (SphereCells.iso cCoord (sphereCells_biShift (0,-(eg:ℤ)) h2)))⟩
  obtain ⟨L,hCells⟩ := hCL
  exact finite_c_middle_suspension_comparison Y f g h hN q hq L hCells hneg
    eA heA eC eSA hstrict hR0 hR1

/-- Rotate the already constructed mapped row using the same middle
comparison's strict first-arrow square. The literal negative tail is retained. -/
private theorem finite_c_public_row_of_middle_comparison
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (hR0 : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q≫eA.hom) ∈ distTriang SyntheticSpectrum)
    (hf : XModLambdaN.map (N.mor₁⟦(1:ℤ)⟧') q≫eB.hom=
      eA.hom≫(XModLambdaN.map N.mor₁ q)⟦(1:ℤ)⟧') :
    Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
      (-(XModLambdaN.map (N.mor₁⟦(1:ℤ)⟧') q≫eB.hom)) ∈ distTriang SyntheticSpectrum := by
  let R0 := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
    (XModLambdaN.map N.mor₃ q≫eA.hom)
  let R := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (-(XModLambdaN.map (N.mor₁⟦(1:ℤ)⟧') q≫eB.hom))
  let E : R ≅ R0.rotate := Triangle.isoMk R R0.rotate (Iso.refl _) (Iso.refl _) eA
    (by simp only [R,R0,Triangle.mk,Triangle.rotate,Iso.refl_hom,Category.id_comp,Category.comp_id])
    (by simp only [R,R0,Triangle.mk,Triangle.rotate,Iso.refl_hom,Category.id_comp])
    (by
      change (-(XModLambdaN.map (N.mor₁⟦(1:ℤ)⟧') q≫eB.hom))≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (𝟙 _)=
          eA.hom≫(-(XModLambdaN.map N.mor₁ q)⟦(1:ℤ)⟧')
      rw [CategoryTheory.Functor.map_id,Category.comp_id,hf,Preadditive.comp_neg])
  exact isomorphic_distinguished R0.rotate (rot_of_distTriang R0 hR0) R E

end
end KIP126.Literature.Standard.Internal.GhostResearch
