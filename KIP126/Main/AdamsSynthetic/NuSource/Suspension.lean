module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements
public import KIP126.Literature.AdamsSynthetic.Statements
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs
public import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Localization.Recovery.Proofs
public import KIP126.Def.StableHomotopy.Context.Mapping.Data
public import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
public import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

@[expose] public section

/-! Naturality of the specified suspension comparison on the actual classical ν map. -/

namespace KIP126.Main.AdamsSynthetic

section NuSourceProof
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
    {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 4000000 in
open KIP126.Steenrod.Milnor in
open scoped BigOperators in
/-- The specified suspension comparison is natural on the actual classical ν.
The proof uses the same triangle-lift and realization-kernel inputs, sphere
separation, and the constructed reduced Milnor coordinates. -/
private theorem nu_suspension_square (D : AdamsComparison H M Syn)
    [SymmetricCategory C] [MonoidalPreadditive C]
    [∀ Z : C, (tensorRight Z).CommShift ℤ]
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
    (B : Mod2ReducedMilnorBasis H R) (sep : ClassicalSphereSeparated H)
    (hlift : KIP126.Synthetic.SyntheticTriangleLiftComparison H D.nu)
    (kernel : RealizationKernel D) :
    D.nu.functor.map ((shiftFunctor C (1:ℤ)).map D.hopfAndDetector.nuMap) ≫
        (D.nu.suspensionIso SphereSpectrum).hom =
      (D.nu.suspensionIso (Sphere (C:=C) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map D.hopfAndDetector.nuMap) := by
  have word_degree_ge_length {s : ℕ} {t : ℤ} (d : MilnorWord s t) :
      (s : ℤ) ≤ t := by
    have hslot (i : Fin s) : 1 ≤ slotWeight (d.val i) := by
      apply Nat.one_le_iff_ne_zero.mpr
      have hp : 0 < slotWeight (d.val i) := by
        change 0 < (d.val i).sum (fun j n => n • (2^(j+1)-1))
        apply Finsupp.sum_pos _ (d.property.2 i)
        intro j hj
        have hn : 0 < d.val i j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
        have hw : 0 < 2^(j+1)-1 := by
          have hh : 2 ≤ 2^(j+1) := by
            rw [pow_succ]
            have := Nat.one_le_pow j 2 (by decide)
            omega
          omega
        exact Nat.mul_pos hn hw
      omega
    rw [← d.property.1]
    calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, (slotWeight (d.val i) : ℤ) :=
        Finset.sum_le_sum (fun i _ => by exact_mod_cast hslot i)
      _ = wordDegree d.val := rfl

  have negative_sphere_zero (H : Mod2EilenbergMacLane (C:=C))
      (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (sep : ClassicalSphereSeparated H)
      (n : ℤ) (hn : n < 0) (a : HomotopyGroup n (SphereSpectrum : C)) : a = 0 := by
    have hzero (s : ℕ) : Subsingleton
        (HomotopyGroup n (H.HF2 ⊗ adamsTower H.unit SphereSpectrum s)) := by
      letI : IsEmpty (MilnorWord s (n+s)) := ⟨fun d => by
        have hd := word_degree_ge_length d
        omega⟩
      exact (sphereTowerHomologyWordEquiv H R K B s n).injective.subsingleton
    have hlift (s : ℕ) : ∃ b : HomotopyGroup n (adamsTower H.unit SphereSpectrum s),
        b ≫ adamsTowerMap H.unit SphereSpectrum 0 s (Nat.zero_le _) = a := by
      induction s with
      | zero => exact ⟨a, by simp⟩
      | succ s ih =>
        obtain ⟨b,hb⟩ := ih
        let T := adamsResolutionTriangle H.unit (SphereSpectrum : C) s
        have hb0 : b ≫ T.mor₂ = 0 := (hzero s).elim _ _
        obtain ⟨c,hc⟩ := T.coyoneda_exact₂
          (adamsResolutionTriangle_distinguished H.unit SphereSpectrum s) b hb0
        refine ⟨c, ?_⟩
        rw [adamsTowerMap_succ H.unit SphereSpectrum 0 s (Nat.zero_le s)]
        change c ≫ (T.mor₁ ≫ adamsTowerMap H.unit SphereSpectrum 0 s _) = a
        rw [← Category.assoc, ← hc, hb]
    apply sep n a
    intro s
    obtain ⟨b,hb⟩ := hlift s
    change a ∈ LinearMap.range
      (inducedMap (adamsTowerMap H.unit SphereSpectrum 0 (s:ℤ).toNat _) n).toIntLinearMap
    simp only [Int.toNat_natCast]
    exact ⟨b,hb⟩

  have sphere_hom_zero_of_lt (H : Mod2EilenbergMacLane (C:=C))
      (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (sep : ClassicalSphereSeparated H)
      (m n : ℤ) (hmn : m < n) (z : Sphere (C := C) m ⟶ Sphere n) : z = 0 := by
    let F := shiftFunctor C (-n)
    let a : Sphere (C := C) (m-n) ≅ F.obj (Sphere m) :=
      (shiftFunctorAdd' C m (-n) (m-n) (by omega)).app (𝟙_ C)
    let b : F.obj (Sphere (C := C) n) ≅ 𝟙_ C :=
      (shiftFunctorCompIsoId C n (-n) (by omega)).app (𝟙_ C)
    have hz := negative_sphere_zero H R K B sep (m-n) (by omega)
      (a.hom ≫ F.map z ≫ b.hom)
    apply F.map_injective
    rw [Functor.map_zero]
    apply (cancel_mono b.hom).mp
    apply (cancel_epi a.hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hz

  have sphere_iso_hom_zero_of_lt (H : Mod2EilenbergMacLane (C:=C))
      (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (sep : ClassicalSphereSeparated H)
      {A B' : C} (m n : ℤ) (hmn : m < n)
      (a : A ≅ Sphere (C := C) m) (b : B' ≅ Sphere (C := C) n)
      (z : A ⟶ B') : z = 0 := by
    have hz := sphere_hom_zero_of_lt H R K B sep m n hmn (a.inv ≫ z ≫ b.hom)
    apply (cancel_mono b.hom).mp
    apply (cancel_epi a.inv).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hz

  have tensorRight_fullyFaithful_of_inverse (A Z : C)
      (e : A ⊗ Z ≅ 𝟙_ C) : (tensorRight A).Full ∧ (tensorRight A).Faithful := by
    have compIso (P Q : C) (e : P ⊗ Q ≅ 𝟙_ C) :
        tensorRight P ⋙ tensorRight Q ≅ 𝟭 C := by
      refine NatIso.ofComponents (fun X =>
        (α_ X P Q) ≪≫ (tensorLeft X).mapIso e ≪≫ (ρ_ X)) ?_
      intro X Y f
      change (f ▷ P ▷ Q) ≫ ((α_ Y P Q).hom ≫ (Y ◁ e.hom) ≫ (ρ_ Y).hom) =
        ((α_ X P Q).hom ≫ (X ◁ e.hom) ≫ (ρ_ X).hom) ≫ f
      simp only [Category.assoc]
      rw [associator_naturality_left_assoc]
      rw [← whisker_exchange_assoc]
      rw [rightUnitor_naturality]
    let i := compIso A Z e
    let j := compIso Z A ((β_ Z A) ≪≫ e)
    letI : (tensorRight Z).Faithful := Functor.Faithful.of_comp_iso j
    exact ⟨Functor.Full.of_comp_faithful_iso i, Functor.Faithful.of_comp_iso i⟩

  have sphere_tensorRight_fullyFaithful (n : ℤ)
      [(tensorRight (Sphere (C := C) (-n))).CommShift ℤ] :
      (tensorRight (Sphere (C := C) n)).Full ∧
        (tensorRight (Sphere (C := C) n)).Faithful := by
    let e : (Sphere (C := C) n) ⊗ Sphere (-n) ≅ 𝟙_ C :=
      ((tensorRight (Sphere (C := C) (-n))).commShiftIso n).app (𝟙_ C) ≪≫
        (shiftFunctor C n).mapIso (λ_ (Sphere (C := C) (-n))) ≪≫
        (shiftFunctorCompIsoId C (-n) n (by omega)).app (𝟙_ C)
    exact tensorRight_fullyFaithful_of_inverse _ _ e

  have scalar_end_cancellation
      (A B Z : C) [(tensorRight A).Full] [(tensorRight Z).Faithful]
      (e : B ⊗ Z ≅ A) (f : A ⟶ B) (κ : A ⟶ A)
      (hκ : ((f ▷ Z) ≫ e.hom) ≫ κ = (f ▷ Z) ≫ e.hom) :
      κ ≫ f = f := by
    let scalar (c : 𝟙_ C ⟶ 𝟙_ C) (X : C) : X ⟶ X :=
      (λ_ X).inv ≫ (c ▷ X) ≫ (λ_ X).hom
    have scalar_natural (c : 𝟙_ C ⟶ 𝟙_ C) {X Y : C} (g : X ⟶ Y) :
        scalar c X ≫ g = g ≫ scalar c Y := by
      dsimp [scalar]
      simp only [Category.assoc]
      rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    have scalar_tensor (c : 𝟙_ C ⟶ 𝟙_ C) (X Y : C) :
        scalar c (X ⊗ Y) = (scalar c X) ▷ Y := by
      dsimp [scalar]
      simp only [leftUnitor_tensor_inv, leftUnitor_tensor_hom,
        whiskerRight_tensor, comp_whiskerRight, Category.assoc,
        Iso.hom_inv_id_assoc]
    obtain ⟨c, hc⟩ := (tensorRight A).map_surjective
      ((λ_ A).hom ≫ κ ≫ (λ_ A).inv)
    change c ▷ A = (λ_ A).hom ≫ κ ≫ (λ_ A).inv at hc
    have hscalar : scalar c A = κ := by
      dsimp [scalar]
      rw [hc]
      simp
    have hwhisker : (f ▷ Z) ≫ (scalar c B ▷ Z) = f ▷ Z := by
      apply (cancel_mono e.hom).mp
      rw [← scalar_tensor]
      rw [Category.assoc, scalar_natural, hscalar]
      simpa only [Category.assoc] using hκ
    have hright : f ≫ scalar c B = f := by
      apply (tensorRight Z).map_injective
      change (f ≫ scalar c B) ▷ Z = f ▷ Z
      rw [comp_whiskerRight]
      exact hwhisker
    rw [← hscalar, scalar_natural, hright]

  have lambda_injective_below_diagonal (D : AdamsComparison H M Syn)
      (m wt : ℤ) (hw : wt ≤ m + 1) :
      LambdaInjectiveAt m wt (S_0_0 : Syn) := by
    letI := D.shiftAdditive (0,-1)
    letI := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).faithful
    let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := Syn) m wt)
    let T := XModLambdaN.cofiberTriangle (S_0_0 : Syn) 1
    let e₀ : U ≅ Smn (Syn := Syn) m (wt-1) :=
      (SyntheticCategory.biShift_comp (m,wt) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp [sub_eq_add_neg])
    let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := Syn) (m+1) (wt-1) :=
      (shiftFunctor Syn (1 : ℤ)).mapIso e₀ ≪≫
        (SyntheticCategory.biShift_compat (Syn := Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (m,wt-1) (1,0)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp)
    have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
      intro q
      haveI : Subsingleton (PageRepresentatives.Ambient H SphereSpectrum (wt-m-2,wt-1)) :=
        adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
          2 (wt-m-2) (wt-1) (by omega)
      have hz : ∀ a : BiHom (m+1) (wt-1) (XModLambdaN (S_0_0 : Syn) 1), a = 0 := by
        intro a
        have hp : wt - 1 - (wt-m-2) = m+1 := by omega
        have hsub : Subsingleton (BiHom (wt-1-(wt-m-2)) (wt-1)
            (XModLambdaN (S_0_0 : Syn) 1)) :=
          (D.sphereFirstQuotient (wt-m-2) (wt-1)).injective.subsingleton
        rw [hp] at hsub
        exact @Subsingleton.elim _ hsub a 0
      apply (cancel_epi e₁.inv).mp
      simpa only [comp_zero] using hz (e₁.inv ≫ q)
    intro a b hab
    have hpre : SyntheticCategory.lam.app (Smn (Syn := Syn) m wt) ≫ (a-b) = 0 := by
      rw [Preadditive.comp_sub]
      apply sub_eq_zero.mpr
      simpa only [lambdaAction, Category.assoc, cancel_epi] using hab
    have hf : (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ T.mor₁ = 0 := by
      change (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ lambdaPow 1 S_0_0 = 0
      rw [lambdaPow_one D.shiftCoherence]
      rw [SyntheticCategory.lam.naturality]
      exact hpre
    have hfs : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' ≫
        T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      rw [← Functor.map_comp, hf, Functor.map_zero]
    obtain ⟨q,hq⟩ := T.coyoneda_exact₁
      (HasFunctorialCofiber.cofib_distinguished _) _ hfs
    have hz : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' = 0 := by
      rw [hq, hQ q, zero_comp]
    have hz' : (SyntheticCategory.biShift (0,-1)).map (a-b) = 0 := by
      apply (shiftFunctor Syn (1 : ℤ)).map_injective
      simpa only [Functor.map_zero] using hz
    apply sub_eq_zero.mp
    apply (SyntheticCategory.biShift (0,-1)).map_injective
    simpa only [Functor.map_zero] using hz'

  have lambda_powers_injective_of_lower_weights
      (coh : BiShiftCoherence Syn) (m wt : ℤ) (X : Syn)
      (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
      LambdaPowersInjectiveAt m wt X := by
    have one (k : ℕ) : Function.Injective (fun a :
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := Syn) m wt) ⟶ X =>
        SyntheticCategory.lam.app _ ≫ a) := by
      let e : Smn (Syn := Syn) m (wt-k) ≅
          (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn m wt) :=
        eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
          ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).app S_0_0).symm
      intro a b hab
      apply (cancel_epi e.hom).mp
      apply h (wt-k) (by omega)
      dsimp only [lambdaAction]
      have hc : SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ a) =
          SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ b) := by
        have hn := SyntheticCategory.lam.naturality e.hom
        dsimp only [Functor.id_map] at hn
        rw [← Category.assoc, ← Category.assoc, ← hn]
        simpa only [Category.assoc] using
          congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map e.hom ≫ z) hab
      exact congrArg (fun z => _ ≫ _ ≫ z) hc
    have powers (k : ℕ) : Function.Injective (fun a : BiHom m wt X =>
        lambdaPow k (Smn m wt) ≫ a) := by
      induction k with
      | zero =>
        intro a b hab
        exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn m wt))).mp hab
      | succ k ih =>
        intro a b hab
        apply ih
        apply one k
        rw [lambdaPow_add coh k 1 (k+1) rfl, lambdaPow_one coh] at hab
        have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := Syn) m wt))).mp
          (by simpa only [Category.assoc] using hab)
        have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := Syn) m wt))
        dsimp only [Functor.id_map] at hn
        change (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
          (SyntheticCategory.lam.app (Smn m wt) ≫ a) =
          (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
          (SyntheticCategory.lam.app (Smn m wt) ≫ b) at hc
        rw [← Category.assoc, ← Category.assoc] at hc
        rw [hn] at hc
        simpa only [Category.assoc] using hc
    intro k a b hab
    apply powers k
    dsimp only [lambdaMultiply] at hab
    have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
    exact (cancel_epi ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
      (by simpa only [Category.assoc] using hc)

  have low_realization_zero_iff (D : AdamsComparison H M Syn)
      (kernel : RealizationKernel D) {m wt : ℤ} (hw : wt ≤ m+1)
      (a : BiHom m wt (S_0_0 : Syn)) : D.recovery.realization.map a = 0 ↔ a = 0 := by
    letI := D.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts D.recovery.realization
    constructor
    · intro ha
      obtain ⟨k,hk⟩ := (kernel .sphere m wt a).mp ha
      have hi := lambda_powers_injective_of_lower_weights D.shiftCoherence m wt
        (S_0_0 : Syn) (fun wt' h => lambda_injective_below_diagonal D m wt' (by omega))
      apply hi k
      simpa only [lambdaMultiply, comp_zero] using hk
    · rintro rfl
      exact D.recovery.realization.map_zero _ _

  have third_arrow_unique_of_no_return
      {A B E : C} (f : A ⟶ B) (g : B ⟶ E) (h h' : E ⟶ A⟦(1:ℤ)⟧)
      (hT : Triangle.mk f g h ∈ distTriang C)
      (hT' : Triangle.mk f g h' ∈ distTriang C)
      (hzero : ∀ z : A⟦(1:ℤ)⟧ ⟶ E, z = 0) : h = h' := by
    obtain ⟨c,hc,hc'⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g h') hT hT' (𝟙 A) (𝟙 B) (by
        change f ≫ 𝟙 B = 𝟙 A ≫ f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
    change E ⟶ E at c
    change g ≫ c = 𝟙 B ≫ g at hc
    change h ≫ (shiftFunctor C (1:ℤ)).map (𝟙 A) = c ≫ h' at hc'
    have hz : g ≫ (c - 𝟙 E) = 0 := by
      simpa only [Triangle.mk_mor₂, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, sub_eq_zero] using hc
    obtain ⟨z,hz'⟩ := (Triangle.mk f g h).yoneda_exact₃ hT (c-𝟙 E) hz
    have he : c = 𝟙 E := by
      apply sub_eq_zero.mp
      rw [hz', hzero z, comp_zero]
    rw [(shiftFunctor C (1:ℤ)).map_id A, Category.comp_id, he, Category.id_comp] at hc'
    exact hc'

  have realized_triangle_lift_third (D : AdamsComparison H M Syn)
      (T : Triangle C) (hT : T ∈ distTriang C)
      (L : KIP126.Synthetic.SyntheticTriangleLift D.nu T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := D.realizationShift
      D.recovery.nuRealizationIso.inv.app T.obj₃ ≫
        D.recovery.realization.map (L.connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom) ≫
        (D.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor C (1:ℤ)).map (D.recovery.nuRealizationIso.hom.app T.obj₁) = T.mor₃ := by
    letI := D.realizationShift
    letI := D.realizationExact
    let F := D.recovery.realization
    let e := D.recovery.nuRealizationIso
    let U := Triangle.mk (D.nu.functor.map T.mor₁) (D.nu.functor.map T.mor₂)
      (L.connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom)
    let d := e.inv.app T.obj₃ ≫ F.map U.mor₃ ≫
      (F.commShiftIso (1:ℤ)).hom.app U.obj₁ ≫
      (shiftFunctor C (1:ℤ)).map (e.hom.app T.obj₁)
    have hU : U ∈ distTriang Syn := L.distinguished
    have hi : F.mapTriangle.obj U ≅ Triangle.mk T.mor₁ T.mor₂ d := by
      refine Triangle.isoMk _ _ (e.app T.obj₁) (e.app T.obj₂) (e.app T.obj₃) ?_ ?_ ?_
      · exact D.recovery.recovery_naturality T.mor₁
      · exact D.recovery.recovery_naturality T.mor₂
      · change (F.map U.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app U.obj₁) ≫
          (shiftFunctor C (1:ℤ)).map (e.hom.app T.obj₁) = e.hom.app T.obj₃ ≫ d
        dsimp only [d]
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have hd : Triangle.mk T.mor₁ T.mor₂ d ∈ distTriang C :=
      isomorphic_distinguished _ (F.map_distinguished U hU) _ hi.symm
    change d = T.mor₃
    exact third_arrow_unique_of_no_return T.mor₁ T.mor₂ d T.mor₃ hd hT hzero

  have realization_map_lambda_isIso (D : AdamsComparison H M Syn) (X : Syn) :
      IsIso (D.recovery.realization.map (SyntheticCategory.lam.app X)) := by
    letI := D.recovery.localization.map_lambda_isIso X
    change IsIso (D.recovery.equivalence.functor.map
      (D.recovery.localization.reflector.map (SyntheticCategory.lam.app X)))
    infer_instance

  have realized_suspension_normalization_on_third (D : AdamsComparison H M Syn)
      (T : Triangle C) (hT : T ∈ distTriang C)
      (L : KIP126.Synthetic.SyntheticTriangleLift D.nu T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := D.realizationShift
      letI := realization_map_lambda_isIso D (D.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
      T.mor₃ ≫ (D.recovery.nuRealizationIso.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
        inv (D.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
        D.recovery.realization.map (D.nu.boundaryLandingIso T.obj₁).hom ≫
        (D.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor C (1:ℤ)).map (D.recovery.nuRealizationIso.hom.app T.obj₁)) = T.mor₃ := by
    letI := D.realizationShift
    letI := realization_map_lambda_isIso D (D.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
    let F := D.recovery.realization
    let e := D.recovery.nuRealizationIso
    have hf : e.inv.app T.obj₃ ≫ F.map L.connecting =
        T.mor₃ ≫ e.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
          inv (F.map (SyntheticCategory.lam.app _)) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (D.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp, L.factorization]
      have hn := e.inv.naturality T.mor₃
      exact hn.symm
    have hd := realized_triangle_lift_third D T hT L hzero
    change e.inv.app T.obj₃ ≫ F.map (L.connecting ≫ (D.nu.boundaryLandingIso T.obj₁).hom) ≫
      (F.commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor C (1:ℤ)).map (e.hom.app T.obj₁) = T.mor₃ at hd
    simp only [F.map_comp, Category.assoc] at hd
    rw [← Category.assoc (e.inv.app T.obj₃) (F.map L.connecting), hf] at hd
    simpa only [Category.assoc] using hd

  have positive_filtration_of_tensor_zero
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      AdamsFiltrationAtLeast H f 1 := by
    have hu : f ≫ adamsUnit H.unit Y = 0 := by
      rw [adamsUnit_naturality, hf, comp_zero]
    obtain ⟨a,ha⟩ := (adamsResolutionTriangle H.unit Y 0).coyoneda_exact₂
      (adamsResolutionTriangle_distinguished H.unit Y 0) f hu
    change f = a ≫ adamsTowerStep H.unit Y 0 at ha
    refine ⟨a,?_⟩
    change a ≫ adamsTowerMap H.unit Y 0 1 (by decide) = f
    simpa only [adamsTowerMap,adamsTowerComposite,adamsResolutionTriangle,
      eqToHom_refl,Category.id_comp,Category.comp_id,Nat.add_zero] using ha.symm

  have rotated_cofiber_homology_short_exact
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      KIP126.Synthetic.HomologyShortExact H
        (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f)).rotate := by
    let U := (HoCofiberSequence.ofMorphism f).map (tensorLeft H.HF2)
    let T := Triangle.mk U.f U.g U.h
    have hT : T ∈ distTriang C := U.distinguished
    have hzero : T.mor₁ = 0 := hf
    haveI : Mono T.mor₂ := T.mono₂ hT hzero
    intro n
    refine ⟨?_,?_,?_⟩
    · intro a b hab
      exact (cancel_mono T.mor₂).1 hab
    · intro a
      change a ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibδ f) = 0 ↔
        ∃ b, b ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibι f) = a
      constructor
      · intro ha
        have hz : a ≫ T.mor₃ = 0 := by
          change a ≫ ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0
          rw [←Category.assoc,ha,zero_comp]
        obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hz
        exact ⟨b,hb.symm⟩
      · rintro ⟨b,rfl⟩
        have hh := comp_distTriang_mor_zero₂₃ T hT
        change (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
          ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0 at hh
        have hg : (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
            (H.HF2 ◁ HasFunctorialCofiber.cofibδ f) = 0 := by
          apply (cancel_mono (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X)).1
          change (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
            ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫
              (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X)) = 0 at hh
          simpa only [Category.assoc,zero_comp] using hh
        rw [Category.assoc,hg,comp_zero]
    · intro a
      let e := (((tensorLeft H.HF2).commShiftIso (1:ℤ)).app X)
      obtain ⟨b,hb⟩ := T.coyoneda_exact₁ hT (a ≫ e.hom) (by
        rw [hzero,Functor.map_zero,comp_zero])
      refine ⟨b,?_⟩
      apply (cancel_mono e.hom).1
      change (b ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibδ f)) ≫ e.hom = a ≫ e.hom
      change a ≫ e.hom = b ≫ ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ e.hom) at hb
      simpa only [Category.assoc] using hb.symm

  have rotated_cofiber_positive_filtration
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).Additive]
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      AdamsFiltrationAtLeast H
        (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f)).rotate.mor₃ 1 := by
    apply positive_filtration_of_tensor_zero
    change (tensorLeft H.HF2).map (-((shiftFunctor C (1:ℤ)).map f)) = 0
    rw [Functor.map_neg]
    apply neg_eq_zero.mpr
    apply (cancel_mono (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app Y)).1
    have hn := ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.naturality f
    change (tensorLeft H.HF2).map ((shiftFunctor C (1:ℤ)).map f) ≫
        ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app Y =
      ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X ≫
        (shiftFunctor C (1:ℤ)).map (H.HF2 ◁ f) at hn
    calc
      _ = _ := hn
      _ = _ := by rw [hf,Functor.map_zero,comp_zero,zero_comp]

  have normalization_fixes_shift_of_tensor_zero (D : AdamsComparison H M Syn)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
      (hlift : KIP126.Synthetic.SyntheticTriangleLiftComparison H D.nu)
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0)
      (hzero : ∀ z : Y⟦(1:ℤ)⟧ ⟶ X⟦(1:ℤ)⟧, z = 0) :
      letI := D.realizationShift
      letI := realization_map_lambda_isIso D (D.nu.functor.obj (Y⟦(1:ℤ)⟧))
      (shiftFunctor C (1:ℤ)).map f ≫
        (D.recovery.nuRealizationIso.inv.app (Y⟦(1:ℤ)⟧) ≫
          inv (D.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          D.recovery.realization.map (D.nu.boundaryLandingIso Y).hom ≫
          (D.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor C (1:ℤ)).map (D.recovery.nuRealizationIso.hom.app Y)) =
        (shiftFunctor C (1:ℤ)).map f := by
    letI := D.realizationShift
    letI := realization_map_lambda_isIso D (D.nu.functor.obj (Y⟦(1:ℤ)⟧))
    let T := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f)).rotate
    have hT : T ∈ distTriang C := rot_of_distTriang _
      (HasFunctorialCofiber.cofib_distinguished f)
    obtain ⟨L,hL⟩ := hlift T hT
      (rotated_cofiber_positive_filtration f hf)
      (rotated_cofiber_homology_short_exact f hf)
    have ht := realized_suspension_normalization_on_third D T hT L hzero
    change (-(shiftFunctor C (1:ℤ)).map f) ≫ _ = -(shiftFunctor C (1:ℤ)).map f at ht
    simpa only [T, Triangle.rotate_obj₁, Triangle.mk_obj₂, Preadditive.neg_comp, neg_inj] using ht

  have realized_boundary_square_of_normalization_natural (D : AdamsComparison H M Syn)
      {X Y : C} (f : X ⟶ Y) :
      letI := D.realizationShift
      let κ (A : C) : A⟦(1:ℤ)⟧ ⟶ A⟦(1:ℤ)⟧ :=
        letI := realization_map_lambda_isIso D (D.nu.functor.obj (A⟦(1:ℤ)⟧))
        D.recovery.nuRealizationIso.inv.app (A⟦(1:ℤ)⟧) ≫
          inv (D.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          D.recovery.realization.map (D.nu.boundaryLandingIso A).hom ≫
          (D.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor C (1:ℤ)).map (D.recovery.nuRealizationIso.hom.app A)
      (shiftFunctor C (1:ℤ)).map f ≫ κ Y = κ X ≫ (shiftFunctor C (1:ℤ)).map f →
        D.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
          (D.nu.boundaryLandingIso Y).hom) =
        D.recovery.realization.map ((D.nu.boundaryLandingIso X).hom ≫
          (shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map f)) := by
    letI := D.realizationShift
    dsimp only
    intro hk
    let F := D.recovery.realization
    let e := D.recovery.nuRealizationIso
    let G := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let S := shiftFunctor C (1:ℤ)
    letI (A : C) := realization_map_lambda_isIso D (D.nu.functor.obj (S.obj A))
    let β (A : C) : S.obj A ≅ F.obj (G.obj (D.nu.functor.obj (S.obj A))) :=
      (e.app (S.obj A)).symm ≪≫ (asIso (F.map (SyntheticCategory.lam.app _))).symm
    let j (A : C) : F.obj ((shiftFunctor Syn (1:ℤ)).obj (D.nu.functor.obj A)) ≅ S.obj A :=
      (F.commShiftIso (1:ℤ)).app _ ≪≫ S.mapIso (e.app A)
    have hβ : S.map f ≫ (β Y).hom = (β X).hom ≫
        F.map (G.map (D.nu.functor.map (S.map f))) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (D.nu.functor.obj (S.obj Y))))).mp
      dsimp only [β, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp]
      have hn := SyntheticCategory.lam.naturality (D.nu.functor.map (S.map f))
      change G.map (D.nu.functor.map (S.map f)) ≫ SyntheticCategory.lam.app _ =
        SyntheticCategory.lam.app _ ≫ D.nu.functor.map (S.map f) at hn
      rw [hn, F.map_comp]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      exact e.inv.naturality (S.map f)
    have hj : F.map ((shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map f)) ≫ (j Y).hom =
        (j X).hom ≫ S.map f := by
      have hn := (F.commShiftIso (1:ℤ)).hom.naturality (D.nu.functor.map f)
      change F.map ((shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map f)) ≫
        (F.commShiftIso (1:ℤ)).hom.app _ =
        (F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (F.map (D.nu.functor.map f)) at hn
      change F.map ((shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map f)) ≫
          ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app Y)) =
        ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app X)) ≫ S.map f
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← S.map_comp]
      have he := D.recovery.recovery_naturality f
      change F.map (D.nu.functor.map f) ≫ e.hom.app Y = e.hom.app X ≫ f at he
      rw [he]
    apply (cancel_epi (β X).hom).mp
    apply (cancel_mono (j Y).hom).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (β X).hom (F.map (G.map (D.nu.functor.map (S.map f)))), ← hβ]
    rw [← Category.assoc (F.map (D.nu.boundaryLandingIso X).hom)
      (F.map ((shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map f)))]
    rw [Category.assoc _ _ (j Y).hom, hj]
    dsimp only [β, j, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, F, e, S]
    simpa only [Category.assoc] using hk

  have suspension_square_of_boundary_square (N : NuFunctorData C Syn)
      {X Y : C} (f : X ⟶ Y)
      (hb : (SyntheticCategory.biShift (0,-1)).map
          (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
          (N.boundaryLandingIso Y).hom =
        (N.boundaryLandingIso X).hom ≫ (shiftFunctor Syn (1:ℤ)).map (N.functor.map f)) :
      N.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
        (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f) := by
    let G := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let j : SyntheticCategory.biShift (Syn:=Syn) (1,1) ⋙ G ≅ shiftFunctor Syn (1:ℤ) :=
      SyntheticCategory.biShift_comp (1,1) (0,-1) ≪≫ SyntheticCategory.biShift_compat 1
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_injective
    apply (cancel_mono (j.hom.app (N.functor.obj Y))).mp
    simp only [Functor.map_comp, Category.assoc]
    change G.map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y) =
      G.map (N.suspensionIso X).hom ≫
        G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
          j.hom.app (N.functor.obj Y)
    have hn := j.hom.naturality (N.functor.map f)
    change G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
      j.hom.app (N.functor.obj Y) = j.hom.app (N.functor.obj X) ≫
        (shiftFunctor Syn (1:ℤ)).map (N.functor.map f) at hn
    rw [hn]
    change G.map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        (G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y)) =
      (G.map (N.suspensionIso X).hom ≫ j.hom.app (N.functor.obj X)) ≫
        (shiftFunctor Syn (1:ℤ)).map (N.functor.map f) at hb
    simpa only [Category.assoc] using hb

  have suspension_square_of_realized_boundary_square (D : AdamsComparison H M Syn)
      (kernel : RealizationKernel D)
      (hb : D.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (D.nu.functor.map ((shiftFunctor C (1:ℤ)).map D.hopfAndDetector.nuMap)) ≫
          (D.nu.boundaryLandingIso SphereSpectrum).hom) =
        D.recovery.realization.map ((D.nu.boundaryLandingIso (Sphere (C:=C) 3)).hom ≫
          (shiftFunctor Syn (1:ℤ)).map (D.nu.functor.map D.hopfAndDetector.nuMap))) :
      D.nu.functor.map ((shiftFunctor C (1:ℤ)).map D.hopfAndDetector.nuMap) ≫
          (D.nu.suspensionIso SphereSpectrum).hom =
        (D.nu.suspensionIso (Sphere (C:=C) 3)).hom ≫
          (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map D.hopfAndDetector.nuMap) := by
    letI := D.realizationShift
    letI := D.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts D.recovery.realization
    let F := D.recovery.realization
    let S := shiftFunctor Syn (1:ℤ)
    let A := D.nu.functor.obj (Sphere (C:=C) 3)
    let B := D.nu.functor.obj SphereSpectrum
    have hinj : Function.Injective (fun a : A ⟶ B => F.map a) := by
      intro a b hab
      have hz : F.map ((nuSphereThree D).inv ≫ (a-b) ≫ D.nu.unitIso.hom) = 0 := by
        simp only [F.map_comp, Functor.map_sub, hab, sub_self, zero_comp, comp_zero]
      have ht := (low_realization_zero_iff D kernel (m:=3) (wt:=3) (by omega)
        ((nuSphereThree D).inv ≫ (a-b) ≫ D.nu.unitIso.hom)).mp hz
      apply sub_eq_zero.mp
      apply (cancel_mono D.nu.unitIso.hom).mp
      apply (cancel_epi (nuSphereThree D).inv).mp
      simpa only [Category.assoc, comp_zero, zero_comp] using ht
    have hshift : Function.Injective (fun a : S.obj A ⟶ S.obj B => F.map a) := by
      intro a b hab
      change F.map a = F.map b at hab
      have ha := S.map_preimage a
      have hb := S.map_preimage b
      have he : F.map (S.preimage a) = F.map (S.preimage b) := by
        apply (shiftFunctor C (1:ℤ)).map_injective
        apply (cancel_epi ((F.commShiftIso (1:ℤ)).hom.app A)).mp
        have hna := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage a)
        have hnb := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage b)
        change F.map (S.map (S.preimage a)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor C (1:ℤ)).map (F.map (S.preimage a)) at hna
        change F.map (S.map (S.preimage b)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor C (1:ℤ)).map (F.map (S.preimage b)) at hnb
        rw [ha] at hna
        rw [hb] at hnb
        rw [← hna, ← hnb, hab]
      calc a = S.map (S.preimage a) := ha.symm
           _ = S.map (S.preimage b) := congrArg S.map (hinj he)
           _ = b := hb
    apply suspension_square_of_boundary_square D.nu D.hopfAndDetector.nuMap
    apply (cancel_epi (D.nu.boundaryLandingIso (Sphere (C:=C) 3)).inv).mp
    apply hshift
    simpa only [Functor.map_comp, Category.assoc] using congrArg (fun z =>
      F.map (D.nu.boundaryLandingIso (Sphere (C:=C) 3)).inv ≫ z) hb

  letI := D.realizationShift
  let S := shiftFunctor C (1:ℤ)
  let Z := Sphere (C:=C) 3
  let f := D.hopfAndDetector.nuMap
  letI (X : C) := realization_map_lambda_isIso D (D.nu.functor.obj (S.obj X))
  let κ (X : C) : S.obj X ⟶ S.obj X :=
    D.recovery.nuRealizationIso.inv.app (S.obj X) ≫
      inv (D.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
      D.recovery.realization.map (D.nu.boundaryLandingIso X).hom ≫
      (D.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
      S.map (D.recovery.nuRealizationIso.hom.app X)
  have hneg (a : (𝟙_ C) ⟶ Z) : a = 0 := by
    exact sphere_iso_hom_zero_of_lt H R K B sep 0 3 (by omega)
      ((shiftFunctorZero C ℤ).app (𝟙_ C)).symm (Iso.refl _) a
  have hF : AdamsFiltrationAtLeast H f 1 := by
    have hu : f ≫ adamsUnit H.unit SphereSpectrum = 0 := by
      apply (cancel_mono (ρ_ H.HF2).hom).mp
      letI := H.homotopy_vanishes 3 (by decide)
      exact Subsingleton.elim _ _
    obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₂
      (adamsResolutionTriangle H.unit SphereSpectrum 0)
      (adamsResolutionTriangle_distinguished H.unit SphereSpectrum 0) f hu
    refine ⟨g, ?_⟩
    simpa [adamsTowerMap, adamsTowerComposite, adamsResolutionTriangle, Triangle.mk,
      adamsTower] using hg.symm
  have hf : H.HF2 ◁ f = 0 := by
    obtain ⟨g,hg⟩ := hF
    rw [← hg, whiskerLeft_comp, mod2_adamsTowerMap_eq_zero H R _ 0 1 (by decide), comp_zero]
  have hret (a : S.obj (𝟙_ C) ⟶ S.obj Z) : a = 0 := by
    have ha := S.map_preimage a
    rw [hneg (S.preimage a), Functor.map_zero] at ha
    exact ha.symm
  have hy : S.map f ≫ κ (𝟙_ C) = S.map f :=
    normalization_fixes_shift_of_tensor_zero D hlift f hf hret
  obtain ⟨hfullZ,hfaithZ⟩ := sphere_tensorRight_fullyFaithful 3
  letI : (tensorRight Z).Full := hfullZ
  letI : (tensorRight Z).Faithful := hfaithZ
  let q : Z ⊗ Z ⟶ Z := (f ▷ Z) ≫ (λ_ Z).hom
  have hq : H.HF2 ◁ q = 0 := by
    dsimp only [q]
    rw [whiskerLeft_comp]
    have hq' : H.HF2 ◁ (f ▷ Z) = 0 := by
      apply (cancel_epi (α_ H.HF2 Z Z).hom).mp
      rw [← associator_naturality_middle, hf, MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
    rw [hq', zero_comp]
  have hretq (a : S.obj Z ⟶ S.obj (Z ⊗ Z)) : a = 0 := by
    have ha := S.map_preimage a
    have hb := (tensorRight Z).map_preimage ((λ_ Z).hom ≫ S.preimage a)
    have hz := hneg ((tensorRight Z).preimage ((λ_ Z).hom ≫ S.preimage a))
    rw [hz, Functor.map_zero] at hb
    have hz' : S.preimage a = 0 := by
      apply (cancel_epi (λ_ Z).hom).mp
      simpa only [comp_zero] using hb.symm
    rw [hz', Functor.map_zero] at ha
    exact ha.symm
  have hxq : S.map q ≫ κ Z = S.map q :=
    normalization_fixes_shift_of_tensor_zero D hlift q hq hretq
  let e : S.obj (𝟙_ C) ⊗ Z ≅ S.obj Z :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app (𝟙_ C) ≪≫ S.mapIso (λ_ Z)
  let j : S.obj Z ⊗ Z ≅ S.obj (Z ⊗ Z) :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app Z
  have hj : (S.map f ▷ Z) ≫ e.hom = j.hom ≫ S.map q := by
    have hn := ((tensorRight Z).commShiftIso (1:ℤ)).hom.naturality f
    change (S.map f ▷ Z) ≫ ((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ C) =
      ((tensorRight Z).commShiftIso (1:ℤ)).hom.app Z ≫ S.map (f ▷ Z) at hn
    change (S.map f ▷ Z) ≫ (((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ C) ≫
      S.map (λ_ Z).hom) = _
    rw [← Category.assoc, hn, Category.assoc, ← S.map_comp]
    rfl
  have hκ : ((S.map f ▷ Z) ≫ e.hom) ≫ κ Z = (S.map f ▷ Z) ≫ e.hom := by
    rw [hj, Category.assoc, hxq]
  let a : S.obj Z ≅ Sphere (C:=C) 4 :=
    ((shiftFunctorAdd' C 3 1 4 (by omega)).app (𝟙_ C)).symm
  let ai : S.obj Z ⊗ Sphere (C:=C) (-4) ≅ 𝟙_ C :=
    (tensorRight (Sphere (C:=C) (-4))).mapIso a ≪≫
      ((tensorRight (Sphere (C:=C) (-4))).commShiftIso (4:ℤ)).app (𝟙_ C) ≪≫
      (shiftFunctor C (4:ℤ)).mapIso (λ_ (Sphere (C:=C) (-4))) ≪≫
      (shiftFunctorCompIsoId C (-4) 4 (by omega)).app (𝟙_ C)
  obtain ⟨hfullA,hfaithA⟩ := tensorRight_fullyFaithful_of_inverse
    (S.obj Z) (Sphere (C:=C) (-4)) ai
  letI : (tensorRight (S.obj Z)).Full := hfullA
  have hx : κ Z ≫ S.map f = S.map f :=
    scalar_end_cancellation (S.obj Z) (S.obj (𝟙_ C)) Z e (S.map f) (κ Z) hκ
  apply suspension_square_of_realized_boundary_square D kernel
  apply realized_boundary_square_of_normalization_natural D f
  exact hy.trans hx.symm

end

end NuSourceProof

end KIP126.Main.AdamsSynthetic
