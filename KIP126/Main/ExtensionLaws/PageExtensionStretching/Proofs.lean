module

public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.AdamsSynthetic.ExtensionLaws.PageExtensionStretching.Predicates
public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs

@[expose] public section

/-! The finite extension stretching law, proved from the stated
classical/synthetic comparisons on the same Adams towers. All finite quotient
representatives and filtration corrections refer to those comparisons. -/
namespace KIP126.Main.ExtensionLaws

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Literature.AdamsSynthetic

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

open CategoryTheory.Limits KIP126.SpectralSequence
open KIP126.Synthetic.SpectralSequence KIP126.Synthetic.PageExtension

open KIP126.Algebra KIP126.Classical.Adams.PageRepresentatives

set_option maxHeartbeats 1600000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A zero-length finite extension stretches because its actual E∞ equation
restricts along ρ, whose target map is injective in the common finite window. -/
private theorem finite_extension_zero_stretches
    (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
    (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
    (rEarlier rLater : ℕ) (s t : ℤ)
    (x : Ambient H (X.obj D.hopfAndDetector) (s,t))
    (y : Ambient H (Y.obj D.hopfAndDetector) (s+0,t+0))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent H f : ℤ) ≤ 0)
    (hx : IsCycle H (X.obj D.hopfAndDetector) ((rLater:ℤ)-1) (s,t) x)
    (hy : IsCycle H (Y.obj D.hopfAndDetector) ((rLater:ℤ)-1-0+normalizedExponent H f)
      (s+0,t+0) y)
    (W : FiniteExtensionWitness D X Y f rEarlier 0 s t x y) :
    FiniteExtension D X Y f rLater 0 s t x y := by
  have extension_zero_iff (D : AdamsComparison H M Syn)
      (A B : SyntheticObject) (g : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
      (p : ℤ × ℤ) (s : ℤ)
      (x : ((D.family.obj (A.obj D.nu D.hopfAndDetector)).sequence.ssData (s, p.1+s, p.2)).eInfty)
      (y : ((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData (s, p.1+s, p.2)).eInfty) :
      ExtensionEquation g (D.convergence A) (D.convergence B) p s 0 x
        (by simpa only [add_zero] using y) ↔
        (D.family.functor.map g).eInftyMap (s, p.1+s, p.2) x = y := by
    have elementMap_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
        elementMap x ≫ f = elementMap (f x) := by
      ext a
      simp [elementMap]
    have strict_fiber_elements (FC : FilteredComplex (ModuleCat.{v} ℤ))
        (n s k : ℤ) (x : FC.assocGraded s k) (y : FC.assocGraded (s+n) (k-1)) :
        Nonempty (FilteredComplex.Solutions.Fiber FC n s k (elementMap x) (elementMap y)) ↔
          ∃ (a : (Subobject.underlying.obj (FC.fil s k) : ModuleCat.{v} ℤ))
            (b : (Subobject.underlying.obj (FC.fil (s+n) (k-1)) : ModuleCat.{v} ℤ)),
            FC.filToAssocGraded s k a=x ∧ FC.filToAssocGraded (s+n) (k-1) b=y ∧
            FC.d k ((FC.fil s k).arrow a)=(FC.fil (s+n) (k-1)).arrow b := by
      constructor
      · rintro ⟨W⟩
        obtain ⟨hx,hy,he⟩ := (FilteredComplex.Solutions.mem_fiber_iff W.val).mp W.property
        refine ⟨W.val.1.hom (ULift.up 1),W.val.2.hom (ULift.up 1),?_,?_,?_⟩
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hx
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hy
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · exact congrArg (fun f => f.hom (ULift.up (1:ℤ))) he
      · rintro ⟨a,b,ha,hb,he⟩
        refine ⟨⟨(elementMap a,elementMap b),(FilteredComplex.Solutions.mem_fiber_iff _).mpr ⟨?_,?_,?_⟩⟩⟩
        · change elementMap a ≫ FC.filToAssocGraded s k=elementMap x
          rw [elementMap_comp,ha]
        · change elementMap b ≫ FC.filToAssocGraded (s+n) (k-1)=elementMap y
          rw [elementMap_comp,hb]
        · rw [←Category.assoc,elementMap_comp,elementMap_comp,elementMap_comp,he]
    have actual_extension_zero_comparison
        (A B : SyntheticObject) (g : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
        (p : ℤ×ℤ) (s : ℤ) :
        (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g (D.convergence A) p s).hom ≫
          (extensionComplex (nuCoefficientUnit H.unit D.nu) g p).assocGradedDiff s 1 =
        (D.family.functor.map g).eInftyMap (s,p.1+s,p.2) ≫
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom := by
      obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B g
      have hc := c.iso_compat (s,p.1+s,p.2)
      simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,
        SyntheticAdamsConvergence.toConvergence] at hc
      rw [hce] at hc
      have hd : (extensionComplex (nuCoefficientUnit H.unit D.nu) g p).assocGradedDiff s 1 =
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p := by
        haveI : Epi ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
        apply (cancel_epi ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded s p)).mp
        change _ ≫ (underlyingComplex (syntheticHomotopyMap g) (homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D.nu) g) p).assocGradedDiff s 1 = _
        rw [underlyingComplex_assocGradedDiff_compat_one]
        have hq : (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded s p ≫
            Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p =
            (c.filtration_compat s p).choose ≫ (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded s p := by
          exact cokernel.π_desc _ _ _
        rw [hq]
        congr 1
        apply (cancel_mono ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector)).F s p).arrow).mp
        rw [(homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D.nu) g s p).choose_spec]
        let k := (c.filtration_compat s p).choose
        have hk : k ≫ ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F s p).arrow =
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F s p).arrow ≫ c.aMap p :=
          (c.filtration_compat s p).choose_spec
        change k ≫
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F s p).arrow =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F s p).arrow ≫ c.aMap p at hk
        rw [hca] at hk
        exact hk.symm
      rw [hd]
      have transport {ι : Type} (P Q : ι → ModuleCat.{v} ℤ) (F : ∀i, P i ⟶ Q i)
          {i j : ι} (h : i=j) {U V : ModuleCat.{v} ℤ} (a : U ⟶ P i) (b : V ⟶ Q i)
          (g : U ⟶ V) (he : g≫b=a≫F i) :
          (a≫eqToHom (congrArg P h))≫F j=g≫(b≫eqToHom (congrArg Q h)) := by
        subst j
        simpa only [eqToHom_refl,Category.comp_id] using he.symm
      exact transport (ι:=ℤ×ℤ) (i:=(p.1+s-s,p.2)) (j:=p)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).associatedGraded s m)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).associatedGraded s m)
        (fun m => Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m)
        (show (p.1+s-s,p.2)=p by ext <;> simp)
        ((D.convergence A).identification (s,p.1+s,p.2)).hom
        ((D.convergence B).identification (s,p.1+s,p.2)).hom
        ((D.family.functor.map g).eInftyMap (s,p.1+s,p.2)) hc
    let FC := extensionComplex (nuCoefficientUnit H.unit D.nu) g p
    let xx := (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g (D.convergence A) p s).hom x
    let yy := (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom y
    have hcomp := ConcreteCategory.congr_hom (actual_extension_zero_comparison A B g p s) x
    have transport_zero (u : ℤ) (hu : u = s)
        (y' : ((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData (u, p.1+u, p.2)).eInfty)
        (hy : HEq y' y) :
        (∃ (a : (Subobject.underlying.obj (FC.fil s 1) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj (FC.fil u 0) : ModuleCat.{v} ℤ)),
          FC.filToAssocGraded s 1 a = xx ∧ FC.filToAssocGraded u 0 b =
            (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p u).hom y' ∧
          FC.d 1 ((FC.fil s 1).arrow a) = (FC.fil u 0).arrow b) ↔
        (∃ (a : (Subobject.underlying.obj (FC.fil s 1) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj (FC.fil s 0) : ModuleCat.{v} ℤ)),
          FC.filToAssocGraded s 1 a = xx ∧ FC.filToAssocGraded s 0 b = yy ∧
          FC.d 1 ((FC.fil s 1).arrow a) = (FC.fil s 0).arrow b) := by
      subst u
      cases hy
      rfl
    simp only [ExtensionEquation]
    rw [strict_fiber_elements]
    refine (and_congr Iff.rfl (transport_zero (s+0) (add_zero s)
      (by simpa only [add_zero] using y) (by change HEq (cast _ y) y; exact cast_heq _ _))).trans ?_
    constructor
    · rintro ⟨_, a, b, ha, hb, hd⟩
      have hdiff : FC.filDiff s 1 a = b := by
        apply (ModuleCat.mono_iff_injective (FC.fil s 0).arrow).mp inferInstance
        have hpres := ConcreteCategory.congr_hom (FC.differential_preserves s 1).choose_spec a
        exact hpres.trans hd
      have hgraded := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat s 1) a
      change FC.assocGradedDiff s 1 (FC.filToAssocGraded s 1 a) =
        FC.filToAssocGraded s 0 (FC.filDiff s 1 a) at hgraded
      rw [ha, hdiff, hb] at hgraded
      apply (ModuleCat.mono_iff_injective
        (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom).mp inferInstance
      exact hcomp.symm.trans hgraded
    · intro hxy
      refine ⟨le_refl _, ?_⟩
      haveI : Epi (FC.filToAssocGraded s 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (FC.filToAssocGraded s 1)).mp inferInstance xx
      refine ⟨a, FC.filDiff s 1 a, ha, ?_, ?_⟩
      · have hgraded := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat s 1) a
        change FC.assocGradedDiff s 1 (FC.filToAssocGraded s 1 a) =
          FC.filToAssocGraded s 0 (FC.filDiff s 1 a) at hgraded
        rw [ha] at hgraded
        apply hgraded.symm.trans
        apply hcomp.trans
        change (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom
          ((D.family.functor.map g).eInftyMap (s,p.1+s,p.2) x) = yy
        exact congrArg (fun z => (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom z) hxy
      · exact (ConcreteCategory.congr_hom (FC.differential_preserves s 1).choose_spec a).symm


  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map (D : AdamsComparison H M Syn)
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  have page_regrade (D : AdamsComparison H M Syn) {A B : Syn} (f : A ⟶ B) {i j : Tridegree}
      (h : i = j) (z : (D.family.obj A).E₂ i) :
      regradeE2 h (familyPageMap D.family f 2 i z) =
        familyPageMap D.family f 2 j (regradeE2 h z) := by
    subst j
    rfl

  have finite_source_rho (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (i j : ℕ) (hij : i ≤ j) (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
      familyPageMap D.family
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho i j hij) 2
        (s, (t-s)+s, t+normalizedExponent H f)
        (finiteSourceForExtension D X Y f j s t x) =
          finiteSourceForExtension D X Y f i s t x := by
    unfold finiteSourceForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteNuLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s,t,t+(normalizedExponent H f : ℤ)-(0:ℕ)))
      ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc ((D.nuE2 X _ s t 0) x)

  have finite_target_rho (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (y : E2 H (Y.obj D.hopfAndDetector) (s+n) (t+n)) :
      familyPageMap D.family ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho i j hij) 2
        (s+n, (t-s)+(s+n), t+normalizedExponent H f)
        (finiteTargetForExtension D X Y f j n s t hn y) =
          finiteTargetForExtension D X Y f i n s t hn y := by
    unfold finiteTargetForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteTargetLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s+n,t+n,t+n-(n-normalizedExponent H f).toNat))
      ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc (targetNuLabel D Y (s+n) (t+n) _ y)


  have zero_shift_source_exists (D : AdamsComparison H M Syn)
      (BHS : EInftyComparison D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s, t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0, 0) (.nu X))).obj
          D.nu D.hopfAndDetector)).sequence.ssData (s, t, t-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s, t, t-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) e := by
    have zero_shift_quotient_label
        (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
        familyPageMap D.family
          (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector)) ⟶ D.nu.functor.obj (X.obj D.hopfAndDetector) from SyntheticCategory.biShift_zero.hom.app _) q)
          2 (s,t,t-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) =
        (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) := by
      simp only [finiteNuLabel, finiteTargetLabel, targetNuLabel, SyntheticObject.obj]
      have cast_page {A B : Syn} (f : A ⟶ B) {i j : Tridegree}
          (h : i = j) (z : (D.family.obj A).E₂ i) :
          (congrArg (fun k => ((D.family.obj B).E₂ k : Type v)) h).mp
            (familyPageMap D.family f 2 i z) =
          familyPageMap D.family f 2 j
            ((congrArg (fun k => ((D.family.obj A).E₂ k : Type v)) h).mp z) := by
        subst j
        rfl
      have hc := cast_page
        (XModLambdaN.incl ((SyntheticCategory.biShift (0,0)).obj
          (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)
        (show (s,t,t+0-(0:ℕ)) = (s,t,t-(0:ℕ)) by simp) ((D.nuE2 X 0 s t 0) x)
      rw [hc]
      have hn := congrArg (fun f => familyPageMap D.family f 2 (s,t,t-(0:ℕ)))
        (XModLambdaN.incl_naturality (SyntheticCategory.biShift_zero.hom.app
          (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)
      rw [← family_page_comp D, ← family_page_comp D] at hn
      exact (ConcreteCategory.congr_hom hn _).symm
    have zero_shift_quotient_label_inverse
        (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
        familyPageMap D.family
          (XModLambdaN.map (show D.nu.functor.obj (X.obj D.hopfAndDetector) ⟶ (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector)) from SyntheticCategory.biShift_zero.inv.app _) q)
          2 (s,t,t-(0:ℕ))
          (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) =
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) := by
      let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
      let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
      let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
      have hfg : f≫g=𝟙 _ := by
        dsimp only [f,g]
        rw [←D.quotientFunctoriality.map_comp,Iso.hom_inv_id_app,D.quotientFunctoriality.map_id]
      rw [←zero_shift_quotient_label  X q x]
      change familyPageMap D.family g 2 (s,t,t-(0:ℕ))
        (familyPageMap D.family f 2 (s,t,t-(0:ℕ)) _) = _
      rw [←ConcreteCategory.comp_apply]
      rw [family_page_comp D  f g 2 (s,t,t-(0:ℕ)),hfg,family_map_data D,D.family.functor.map_id]
      exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
        (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q)).ssData (s,t,t-(0:ℕ))
        ↑(2-2:ℤ).toNat) _
    have zero_shift_finite_infinity_exists
        (BHS : EInftyComparison D) (X : ClassicalObject) (q : ℕ) (hq : 0<q)
        (x : E2 H (X.obj D.hopfAndDetector) s t)
        (hx : x∈PageRepresentatives.cycles H (X.obj D.hopfAndDetector) q (s,t)) :
        ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,t-(0:ℕ))).eInfty,
          HasInfinityRepresentative _ 2 (s,t,t-(0:ℕ))
            (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) e := by
      let P := BHS.presentation.finiteWindow (X.obj D.hopfAndDetector) q hq (s,t) (t-(0:ℕ)) (by constructor <;> omega)
      let c : PageRepresentatives.cycles H (X.obj D.hopfAndDetector) ((q:ℤ)-t+(t-(0:ℕ))) (s,t) :=
        ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
      let en := P.symm (NestedQuotient.projection _ _ c)
      have hen : HasInfinityRepresentative (D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q)
          2 (s,t,t-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) en := by
        exact (BHS.labels.1 X q hq (s,t) 0 hq c en).mpr (P.apply_symm_apply _)
      let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (D.nu.functor.obj (X.obj D.hopfAndDetector))) q
      refine ⟨(D.family.functor.map g).eInftyMap (s,t,t-(0:ℕ)) en,?_⟩
      have he := family_infinity_representative_map D  g (s,t,t-(0:ℕ)) _ en hen
      dsimp only [g,id] at he
      have hl := zero_shift_quotient_label_inverse  X q x
      have hrepl := congrArg (fun z => HasInfinityRepresentative
        (D.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D.nu D.hopfAndDetector))
        2 (s,t,t-(0:ℕ)) z ((D.family.functor.map g).eInftyMap (s,t,t-(0:ℕ)) en)) hl
      exact hrepl.mp he
    exact zero_shift_finite_infinity_exists BHS X q hq x hx


  have infinity_representative_regrade
      {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i = j)
      (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
      (he : HasInfinityRepresentative A 2 i x e) :
      HasInfinityRepresentative A 2 j (regradeE2 h x)
        ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h)) e) := by
    subst j
    exact he

  have zero_shift_source_raw (D : AdamsComparison H M Syn)
      (BHS : EInftyComparison D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s, t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0, 0) (.nu X))).obj
          D.nu D.hopfAndDetector)).sequence.ssData (s, t, t+0-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s, t, t+0-(0:ℕ))
          (finiteNuLabel D X q 0 s t 0 x) e := by
    have backward_transport {A : SyntheticAdamsSS.{v}} {i j : Tridegree}
        (h : i=j) (x : A.E₂ i)
        (hx : ∃ e : (A.sequence.ssData j).eInfty,
          HasInfinityRepresentative A 2 j
            ((congrArg (fun k => (A.E₂ k : Type v)) h).mp x) e) :
        ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
      subst j
      exact hx
    exact backward_transport (show (s,t,t+0-(0:ℕ))=(s,t,t-(0:ℕ)) by simp)
      (finiteNuLabel D X q 0 s t 0 x) (zero_shift_source_exists D BHS X q hq s t x hx)

  have zero_source_for_extension_exists (D : AdamsComparison H M Syn)
      (BHS : EInftyComparison D) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (hf : normalizedExponent H f=0)
      (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s, t)) :
      ∃ z : ((D.family.obj ((SyntheticObject.quotient q
          (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 (s,(t-s)+s,t+normalizedExponent H f)
          (finiteSourceForExtension D X Y f q s t x) z := by
    have source_exists (e : ℕ) (he : e=0) :
        ∃ z : ((D.family.obj ((SyntheticObject.quotient q
            (.shift (0,(e:ℤ)) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData
            (s,(t-s)+s,t+e)).eInfty,
          HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e)
            (regradeE2 (by simp) (finiteNuLabel D X q e s t 0 x)) z := by
      subst e
      obtain ⟨z,hz⟩ := zero_shift_source_raw D BHS X q hq s t x hx
      exact ⟨_,infinity_representative_regrade (by simp) _ z hz⟩
    exact source_exists _ hf


  have finite_target_infinity_exists (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (q : ℕ) (hq : 0 < q) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (hk : n - normalizedExponent H f < q)
      (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n))
      (hy : y ∈ cycles H (Y.obj D.hopfAndDetector)
        ((q : ℤ) - n + normalizedExponent H f) (s + n, t + n)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
          D.nu D.hopfAndDetector)).sequence.ssData
            (s + n, (t - s) + (s + n), t + normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 _ (finiteTargetForExtension D X Y f q n s t hn y) e := by
    let k := (n - normalizedExponent H f).toNat
    have hkZ : (k : ℤ) = n - normalizedExponent H f := Int.toNat_of_nonneg (by omega)
    have hkq : k < q := by omega
    let p : ℤ × ℤ := (s + n, t + n)
    let P := synthetic.eInfty.presentation.finiteWindow
      (Y.obj D.hopfAndDetector) q hq p (p.2 - k) (by constructor <;> omega)
    let c : cycles H (Y.obj D.hopfAndDetector) ((q : ℤ) - p.2 + (p.2 - k)) p :=
      ⟨y, by
        have heq : (q : ℤ) - p.2 + (p.2 - k) = (q : ℤ) - n + normalizedExponent H f := by omega
        simpa only [heq] using hy⟩
    let e := P.symm (NestedQuotient.projection _ _ c)
    have he : HasInfinityRepresentative (D.family.nuQuotient D.nu (Y.obj D.hopfAndDetector) q)
        2 (p.1, p.2, p.2 - k) (finiteTargetLabel D Y q p.1 p.2 k y) e :=
      (synthetic.eInfty.labels.1 Y q hq p k hkq c e).mpr (P.apply_symm_apply _)
    have hi : (p.1, p.2, p.2 - k) =
        (s + n, (t - s) + (s + n), t + normalizedExponent H f) := by
      dsimp only [p]
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd] <;> omega
    refine ⟨(eqToHom (congrArg (fun p =>
      ((D.family.nuQuotient D.nu (Y.obj D.hopfAndDetector) q).sequence.ssData p).eInfty) hi)) e, ?_⟩
    exact infinity_representative_regrade hi _ _ he


  have rho_injective (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (Y : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : ℤ × ℤ) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i) :
      Function.Injective (((D.family.functor.map
        ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho i j hij)).eInftyMap
          (p.1,p.2,w)).hom) := by
    intro a b hab
    apply (synthetic.eInfty.presentation.finiteWindow (Y.obj D.hopfAndDetector) j (by omega)
      p w (by constructor <;> omega)).injective
    have hcycles : cycles H (Y.obj D.hopfAndDetector) ((j:ℤ)-p.2+w) p ≤
        cycles H (Y.obj D.hopfAndDetector) ((i:ℤ)-p.2+w) p :=
      cycles_antitone H (Y.obj D.hopfAndDetector) p (by omega)
    apply NestedQuotient.cycle_map_injective hcycles
    change quotientMap H (Y.obj D.hopfAndDetector) (by omega) (le_refl _) p _ =
      quotientMap H (Y.obj D.hopfAndDetector) (by omega) (le_refl _) p _
    rw [← synthetic.eInfty.maps.rho_finite (Y.obj D.hopfAndDetector) i j hi hij p w hw a,
      ← synthetic.eInfty.maps.rho_finite (Y.obj D.hopfAndDetector) i j hi hij p w hw b, hab]

  have he : normalizedExponent H f = 0 := by omega
  have hq : 0 < rLater-1 := by omega
  have hi : 0 < rEarlier-1 := by omega
  have hij : rEarlier-1 ≤ rLater-1 := by omega
  obtain ⟨xx,hxx⟩ := zero_source_for_extension_exists D synthetic.eInfty X Y f he
    (rLater-1) hq s t x (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hx.2)
  obtain ⟨yy,hyy⟩ := finite_target_infinity_exists D synthetic X Y f
    (rLater-1) hq 0 s t hn (by omega) y (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hy.2)
  let a := (D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
    (rEarlier-1) (rLater-1) hij
  let b := (D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho
    (rEarlier-1) (rLater-1) hij
  have hsource : (D.family.functor.map a).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) xx = W.source := by
    have hh := family_infinity_representative_map D a _ _ xx hxx
    rw [finite_source_rho D] at hh
    exact hh.unique W.source_rep
  have htarget : (D.family.functor.map b).eInftyMap
      (s+0,(t-s)+(s+0),t+normalizedExponent H f) yy = W.target := by
    have hh := family_infinity_representative_map D b _ _ yy hyy
    rw [finite_target_rho D] at hh
    exact hh.unique W.target_rep
  let yy0 : ((D.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        D.nu D.hopfAndDetector)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty := by
    simpa only [add_zero] using yy
  let wy0 : ((D.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
        D.nu D.hopfAndDetector)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty := by
    simpa only [add_zero] using W.target
  have hearly : (D.family.functor.map (finiteExtensionMap D X Y f (rEarlier-1))).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) W.source = wy0 := by
    have hcast : (by simpa only [add_zero] using wy0 :
        ((D.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
          D.nu D.hopfAndDetector)).sequence.ssData
            (s+0,(t-s)+(s+0),t+normalizedExponent H f)).eInfty) = W.target := by
      change cast _ (cast _ W.target) = W.target
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    have hh := extension_zero_iff D
      (.quotient (rEarlier-1) (extensionSourceObject D X Y f)) (.quotient (rEarlier-1) (.nu Y))
      (finiteExtensionMap D X Y f (rEarlier-1)) (t-s,t+normalizedExponent H f) s W.source wy0
    rw [hcast] at hh
    exact hh.mp W.equation
  have htarget0 : (D.family.functor.map b).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) yy0 = wy0 := by
    have cast_infty {A B : Syn} (g : A ⟶ B) {i j : Tridegree}
        (h : i=j) (z : ((D.family.obj A).sequence.ssData i).eInfty) :
        (congrArg (fun k => (((D.family.obj B).sequence.ssData k).eInfty : Type v)) h).mp
          ((D.family.functor.map g).eInftyMap i z) =
        (D.family.functor.map g).eInftyMap j
          ((congrArg (fun k => (((D.family.obj A).sequence.ssData k).eInfty : Type v)) h).mp z) := by
      subst j
      rfl
    have hh := cast_infty b
      (show (s+0,(t-s)+(s+0),t+normalizedExponent H f)=
        (s,(t-s)+s,t+normalizedExponent H f) by simp) yy
    rw [htarget] at hh
    exact hh.symm
  have hsquare : a ≫ finiteExtensionMap D X Y f (rEarlier-1) =
      finiteExtensionMap D X Y f (rLater-1) ≫ b :=
    (D.comparisonCompatible.quotient_naturality (D.normalizedMap X Y f).map).rho_naturality hij
  have infinity_comp {A B C : Syn} (g : A ⟶ B) (h : B ⟶ C) (i : Tridegree) :
      (D.family.functor.map (g ≫ h)).eInftyMap i =
        (D.family.functor.map g).eInftyMap i ≫ (D.family.functor.map h).eInftyMap i := by
    rw [Functor.map_comp]
    exact SpectralSequenceMorphism.eInftyMap_comp _ _ _
  have hsquare' := congrArg (fun g => (D.family.functor.map g).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f)) hsquare
  rw [infinity_comp, infinity_comp] at hsquare'
  have hlater : (D.family.functor.map (finiteExtensionMap D X Y f (rLater-1))).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) xx = yy0 := by
    apply rho_injective D synthetic Y (rEarlier-1) (rLater-1) hi hij
      (s,(t-s)+s) (t+normalizedExponent H f) (by dsimp only [Prod.snd]; constructor <;> omega)
    have hh := ConcreteCategory.congr_hom hsquare' xx
    change (D.family.functor.map (finiteExtensionMap D X Y f (rEarlier-1))).eInftyMap _
      ((D.family.functor.map a).eInftyMap _ xx) =
      (D.family.functor.map b).eInftyMap _
        ((D.family.functor.map (finiteExtensionMap D X Y f (rLater-1))).eInftyMap _ xx) at hh
    rw [hsource,hearly] at hh
    exact hh.symm.trans htarget0.symm
  refine ⟨{
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := hx
    target_cycle := hy
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := ?_}⟩
  have hh := (extension_zero_iff D
    (.quotient (rLater-1) (extensionSourceObject D X Y f)) (.quotient (rLater-1) (.nu Y))
    (finiteExtensionMap D X Y f (rLater-1)) (t-s,t+normalizedExponent H f) s xx yy0).mpr hlater
  have hcast : (by simpa only [add_zero] using yy0 :
      ((D.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        D.nu D.hopfAndDetector)).sequence.ssData
          (s+0,(t-s)+(s+0),t+normalizedExponent H f)).eInfty) = yy := by
    change cast _ (cast _ yy) = yy
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  rw [hcast] at hh
  exact hh


section ShiftedRepresentatives

open CategoryTheory.Functor CategoryTheory.Pretriangulated

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_shift_exists (coh : BiShiftCoherence Syn)
    (a : ℤ × ℤ) (q : ℕ) (X : Syn)
    [cs : (SyntheticCategory.biShift (Syn := Syn) a).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn := Syn) a).IsTriangulated] :
    ∃ e : XModLambdaN ((SyntheticCategory.biShift a).obj X) q ≅
      (SyntheticCategory.biShift a).obj (XModLambdaN X q),
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj X) q ≫ e.hom =
        (SyntheticCategory.biShift a).map (XModLambdaN.incl X q) := by
  let oneComm (a : ℤ × ℤ) :
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree 1) ≅
        SyntheticCategory.biShift (lambdaDegree 1) ⋙ SyntheticCategory.biShift a :=
    biShiftAddIso a (0,-1) (a+(0,-1)) rfl ≪≫
      (biShiftAddIso (0,-1) a (a+(0,-1)) (add_comm _ _)).symm

  let powerComm (a : ℤ × ℤ) : (q : ℕ) →
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a := fun q =>
    Nat.rec (motive := fun q =>
      SyntheticCategory.biShift (Syn := Syn) a ⋙ SyntheticCategory.biShift (lambdaDegree q) ≅
        SyntheticCategory.biShift (lambdaDegree q) ⋙ SyntheticCategory.biShift a)
      (isoWhiskerLeft _ SyntheticCategory.biShift_zero ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
        (isoWhiskerRight SyntheticCategory.biShift_zero _).symm)
      (fun q ih =>
        isoWhiskerLeft _ (lambdaShiftAddIso 1 q (q+1) (by omega)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (oneComm a) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ih ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (lambdaShiftAddIso 1 q (q+1) (by omega)) _) q

  have powerComm_square (coh : BiShiftCoherence Syn) (a : ℤ × ℤ)
      (q : ℕ) (X : Syn) :
      lambdaPow q ((SyntheticCategory.biShift a).obj X) =
        (powerComm a q).hom.app X ≫ (SyntheticCategory.biShift a).map (lambdaPow q X) := by
    induction q generalizing X with
    | zero =>
      simp [powerComm, lambdaPow, ← Functor.map_comp]
      exact (Category.comp_id _).symm
    | succ q ih =>
      have h1 : (oneComm a).hom.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) =
          SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) := by
        simpa [oneComm, Category.assoc] using (coh.lambda_comm a X).symm
      apply (cancel_epi ((lambdaShiftAddIso 1 q (q+1) (by omega)).hom.app
        ((SyntheticCategory.biShift a).obj X))).mp
      rw [lambdaPow_succ_comparison]
      simp only [powerComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
      rw [Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp, lambdaPow_succ_comparison, Functor.map_comp]
      have hn := (powerComm a q).hom.naturality (SyntheticCategory.lam.app X)
      have hn' := congrArg (fun h => h ≫ (SyntheticCategory.biShift a).map (lambdaPow q X)) hn
      simp only [Functor.comp_map, Category.assoc] at hn'
      dsimp only [KIP126.Synthetic.Context.lambdaDegree, Functor.id_obj] at hn' ⊢
      erw [← hn']
      rw [← Category.assoc, ← Functor.map_comp, h1, ih]

  let F := SyntheticCategory.biShift (Syn := Syn) a
  let T := Triangle.mk (lambdaPow q X) (XModLambdaN.incl X q) (XModLambdaN.proj X q)
  let T' := Triangle.mk (lambdaPow q (F.obj X))
    (XModLambdaN.incl (F.obj X) q) (XModLambdaN.proj (F.obj X) q)
  have hT : T ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  let e := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) ((powerComm a q).app X) (Iso.refl _) (by
      change lambdaPow q (F.obj X) ≫ 𝟙 _ =
        (powerComm a q).hom.app X ≫ F.map (lambdaPow q X)
      simpa only [Category.comp_id] using powerComm_square coh a q X)
  refine ⟨Triangle.π₃.mapIso e, ?_⟩
  have h := e.hom.comm₂
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ F.map (XModLambdaN.incl X q) at h
  change XModLambdaN.incl (F.obj X) q ≫ e.hom.hom₃ =
    F.map (XModLambdaN.incl X q)
  simpa only [e, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom, Category.id_comp] using h


set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shifted_finite_source_exists (D : AdamsComparison H M Syn)
    (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (a s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t)
    (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s,t)) :
    ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ)) (finiteNuLabel D X q a s t 0 x) e := by
  have weightPageShift_exists {K : Syn} {unit : S_0_0 ⟶ K}
      {F : SyntheticAdamsFamily Syn} (P : TowerPresentation unit F)
      (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) (n : WithTop ℕ) :
      Nonempty (((F.obj ((SyntheticCategory.biShift (0,k)).obj A)).sequence.ssData
        (p.1,p.2,w+k)).page n ≅ ((F.obj A).sequence.ssData (p.1,p.2,w)).page n) := by
    classical
    let X := (SyntheticCategory.biShift (0, k)).obj A
    let U := (SyntheticCategory.biShift (0, -(w + k))).obj X
    let V := (SyntheticCategory.biShift (0, -w)).obj A
    let eF : ((F.obj X).sequence.ssData (p.1, p.2, w + k)).V ≅
        ((weightTower unit X (w + k)).ssData p).V :=
      { hom := (P.forward X (w + k)).φ p
        inv := (P.inverse X (w + k)).φ p
        hom_inv_id := P.left_inv X (w + k) p
        inv_hom_id := P.right_inv X (w + k) p }
    let eI : ((weightTower unit A w).ssData p).V ≅
        ((F.obj A).sequence.ssData (p.1, p.2, w)).V :=
      { hom := (P.inverse A w).φ p
        inv := (P.forward A w).φ p
        hom_inv_id := P.right_inv A w p
        inv_hom_id := P.left_inv A w p }
    let eT := LinearEquiv.ofBijective
      (KIP126.Classical.Adams.adamsCycleInduced unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
      (KIP126.Classical.Adams.adamsCycleInduced_bijective unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
    let e := (eF.toLinearEquiv.trans eT).trans eI.toLinearEquiv
    have htZ (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).Z n) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).Z n) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit V p.1 p.2 n)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit U p.1 p.2 n))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 n x
    have htB (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).B n) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).B n) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit V p.1 p.2 n)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit U p.1 p.2 n))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 n x
    have hZ x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_Z p n) ((P.forward A w).preserves_Z p n) (eT (eF.hom x))).trans
      ((htZ (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_Z p n) ((P.inverse X (w + k)).preserves_Z p n) x))
    have hB x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_B p n) ((P.forward A w).preserves_B p n) (eT (eF.hom x))).trans
      ((htB (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_B p n) ((P.inverse X (w + k)).preserves_B p n) x))
    obtain ⟨q, hq⟩ := subobject_quotient_iso_of_linearEquiv
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B n)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).Z n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).Z n)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B_le_Z n)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B_le_Z n) e hB hZ
    exact ⟨q⟩

  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_page_id (D : AdamsComparison H M Syn) (X : Syn) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family (𝟙 X) r i = 𝟙 _ := by
    rw [family_map_data, CategoryTheory.Functor.map_id]
    exact SSDataMorphism.pageMap_id _ _ _

  let familyPageIso (D : AdamsComparison H M Syn) {X Y : Syn} (e : X ≅ Y)
      (r : ℤ) (i : Tridegree) : (D.family.obj X).Page r i ≅ (D.family.obj Y).Page r i := {
    hom := familyPageMap D.family e.hom r i
    inv := familyPageMap D.family e.inv r i
    hom_inv_id := by rw [family_page_comp, e.hom_inv_id, family_page_id]
    inv_hom_id := by rw [family_page_comp, e.inv_hom_id, family_page_id] }

  have shiftedFinitePageVanishing (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (a r s t w : ℤ)
      (e : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector))) q ≅
        (SyntheticCategory.biShift (0,a)).obj (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (hr : 2 ≤ r) (hw : t < w-a ∨ (q:ℤ) ≤ t-(w-a)) :
      Subsingleton ((D.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page r (s,t,w)) := by
    haveI := synthetic.finite_quotient_page_vanishing X q hq r s t (w-a) hr hw
    obtain ⟨ew⟩ := weightPageShift_exists D.towerPresentation
      (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q) a (s,t) (w-a) (↑(r-2).toNat)
    have ew' : (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))).Page r (s,t,w) ≅
        (D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).Page r (s,t,w-a) := by
      simpa only [sub_add_cancel, SyntheticAdamsSS.Page, SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient] using ew
    exact ((familyPageIso D e r (s,t,w)) ≪≫ ew').toLinearEquiv.injective.subsingleton

  have syntheticRep_map (D : AdamsComparison H M Syn) {X Y : Syn}
      (f : X ⟶ Y) (r : ℤ) (i : Tridegree)
      (x : (D.family.obj X).E₂ i) (xr : (D.family.obj X).Page r i)
      (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj X) r i x xr) :
      KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj Y) r i
        (familyPageMap D.family f 2 i x) (familyPageMap D.family f r i xr) := by
    obtain ⟨hr,z,hz,he⟩ := hx
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z (↑(r-2).toNat)) (((D.family.functor.obj X).ssData i).Z 0) _ ≫
      ((D.family.functor.obj X).ssData i).pageπ 0) z=x at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i (↑(r-2).toNat) z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤↑(r-2).toNat from bot_le)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [← F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · rw [family_map_data D]
      exact (congrArg (fun a => a z) (F.pageπ_pageMap i (↑(r-2).toNat))).symm.trans (by
        change F.pageMap i (↑(r-2).toNat) (((D.family.obj X).sequence.ssData i).pageπ (↑(r-2).toNat) z)=_
        rw [he])

  have syntheticRep_infty (A : SyntheticAdamsSS.{v})
      (r : ℤ) (i : Tridegree) (x : A.E₂ i) (xr : A.Page r i)
      (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r i x xr)
      (hout : ∀ n : ℤ, r ≤ n → A.sequence.d n i = 0) :
      ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
    obtain ⟨hr,z,hz,he⟩ := hx
    have hZ := cycles_top_eq_of_d_eq_zero A.sequence r (by rw [A.firstPage]; exact hr) i hout
    rw [A.firstPage] at hZ
    let zInf := (Subobject.ofLE _ _ hZ.ge) z
    refine ⟨_,by norm_num,zInf,?_,rfl⟩
    change (Subobject.ofLE _ _ _ ≫ (A.sequence.ssData i).pageπ 0)
      ((Subobject.ofLE _ _ hZ.ge) z)=x
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz

  have page_has_initial_rep
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
      {r : ℤ} {p : ℤ × ℤ} (hr : 2 ≤ r) (a : E.Page r p) :
      ∃ x : E.Page 2 p, KIP126.SpectralSequence.RepresentsOnPage E r p x a := by
    haveI : Epi ((E.ssData p).pageπ ↑(r-E.r₀).toNat) := by
      change Epi (cokernel.π _)
      infer_instance
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ ↑(r-E.r₀).toNat)).mp inferInstance a
    exact ⟨_,hr,z,rfl,hz⟩

  have shiftedFiniteSource_exists (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (a s t : ℤ)
      (eqs : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector))) q ≅
        (SyntheticCategory.biShift (0,a)).obj (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s,t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,a) (.nu X))).obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,t+a-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s,t,t+a-(0:ℕ)) (finiteNuLabel D X q a s t 0 x) e := by
    let E := adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)
    have hr : 2 ≤ (q+1:ℕ) := by omega
    have hx' : IsCycle H (X.obj D.hopfAndDetector) ((q+1:ℕ)-1:ℤ) (s,t) x := by
      refine ⟨by omega,?_⟩
      simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hx
    obtain ⟨xr,hxr⟩ := (isCycle_iff_represents H (X.obj D.hopfAndDetector) (q+1:ℕ) (by omega) (s,t) x).mp hx'
    have hd : (s,t) + E.diffDeg (q+1:ℕ) = (s+(q+1:ℕ),t+(q+1:ℕ)-1) := by
      change (s+(q+1:ℕ),t+((q+1:ℕ)-1)) = _
      congr 1; omega
    let yr := (E.d (q+1:ℕ) (s,t) ≫ eqToHom (congrArg (E.Page (q+1:ℕ)) hd)) xr
    obtain ⟨y,hy⟩ := page_has_initial_rep (by omega : (2:ℤ)≤(q+1:ℕ)) yr
    have hc : KIP126.SpectralSequence.HasDifferential E (q+1:ℕ)
        (s,t) (s+(q+1:ℕ),t+(q+1:ℕ)-1) x y := ⟨hd,xr,yr,hxr,hy,rfl⟩
    have hs := (synthetic.differentials X a s t (q+1) 0 hr x y).mp hc
    obtain ⟨_,xs,ys,hxs,hys,hds⟩ := hs
    have hf := syntheticRep_map D (XModLambdaN.incl _ q) (q+1:ℕ)
      (s,t,t+a-(0:ℕ)) (D.nuE2 X a s t 0 x) xs hxs
    apply syntheticRep_infty _ (q+1:ℕ) (s,t,t+a-(0:ℕ)) _ _ hf
    intro n hn
    have hi : (s,t,t+a-(0:ℕ)) +
        (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
          (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).diffDeg n = (s+n,t+n-1,t+a) := by
      rw [D.family.differentialDegree]
      simp only [syntheticAdamsDifferentialDegree, Prod.mk_add_mk, Nat.cast_zero, sub_zero, add_zero]
      ext <;> dsimp; omega
    haveI := shiftedFinitePageVanishing D synthetic X q hq a n (s+n) (t+n-1) (t+a)
      eqs (by omega) (Or.inr (by omega))
    have hp : Subsingleton ((D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page n
          ((s,t,t+a-(0:ℕ)) + (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
            (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).diffDeg n)) := by
      rw [hi]
      simpa only [KIP126.SpectralSequence.Page, D.family.firstPage, SyntheticAdamsSS.Page,
        SyntheticAdamsFamily.obj] using (inferInstance : Subsingleton
          ((D.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
            (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).Page n (s+n,t+n-1,t+a)))
    letI := hp
    ext z
    exact @Subsingleton.elim _ hp _ _

  letI := D.shiftCommShift (0,a)
  letI := D.shiftExact (0,a)
  obtain ⟨eqs,heqs⟩ := quotient_shift_exists D.shiftCoherence (0,a) q (D.nu.functor.obj (X.obj D.hopfAndDetector))
  exact shiftedFiniteSource_exists D synthetic X q hq a s t eqs x hx



set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_representatives_lift (D : AdamsComparison H M Syn)
    (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
    (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s+n) (t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hnUpper : n ≤ (rEarlier:ℤ)-2+normalizedExponent H f)
    (hx : IsCycle H (X.obj D.hopfAndDetector) ((rLater:ℤ)-1) (s,t) x)
    (hy : IsCycle H (Y.obj D.hopfAndDetector)
      ((rLater:ℤ)-1-n+normalizedExponent H f) (s+n,t+n) y)
    (W : FiniteExtensionWitness D X Y f rEarlier n s t x y) :
    ∃ (xx : ((D.family.obj ((SyntheticObject.quotient (rLater-1)
        (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector)).sequence.ssData
        (s,(t-s)+s,t+normalizedExponent H f)).eInfty)
      (yy : ((D.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        D.nu D.hopfAndDetector)).sequence.ssData
        (s+n,(t-s)+(s+n),t+normalizedExponent H f)).eInfty),
      HasInfinityRepresentative _ 2 _ (finiteSourceForExtension D X Y f (rLater-1) s t x) xx ∧
      HasInfinityRepresentative _ 2 _ (finiteTargetForExtension D X Y f (rLater-1) n s t hn y) yy ∧
      (D.family.functor.map ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
        (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
        (s,(t-s)+s,t+normalizedExponent H f) xx = W.source ∧
      (D.family.functor.map ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho
        (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
        (s+n,(t-s)+(s+n),t+normalizedExponent H f) yy = W.target := by
  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map (D : AdamsComparison H M Syn)
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  have page_regrade (D : AdamsComparison H M Syn) {A B : Syn} (f : A ⟶ B) {i j : Tridegree}
      (h : i = j) (z : (D.family.obj A).E₂ i) :
      regradeE2 h (familyPageMap D.family f 2 i z) =
        familyPageMap D.family f 2 j (regradeE2 h z) := by
    subst j
    rfl

  have finite_source_rho (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (i j : ℕ) (hij : i ≤ j) (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
      familyPageMap D.family
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho i j hij) 2
        (s, (t-s)+s, t+normalizedExponent H f)
        (finiteSourceForExtension D X Y f j s t x) =
          finiteSourceForExtension D X Y f i s t x := by
    unfold finiteSourceForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteNuLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s,t,t+(normalizedExponent H f : ℤ)-(0:ℕ)))
      ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc ((D.nuE2 X _ s t 0) x)

  have finite_target_rho (D : AdamsComparison H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (y : E2 H (Y.obj D.hopfAndDetector) (s+n) (t+n)) :
      familyPageMap D.family ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho i j hij) 2
        (s+n, (t-s)+(s+n), t+normalizedExponent H f)
        (finiteTargetForExtension D X Y f j n s t hn y) =
          finiteTargetForExtension D X Y f i n s t hn y := by
    unfold finiteTargetForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteTargetLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s+n,t+n,t+n-(n-normalizedExponent H f).toNat))
      ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc (targetNuLabel D Y (s+n) (t+n) _ y)


  have infinity_representative_regrade
      {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i = j)
      (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
      (he : HasInfinityRepresentative A 2 i x e) :
      HasInfinityRepresentative A 2 j (regradeE2 h x)
        ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h)) e) := by
    subst j
    exact he

  have finite_target_infinity_exists (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
      (q : ℕ) (hq : 0 < q) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (hk : n - normalizedExponent H f < q)
      (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n))
      (hy : y ∈ cycles H (Y.obj D.hopfAndDetector)
        ((q : ℤ) - n + normalizedExponent H f) (s + n, t + n)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
          D.nu D.hopfAndDetector)).sequence.ssData
            (s + n, (t - s) + (s + n), t + normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 _ (finiteTargetForExtension D X Y f q n s t hn y) e := by
    let k := (n - normalizedExponent H f).toNat
    have hkZ : (k : ℤ) = n - normalizedExponent H f := Int.toNat_of_nonneg (by omega)
    have hkq : k < q := by omega
    let p : ℤ × ℤ := (s + n, t + n)
    let P := synthetic.eInfty.presentation.finiteWindow
      (Y.obj D.hopfAndDetector) q hq p (p.2 - k) (by constructor <;> omega)
    let c : cycles H (Y.obj D.hopfAndDetector) ((q : ℤ) - p.2 + (p.2 - k)) p :=
      ⟨y, by
        have heq : (q : ℤ) - p.2 + (p.2 - k) = (q : ℤ) - n + normalizedExponent H f := by omega
        simpa only [heq] using hy⟩
    let e := P.symm (NestedQuotient.projection _ _ c)
    have he : HasInfinityRepresentative (D.family.nuQuotient D.nu (Y.obj D.hopfAndDetector) q)
        2 (p.1, p.2, p.2 - k) (finiteTargetLabel D Y q p.1 p.2 k y) e :=
      (synthetic.eInfty.labels.1 Y q hq p k hkq c e).mpr (P.apply_symm_apply _)
    have hi : (p.1, p.2, p.2 - k) =
        (s + n, (t - s) + (s + n), t + normalizedExponent H f) := by
      dsimp only [p]
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd] <;> omega
    refine ⟨(eqToHom (congrArg (fun p =>
      ((D.family.nuQuotient D.nu (Y.obj D.hopfAndDetector) q).sequence.ssData p).eInfty) hi)) e, ?_⟩
    exact infinity_representative_regrade hi _ _ he



  have hq : 0 < rLater-1 := by omega
  have hij : rEarlier-1 ≤ rLater-1 := Nat.sub_le_sub_right hle 1
  obtain ⟨xs,hxs⟩ := shifted_finite_source_exists D synthetic X (rLater-1) hq
    (normalizedExponent H f) s t x (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hx.2)
  have hsgrade : (s,t,t+(normalizedExponent H f:ℤ)-(0:ℕ)) =
      (s,(t-s)+s,t+normalizedExponent H f) := by simp
  let xx := (eqToHom (congrArg (fun p => ((D.family.obj ((SyntheticObject.quotient (rLater-1)
    (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector)).sequence.ssData p).eInfty) hsgrade)) xs
  have hxx : HasInfinityRepresentative _ 2 _
      (finiteSourceForExtension D X Y f (rLater-1) s t x) xx :=
    infinity_representative_regrade hsgrade _ xs hxs
  obtain ⟨yy,hyy⟩ := finite_target_infinity_exists D synthetic X Y f
    (rLater-1) hq n s t hn (by omega) y (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hy.2)
  refine ⟨xx,yy,hxx,hyy,?_,?_⟩
  · have hh := family_infinity_representative_map D
      ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
        (rEarlier-1) (rLater-1) hij) _ _ xx hxx
    rw [finite_source_rho D] at hh
    exact hh.unique W.source_rep
  · have hh := family_infinity_representative_map D
      ((D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho
        (rEarlier-1) (rLater-1) hij) _ _ yy hyy
    rw [finite_target_rho D] at hh
    exact hh.unique W.target_rep


end ShiftedRepresentatives

/-- A finite correction argument with the actual residual kept throughout. -/
private theorem finite_filtration_correction
    {A A' B : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
    (ρ : A' →+ A) (g : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup A')
    (T : AddSubgroup B) (hL : Antitone L)
    (s : ℤ) (N : ℕ)
    (hstep : ∀ k : ℤ, s ≤ k → k < s + N → ∀ δ : A, δ ∈ E k →
      (∃ ε : A', ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)) ∨ g δ ∈ T)
    (hend : ∀ δ : A, δ ∈ E (s + N) → g δ ∈ T)
    (α₀ : A) (α : A') (hδ : α₀ - ρ α ∈ E s) :
    ∃ α' : A', α' - α ∈ L s ∧ g (α₀ - ρ α') ∈ T := by
  induction N generalizing s α with
  | zero =>
    refine ⟨α, ?_, hend _ ?_⟩
    · simpa only [sub_self] using (L s).zero_mem
    · simpa only [Nat.cast_zero, add_zero] using hδ
  | succ N ih =>
    rcases hstep s le_rfl (by omega) _ hδ with hcorrect | hstop
    · obtain ⟨ε, hε, hδε⟩ := hcorrect
      have hδ' : α₀ - ρ (α + ε) ∈ E (s + 1) := by
        simpa only [map_add, sub_add_eq_sub_sub] using hδε
      obtain ⟨α', hα', hfinal⟩ := ih (s + 1)
        (fun k hk hkn δ hδ => hstep k (by omega) (by omega) δ hδ)
        (fun δ hδ => hend δ (by simpa only [Nat.cast_succ, add_assoc,
          add_comm, add_left_comm] using hδ)) (α + ε) hδ'
      refine ⟨α', ?_, hfinal⟩
      have hmem := (L s).add_mem (hL (by omega) hα') hε
      convert hmem using 1
      abel
    · exact ⟨α, by simpa only [sub_self] using (L s).zero_mem, hstop⟩


/-- Injectivity of successive graded maps reflects membership through a finite
filtration interval; it does not require injectivity of the ambient map. -/
private theorem finite_filtration_reflection
    {B' B : Type*} [AddCommGroup B'] [AddCommGroup B]
    (ρ : B' →+ B) (L : ℤ → AddSubgroup B') (E : ℤ → AddSubgroup B)
    (hE : Antitone E) (s : ℤ) (N : ℕ)
    (hgraded : ∀ k : ℤ, s ≤ k → k < s + N → ∀ b : B', b ∈ L k →
      ρ b ∈ E (k + 1) → b ∈ L (k + 1))
    (b : B') (hb : b ∈ L s) (hρb : ρ b ∈ E (s + N)) :
    b ∈ L (s + N) := by
  have h : ∀ k : ℕ, k ≤ N → b ∈ L (s + k) := by
    intro k hk
    induction k with
    | zero => simpa only [Nat.cast_zero, add_zero] using hb
    | succ k ih =>
      have hkN : k ≤ N := by omega
      have hnext := hgraded (s + k) (by omega) (by omega) b (ih hkN)
        (hE (by omega) hρb)
      simpa only [Nat.cast_succ, add_assoc] using hnext
  exact h N le_rfl

/-- Failure to lie in the final layer is witnessed by a nonzero leading grade
in the finite interval. -/
private theorem first_nonzero_filtration_grade
    {B : Type*} [AddCommGroup B] (E : ℤ → AddSubgroup B)
    (s : ℤ) (N : ℕ) (b : B) (hb : b ∈ E s) (hnot : b ∉ E (s + N)) :
    ∃ k : ℤ, s ≤ k ∧ k < s + N ∧ b ∈ E k ∧ b ∉ E (k + 1) := by
  induction N generalizing s with
  | zero => exact (hnot (by simpa only [Nat.cast_zero, add_zero] using hb)).elim
  | succ N ih =>
    by_cases hnext : b ∈ E (s + 1)
    · have hnot' : b ∉ E ((s + 1) + N) := by
        simpa only [Nat.cast_succ, add_assoc, add_comm, add_left_comm] using hnot
      obtain ⟨k, hk, hkN, hb, hnot⟩ := ih (s + 1) hnext hnot'
      exact ⟨k, by omega, by omega, hb, hnot⟩
    · exact ⟨s, le_rfl, by omega, hb, hnext⟩


set_option maxHeartbeats 3200000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Finite stretching with the layer-preserving obstruction exclusion from
`FiniteExtensionNonliftableCrossing`. The exclusion concerns actual nonzero
extensions in the same earlier quotient, including inessential extensions;
it does not divide by λ or assume a smaller-quotient crossing comparison.
This is a stronger sufficient-condition formulation of the finite correction
argument around MainPaper `prop:dec738d3`, not the printed corollary verbatim.
It asserts neither an infinite lift nor compatibility of arbitrarily chosen
lifts; the later-page cycle conditions remain explicit. -/
theorem finitePageExtensionStretching (synthetic : SyntheticComparisonTheorems D)
    (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector) :
    KIP126.AdamsSynthetic.ExtensionLaws.FinitePageExtensionStretchingLaw D X Y f := by
  intro rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross
  by_cases hsame : rEarlier = rLater
  · subst rLater
    exact hW
  by_cases hnZero : n = 0
  · subst n
    obtain ⟨W⟩ := hW
    exact finite_extension_zero_stretches D synthetic X Y f rEarlier rLater s t
      x y hr hle hn hx hy W
  have hLater : rEarlier < rLater := by omega
  have hnPositive : 0 < n := by omega
  by_cases hzero : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    have module_map_zero {A B : ModuleCat.{v} ℤ} (g : A ⟶ B) : g (0 : A) = 0 :=
      g.hom.map_zero
    have cast_module_zero {A B : ModuleCat.{v} ℤ}
        (h : (A : Type v) = (B : Type v)) (he : A = B) : h.mp (0 : A) = 0 := by
      subst B
      rfl
    have cast_nu_zero (s' t' : ℤ) (k : ℕ)
        (h : ((D.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (D.nu.functor.obj (Y.obj D.hopfAndDetector)))).E₂ (s',t',t'+0-k) : Type v) =
          ((D.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (D.nu.functor.obj (Y.obj D.hopfAndDetector)))).Page 2 (s',t',t'-k) : Type v)) :
        h.mp 0 = 0 := by
      apply cast_module_zero h
      simp only [SyntheticAdamsSS.E₂, add_zero]
    refine ⟨{
      page_ge_two := by omega
      length_lower := hn
      length_upper := by omega
      source_cycle := hx
      target_cycle := hy
      source := 0
      target := 0
      source_rep := ?_
      target_rep := ?_
      equation := ?_ }⟩
    · have hlabel : finiteSourceForExtension D X Y f (rLater - 1) s t 0 = 0 := by
        set_option backward.isDefEq.respectTransparency false in
        simp only [finiteSourceForExtension, finiteNuLabel, regradeE2,
          map_zero, module_map_zero]
      rw [hlabel]
      exact HasInfinityRepresentative.zero _ 2 (by omega) _
    · have hlabel : finiteTargetForExtension D X Y f (rLater - 1) n s t hn 0 = 0 := by
        set_option backward.isDefEq.respectTransparency false in
        simp only [finiteTargetForExtension, finiteTargetLabel, targetNuLabel,
          regradeE2, map_zero, cast_nu_zero, module_map_zero]
      rw [hlabel]
      exact HasInfinityRepresentative.zero _ 2 (by omega) _
    · refine ⟨by omega, ⟨⟨0, ?_⟩⟩⟩
      set_option backward.isDefEq.respectTransparency false in
      simp [FilteredComplex.Solutions.equation, elementMap,
        module_map_zero]
  classical
  let unit := nuCoefficientUnit H.unit D.nu
  have extension_equation_iff_representatives
      {F : SyntheticAdamsFamily Syn} {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence unit F A) (cb : TowerConvergence unit F B)
      (p : ℤ × ℤ) (s n : ℤ)
      (x : ((F.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (y : ((F.obj B).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) :
      ExtensionEquation g ca cb p s n x y ↔
        0 ≤ n ∧ ∃ (a : (Subobject.underlying.obj
          ((towerFiltration unit A).F s p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj
          ((towerFiltration unit B).F (s+n) p) : ModuleCat.{v} ℤ)),
        ((towerFiltration unit A).F s p).arrow a ≫ g =
          ((towerFiltration unit B).F (s+n) p).arrow b ∧
        (towerFiltration unit A).toAssociatedGraded s p a =
          (extensionSourceIso unit g ca p s).hom x ∧
        (towerFiltration unit B).toAssociatedGraded (s+n) p b =
          (extensionTargetIso unit g cb p (s+n)).hom y := by
    have elementMap_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
        elementMap x ≫ f = elementMap (f x) := by
      ext a
      simp [elementMap]
    have strict_fiber_elements (FC : FilteredComplex (ModuleCat.{v} ℤ))
        (n s k : ℤ) (x : FC.assocGraded s k) (y : FC.assocGraded (s+n) (k-1)) :
        Nonempty (FilteredComplex.Solutions.Fiber FC n s k (elementMap x) (elementMap y)) ↔
          ∃ (a : (Subobject.underlying.obj (FC.fil s k) : ModuleCat.{v} ℤ))
            (b : (Subobject.underlying.obj (FC.fil (s+n) (k-1)) : ModuleCat.{v} ℤ)),
            FC.filToAssocGraded s k a=x ∧ FC.filToAssocGraded (s+n) (k-1) b=y ∧
            FC.d k ((FC.fil s k).arrow a)=(FC.fil (s+n) (k-1)).arrow b := by
      constructor
      · rintro ⟨W⟩
        obtain ⟨hx,hy,he⟩ := (FilteredComplex.Solutions.mem_fiber_iff W.val).mp W.property
        refine ⟨W.val.1.hom (ULift.up 1),W.val.2.hom (ULift.up 1),?_,?_,?_⟩
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hx
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hy
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · exact congrArg (fun f => f.hom (ULift.up (1:ℤ))) he
      · rintro ⟨a,b,ha,hb,he⟩
        refine ⟨⟨(elementMap a,elementMap b),(FilteredComplex.Solutions.mem_fiber_iff _).mpr ⟨?_,?_,?_⟩⟩⟩
        · change elementMap a ≫ FC.filToAssocGraded s k=elementMap x
          rw [elementMap_comp,ha]
        · change elementMap b ≫ FC.filToAssocGraded (s+n) (k-1)=elementMap y
          rw [elementMap_comp,hb]
        · rw [←Category.assoc,elementMap_comp,elementMap_comp,elementMap_comp,he]
    simp only [ExtensionEquation, strict_fiber_elements]
    constructor
    · rintro ⟨hn, a, b, ha, hb, he⟩
      refine ⟨hn, a, b, ?_, ha, hb⟩
      simp only [extensionComplex, underlyingComplex_d_one] at he
      exact he
    · rintro ⟨hn, a, b, he, ha, hb⟩
      refine ⟨hn, a, b, ha, hb, ?_⟩
      simp only [extensionComplex, underlyingComplex_d_one]
      exact he

  have tower_filtration_representative_exists
      (A : Syn) (p : ℤ×ℤ) (s : ℤ) (a : BiHom p.1 p.2 A)
      (ha : a ∈ towerFiltrationSubmodule unit A s p) :
      ∃ a' : (Subobject.underlying.obj ((towerFiltration unit A).F s p) : ModuleCat.{v} ℤ),
        ((towerFiltration unit A).F s p).arrow a' = a := by
    have hm : a ∈ (ModuleCat.subobjectModule _) ((towerFiltration unit A).F s p) := by
      simpa only [towerFiltration, OrderIso.apply_symm_apply] using ha
    exact hm

  have element_grade_equal_iff
      {ι : Type} {A : GradedObject ι (ModuleCat.{v} ℤ)}
      (F : KIP126.Algebra.Filtration A) (s : ℤ) (i : ι)
      (a b : (Subobject.underlying.obj (F.F s i) : ModuleCat.{v} ℤ)) :
      F.toAssociatedGraded s i a = F.toAssociatedGraded s i b ↔
      (F.F s i).arrow a - (F.F s i).arrow b ∈
        (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
    have em_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
        elementMap x ≫ f = elementMap (f x) := by
      ext z
      simp [elementMap]
    have em_inj {A : ModuleCat.{v} ℤ} {a b : A} (h : elementMap a = elementMap b) : a = b := by
      have he := congrArg (fun h => h.hom (ULift.up (1 : ℤ))) h
      simpa [elementMap, one_smul] using he
    constructor
    · intro h
      have he : elementMap a ≫ F.toAssociatedGraded s i =
          elementMap b ≫ F.toAssociatedGraded s i := by rw [em_comp,em_comp,h]
      obtain ⟨z,hz⟩ := (F.comp_toAssociatedGraded_eq_iff_sub_lifts s i _ _).mp he
      refine ⟨z (ULift.up 1), ?_⟩
      have hh := congrArg (fun h => h.hom (ULift.up (1:ℤ)))
        (congrArg (fun h => h ≫ (F.F s i).arrow) hz)
      simpa [Category.assoc, Subobject.ofLE_arrow, elementMap, one_smul] using hh
    · rintro ⟨z,hz⟩
      have he : elementMap z ≫ Subobject.ofLE (F.F (s+1) i) (F.F s i)
          (F.decreasing s i) = elementMap a - elementMap b := by
        apply (cancel_mono (F.F s i).arrow).mp
        rw [Category.assoc,Subobject.ofLE_arrow,Preadditive.sub_comp,em_comp,em_comp,em_comp]
        ext w
        simp [elementMap,hz,smul_sub]
      exact em_inj (by
        rw [← em_comp, ← em_comp]
        exact (F.comp_toAssociatedGraded_eq_iff_sub_lifts s i _ _).mpr ⟨elementMap z,he⟩)

  have shifted_quotient_eInfty_zero
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (e s t w : ℤ)
      (hwindow : ¬ (0 ≤ t-(w-e) ∧ t-(w-e) < (q:ℤ))) :
      IsZero (((D.family.obj (XModLambdaN
        ((SyntheticCategory.biShift (0,e)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector))) q)).sequence.ssData
          (s,t,w)).eInfty) := by
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    haveI : Subsingleton (finiteEInftyModel H (X.obj D.hopfAndDetector) q (s,t) (w-e)) := by
      simp only [finiteEInftyModel, hwindow, ite_false]
      infer_instance
    haveI : Subsingleton (((D.family.obj (XModLambdaN A q)).sequence.ssData (s,t,w-e)).eInfty) :=
      (synthetic.eInfty.presentation.finite (X.obj D.hopfAndDetector) q hq (s,t) (w-e)).injective.subsingleton
    let z : ((D.family.obj ((SyntheticCategory.biShift (0,e)).obj (XModLambdaN A q))).sequence.ssData
        (s,t,w)).eInfty ≃ₗ[ℤ]
        ((D.family.obj (XModLambdaN A q)).sequence.ssData (s,t,w-e)).eInfty := by
      have z0 := synthetic.eInfty.weightShift.iso (XModLambdaN A q) e (s,t) (w-e)
      have he : w - e + e = w := by omega
      exact (congrArg (fun z : ℤ =>
        ((D.family.obj ((SyntheticCategory.biShift (0,e)).obj (XModLambdaN A q))).sequence.ssData
          (s,t,z)).eInfty ≃ₗ[ℤ]
        ((D.family.obj (XModLambdaN A q)).sequence.ssData (s,t,w-e)).eInfty) he) ▸ z0
    haveI : Subsingleton (((D.family.obj ((SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN A q))).sequence.ssData (s,t,w)).eInfty) := z.injective.subsingleton
    have hz := ModuleCat.isZero_of_subsingleton (((D.family.obj
      ((SyntheticCategory.biShift (0,e)).obj (XModLambdaN A q))).sequence.ssData (s,t,w)).eInfty)
    letI := D.shiftCommShift (0,e)
    letI := D.shiftExact (0,e)
    obtain ⟨Q,hQ⟩ := quotient_shift_exists D.shiftCoherence (0,e) q A
    let eval : KIP126.SpectralSequence (ModuleCat.{v} ℤ) Tridegree ⥤ ModuleCat.{v} ℤ := {
      obj := fun E => (E.ssData (s,t,w)).eInfty
      map := fun f => f.eInftyMap (s,t,w)
      map_id := fun E => SpectralSequenceMorphism.eInftyMap_id E (s,t,w)
      map_comp := fun f g => SpectralSequenceMorphism.eInftyMap_comp f g (s,t,w) }
    exact hz.of_iso ((D.family.functor ⋙ eval).mapIso Q)

  have extension_source_image_iff_lift
      {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
      {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
      {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H}
      (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
      {T : Syn} (g : B.obj D.nu D.hopfAndDetector ⟶ T) (p : ℤ×ℤ) (k : ℤ)
      (x : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (B.obj D.nu D.hopfAndDetector)).F k p) : ModuleCat.{v} ℤ)) :
      (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p k).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p x)
        ∈ Set.range ((D.family.functor.map f).eInftyMap (k,p.1+k,p.2)).hom ↔
      ∃ a : BiHom p.1 p.2 (A.obj D.nu D.hopfAndDetector),
        a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector) k p ∧
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F k p).arrow x -
          (syntheticHomotopyMap f p) a ∈
          towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector) (k+1) p := by
    have graded_image_iff_lift
        {ι : Type} {A B : GradedObject ι (ModuleCat.{v} ℤ)}
        {F : KIP126.Algebra.Filtration A} {G : KIP126.Algebra.Filtration B} (f : KIP126.Algebra.FilteredMorphism F G)
        (s : ℤ) (i : ι) (x : (Subobject.underlying.obj (G.F s i) : ModuleCat.{v} ℤ)) :
        (∃ z : F.associatedGraded s i,
          f.associatedGradedMap s i z = G.toAssociatedGraded s i x) ↔
        ∃ a : A i, a ∈ (ModuleCat.subobjectModule (A i)) (F.F s i) ∧
          (G.F s i).arrow x - f.map i a ∈
            (ModuleCat.subobjectModule (B i)) (G.F (s+1) i) := by
      have hc (a : (Subobject.underlying.obj (F.F s i) : ModuleCat.{v} ℤ)) :
          f.map i ((F.F s i).arrow a) = (G.F s i).arrow ((f.preserves s i).choose a) := by
        exact (congrArg (fun h => h.hom a) (f.preserves s i).choose_spec).symm
      have hg (a : (Subobject.underlying.obj (F.F s i) : ModuleCat.{v} ℤ)) :
          f.associatedGradedMap s i (F.toAssociatedGraded s i a) =
          G.toAssociatedGraded s i ((f.preserves s i).choose a) :=
        congrArg (fun h => h.hom a) (KIP126.Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap f s i)
      constructor
      · rintro ⟨z,hz⟩
        haveI : Epi (F.toAssociatedGraded s i) := inferInstanceAs (Epi (cokernel.π _))
        obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s i)).mp inferInstance z
        refine ⟨(F.F s i).arrow a, ⟨a,rfl⟩, ?_⟩
        rw [hc]
        apply (element_grade_equal_iff G s i x _).mp
        rw [← hg,ha,hz]
      · rintro ⟨_,⟨a,rfl⟩,ha⟩
        refine ⟨F.toAssociatedGraded s i a, ?_⟩
        rw [hc] at ha
        rw [hg]
        exact ((element_grade_equal_iff G s i x _).mpr ha).symm
    have infinity_image_iff_lift
        {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
        {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
        {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H}
        (D : AdamsComparison H M Syn) (A B : SyntheticObject)
        (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
        (q : Tridegree)
        (x : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector)).F q.1 (q.2.1-q.1,q.2.2)) : ModuleCat.{v} ℤ)) :
        ((D.convergence B).identification q).inv
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded q.1 (q.2.1-q.1,q.2.2) x)
          ∈ Set.range ((D.family.functor.map f).eInftyMap q).hom ↔
        ∃ a : BiHom (q.2.1-q.1) q.2.2 (A.obj D.nu D.hopfAndDetector),
          a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
            (A.obj D.nu D.hopfAndDetector) q.1 (q.2.1-q.1,q.2.2) ∧
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
            q.1 (q.2.1-q.1,q.2.2)).arrow x - (syntheticHomotopyMap f (q.2.1-q.1,q.2.2)) a ∈
            towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
              (B.obj D.nu D.hopfAndDetector) (q.1+1) (q.2.1-q.1,q.2.2) := by
      obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
      let fm : KIP126.Algebra.FilteredMorphism
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAlgebra
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAlgebra :=
        { map := c.aMap, preserves := c.filtration_compat }
      have hc := c.iso_compat q
      simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
        TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
      rw [hce] at hc
      change (D.family.functor.map f).eInftyMap q ≫ ((D.convergence B).identification q).hom =
        ((D.convergence A).identification q).hom ≫ fm.associatedGradedMap q.1 (q.2.1-q.1,q.2.2) at hc
      have hi : (∃ z, (D.family.functor.map f).eInftyMap q z =
          ((D.convergence B).identification q).inv
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded q.1 (q.2.1-q.1,q.2.2) x)) ↔
          ∃ z, fm.associatedGradedMap q.1 (q.2.1-q.1,q.2.2) z =
            (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded q.1 (q.2.1-q.1,q.2.2) x := by
        constructor
        · rintro ⟨z,hz⟩
          refine ⟨((D.convergence A).identification q).hom z,?_⟩
          have he := congrArg (fun h => h.hom z) hc
          change ((D.convergence B).identification q).hom ((D.family.functor.map f).eInftyMap q z) = fm.associatedGradedMap _ _ (((D.convergence A).identification q).hom z) at he
          rw [← he,hz]
          exact ((D.convergence B).identification q).toLinearEquiv.apply_symm_apply _
        · rintro ⟨z,hz⟩
          refine ⟨((D.convergence A).identification q).inv z,?_⟩
          apply ((D.convergence B).identification q).toLinearEquiv.injective
          have he := congrArg (fun h => h.hom (((D.convergence A).identification q).inv z)) hc
          change ((D.convergence B).identification q).hom ((D.family.functor.map f).eInftyMap q (((D.convergence A).identification q).inv z)) = fm.associatedGradedMap _ _ (((D.convergence A).identification q).hom (((D.convergence A).identification q).inv z)) at he
          change ((D.convergence B).identification q).hom _ = ((D.convergence B).identification q).hom _
          rw [he]
          have hA := ((D.convergence A).identification q).toLinearEquiv.apply_symm_apply z
          have hB := ((D.convergence B).identification q).toLinearEquiv.apply_symm_apply
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded q.1 (q.2.1-q.1,q.2.2) x)
          change ((D.convergence A).identification q).hom (((D.convergence A).identification q).inv z) = z at hA
          change ((D.convergence B).identification q).hom (((D.convergence B).identification q).inv _) = _ at hB
          rw [hA,hB]
          exact hz
      change (∃ z, _ = _) ↔ _
      refine hi.trans ((graded_image_iff_lift fm q.1 (q.2.1-q.1,q.2.2) x).trans ?_)
      simp only [fm, KIP126.SpectralSequence.Filtration.toAlgebra,towerFiltration,
        OrderIso.apply_symm_apply,hca]
      rfl
    have transport {I : Type} (M : I → ModuleCat.{v} ℤ) (S : ∀i,Subobject (M i))
        (G : I → ModuleCat.{v} ℤ) (pr : ∀i, Subobject.underlying.obj (S i) ⟶ G i)
        {E : ModuleCat.{v} ℤ} {i j : I} (e : E ≅ G i) (R : Set E)
        (P : ∀i, M i → Prop)
        (h : ∀x, e.inv (pr i x) ∈ R ↔ P i ((S i).arrow x))
        (hij : i=j) (x : (Subobject.underlying.obj (S j) : ModuleCat.{v} ℤ)) :
        (e ≪≫ eqToIso (congrArg G hij)).inv (pr j x) ∈ R ↔ P j ((S j).arrow x) := by
      subst j
      simpa only [eqToIso_refl,Iso.trans_refl] using h x
    exact transport
      (syntheticHomotopy (B.obj D.nu D.hopfAndDetector))
      (fun p => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F k p)
      (fun p => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).associatedGraded k p)
      (fun p => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p)
      ((D.convergence B).identification (k,p.1+k,p.2))
      (Set.range ((D.family.functor.map f).eInftyMap (k,p.1+k,p.2)).hom)
      (fun p b => ∃ a : BiHom p.1 p.2 (A.obj D.nu D.hopfAndDetector),
        a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector) k p ∧
        b - (syntheticHomotopyMap f p) a ∈
        towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector) (k+1) p)
      (fun x => infinity_image_iff_lift D A B f (k,p.1+k,p.2) x)
      (show (p.1+k-k,p.2)=p by ext <;> simp) x
  let p : ℤ × ℤ := (t - s, t + normalizedExponent H f)
  let Aearly := (SyntheticObject.quotient (rEarlier - 1)
    (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector
  let Alater := (SyntheticObject.quotient (rLater - 1)
    (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector
  let Bearly := (SyntheticObject.quotient (rEarlier - 1) (.nu Y)).obj D.nu D.hopfAndDetector
  let E : ℤ → AddSubgroup (BiHom p.1 p.2 Aearly) :=
    fun k => (towerFiltrationSubmodule unit Aearly k p).toAddSubgroup
  let L : ℤ → AddSubgroup (BiHom p.1 p.2 Alater) :=
    fun k => (towerFiltrationSubmodule unit Alater k p).toAddSubgroup
  let F : ℤ → AddSubgroup (BiHom p.1 p.2 Bearly) :=
    fun k => (towerFiltrationSubmodule unit Bearly k p).toAddSubgroup
  let T := F (s + n + 1)
  let ρ : BiHom p.1 p.2 Alater →+ BiHom p.1 p.2 Aearly :=
    (syntheticHomotopyMap
      ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
        (rEarlier - 1) (rLater - 1) (Nat.sub_le_sub_right hle 1)) p).hom.toAddMonoidHom
  let g : BiHom p.1 p.2 Aearly →+ BiHom p.1 p.2 Bearly :=
    (syntheticHomotopyMap (finiteExtensionMap D X Y f (rEarlier - 1)) p).hom.toAddMonoidHom
  have hL : Antitone L := by
    intro i j hij z hz
    exact towerFiltrationSubmodule_antitone unit Alater p hij hz
  have actual_map_preserves {U V : Syn} (h : U ⟶ V) (k : ℤ)
      (z : BiHom p.1 p.2 U) (hz : z ∈ towerFiltrationSubmodule unit U k p) :
      z ≫ h ∈ towerFiltrationSubmodule unit V k p := by
    obtain ⟨a, ha⟩ := hz
    refine ⟨a ≫ adamsTowerInduced unit h k.toNat, ?_⟩
    change (a ≫ adamsTowerInduced unit h k.toNat) ≫
      adamsTowerMap unit V 0 k.toNat (Nat.zero_le _) = z ≫ h
    rw [Category.assoc, adamsTowerInduced_map, ← Category.assoc]
    exact congrArg (fun b => b ≫ h) ha
  have hg : ∀ k : ℤ, ∀ δ : BiHom p.1 p.2 Aearly, δ ∈ E k → g δ ∈ F k := by
    intro k δ hδ
    exact actual_map_preserves (finiteExtensionMap D X Y f (rEarlier - 1)) k δ hδ
  have hstep : ∀ k : ℤ, s + 1 ≤ k → k < s + 1 + n.toNat →
      ∀ δ : BiHom p.1 p.2 Aearly, δ ∈ E k →
      (∃ ε : BiHom p.1 p.2 Alater, ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)) ∨ g δ ∈ T := by
    intro k hk hkn δ hδ
    by_cases hlift : ∃ ε : BiHom p.1 p.2 Alater, ε ∈ L k ∧ δ - ρ ε ∈ E (k + 1)
    · exact Or.inl hlift
    right
    by_contra hnot
    have hlast : k + ((s + n + 1 - k).toNat : ℤ) = s + n + 1 := by omega
    obtain ⟨l, hkl, hln, hgl, hgnext⟩ := first_nonzero_filtration_grade F k
      (s + n + 1 - k).toNat (g δ) (hg k δ hδ) (by simpa only [hlast] using hnot)
    apply hcross
    have module_map_zero {A B : ModuleCat.{v} ℤ} (f : A ⟶ B) : f (0 : A) = 0 := f.hom.map_zero
    have hln' : l ≤ s + n := by omega
    obtain ⟨a, hka⟩ : ∃ a : ℕ, k = s + a :=
      ⟨(k-s).toNat, by omega⟩
    subst k
    have ha : 0 < a := by omega
    obtain ⟨b, hl⟩ : ∃ b : ℕ, l = s + a + (n-a-b) :=
      ⟨(s+n-l).toNat, by omega⟩
    subst l
    have hab : (a : ℤ) + b ≤ n := by omega
    obtain ⟨da, hda⟩ := tower_filtration_representative_exists Aearly p (s+a) δ hδ
    obtain ⟨db, hdb⟩ := tower_filtration_representative_exists Bearly p
      (s+a+(n-a-b)) (g δ) hgl
    let u := (extensionSourceIso unit (finiteExtensionMap D X Y f (rEarlier-1))
      (D.convergence (.quotient (rEarlier-1) (extensionSourceObject D X Y f))) p (s+a)).inv
      ((towerFiltration unit Aearly).toAssociatedGraded (s+a) p da)
    let v := (extensionTargetIso unit (finiteExtensionMap D X Y f (rEarlier-1))
      (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).inv
      ((towerFiltration unit Bearly).toAssociatedGraded (s+a+(n-a-b)) p db)
    have hu : u ∉ Set.range (((D.family.functor.map
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))).eInftyMap
            (s+a,p.1+(s+a),p.2)).hom) := by
      intro hu
      obtain ⟨ε,hε,hres⟩ := (extension_source_image_iff_lift D
        (.quotient (rLater-1) (extensionSourceObject D X Y f))
        (.quotient (rEarlier-1) (extensionSourceObject D X Y f))
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
          (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1))
        (finiteExtensionMap D X Y f (rEarlier-1)) p (s+a) da).mp hu
      apply hlift
      refine ⟨ε,hε,?_⟩
      rw [hda] at hres
      exact hres
    have haupper : a ≤ rEarlier-2 := by
      by_contra ha'
      have hz := shifted_quotient_eInfty_zero D synthetic X (rEarlier-1) (by omega)
        (normalizedExponent H f) (s+a) (p.1+(s+a)) p.2 (by
          dsimp only [p]
          omega)
      haveI := ModuleCat.subsingleton_of_isZero hz
      apply hu
      refine ⟨0, ?_⟩
      have hu0 : u = 0 := Subsingleton.elim _ _
      exact (module_map_zero _).trans hu0.symm
    have hv : v ≠ 0 := by
      intro hv
      have hgrade : (towerFiltration unit Bearly).toAssociatedGraded
          (s+a+(n-a-b)) p db = 0 := by
        apply (extensionTargetIso unit (finiteExtensionMap D X Y f (rEarlier-1))
          (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).toLinearEquiv.symm.injective
        exact hv.trans ((extensionTargetIso unit (finiteExtensionMap D X Y f (rEarlier-1))
          (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).inv.hom.map_zero.symm)
      have hnext := (element_grade_equal_iff (towerFiltration unit Bearly).toAlgebra
        (s+a+(n-a-b)) p db 0).mp (by
          change (towerFiltration unit Bearly).toAssociatedGraded (s+a+(n-a-b)) p db =
            (towerFiltration unit Bearly).toAssociatedGraded (s+a+(n-a-b)) p 0
          rw [module_map_zero]
          exact hgrade)
      change ((towerFiltration unit Bearly).F (s+a+(n-a-b)) p).arrow db -
        ((towerFiltration unit Bearly).F (s+a+(n-a-b)) p).arrow 0 ∈
        (ModuleCat.subobjectModule _) ((towerFiltration unit Bearly).F (s+a+(n-a-b)+1) p) at hnext
      rw [module_map_zero,sub_zero,hdb] at hnext
      have hnext' : g δ ∈ towerFiltrationSubmodule unit Bearly (s+a+(n-a-b)+1) p := by
        simpa only [towerFiltration, OrderIso.apply_symm_apply] using hnext
      exact hgnext hnext'
    refine ⟨hle,a,b,ha,haupper,hab,u,v,hu,?_,hv⟩
    apply (extension_equation_iff_representatives
      (finiteExtensionMap D X Y f (rEarlier-1))
      (D.convergence (.quotient (rEarlier-1) (extensionSourceObject D X Y f)))
      (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a) (n-a-b) u v).mpr
    refine ⟨by omega,da,db,?_,?_,?_⟩
    · change ((towerFiltration unit Aearly).F (s+a) p).arrow da ≫
        finiteExtensionMap D X Y f (rEarlier-1) =
        ((towerFiltration unit Bearly).F (s+a+(n-a-b)) p).arrow db
      rw [hda,hdb]
      rfl
    · exact ((extensionSourceIso unit (finiteExtensionMap D X Y f (rEarlier-1))
        (D.convergence (.quotient (rEarlier-1) (extensionSourceObject D X Y f))) p (s+a)).toLinearEquiv.apply_symm_apply _).symm
    · exact ((extensionTargetIso unit (finiteExtensionMap D X Y f (rEarlier-1))
        (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+a+(n-a-b))).toLinearEquiv.apply_symm_apply _).symm
  have hcorrect (α₀ : BiHom p.1 p.2 Aearly) (α : BiHom p.1 p.2 Alater)
      (hδ : α₀ - ρ α ∈ E (s + 1)) :
      ∃ α' : BiHom p.1 p.2 Alater, α' - α ∈ L (s + 1) ∧
        g (α₀ - ρ α') ∈ T := by
    apply finite_filtration_correction ρ g E L T hL (s + 1) n.toNat hstep
    · intro δ hδ
      have hlast : s + 1 + (n.toNat : ℤ) = s + n + 1 := by omega
      exact hg (s + n + 1) δ (by simpa only [hlast] using hδ)
    · exact hδ
  obtain ⟨W⟩ := hW
  have next_tower_filtration_of_rho
      {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
      {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
      {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H}
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (Y : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (s m w : ℤ) (hupper : m+s-w < i)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j))
      (ha : a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
        (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j) s (m,w))
      (hb : a ≫ (D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho i j hij ∈
        towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) i) (s+1) (m,w)) :
      a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
        (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j) (s+1) (m,w) := by
    have next_filtration_lift_of_graded_mono
        {C : Type (v+1)} [Category.{v} C] [Abelian C]
        {ι : Type} {A B : GradedObject ι C}
        {F : KIP126.Algebra.Filtration A} {G : KIP126.Algebra.Filtration B} (f : KIP126.Algebra.FilteredMorphism F G)
        (s : ℤ) (i : ι) [Mono (f.associatedGradedMap s i)]
        {T : C} (x : T ⟶ Subobject.underlying.obj (F.F s i))
        (y : T ⟶ Subobject.underlying.obj (G.F (s+1) i))
        (hy : y ≫ (G.F (s+1) i).arrow = x ≫ (F.F s i).arrow ≫ f.map i) :
        ∃ x' : T ⟶ Subobject.underlying.obj (F.F (s+1) i),
          x' ≫ Subobject.ofLE (F.F (s+1) i) (F.F s i) (F.decreasing s i) = x := by
      apply (F.comp_toAssociatedGraded_eq_zero_iff_lifts s i x).mp
      apply (cancel_mono (f.associatedGradedMap s i)).mp
      rw [zero_comp, Category.assoc, KIP126.Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap]
      have hxy : x ≫ (f.preserves s i).choose =
          y ≫ Subobject.ofLE (G.F (s+1) i) (G.F s i) (G.decreasing s i) := by
        apply (cancel_mono (G.F s i).arrow).mp
        rw [Category.assoc, (f.preserves s i).choose_spec, Category.assoc,
          Subobject.ofLE_arrow]
        exact hy.symm
      rw [← Category.assoc, hxy, Category.assoc]
      change y ≫ (Subobject.ofLE (G.F (s+1) i) (G.F s i) (G.decreasing s i) ≫
        cokernel.π _) = 0
      rw [cokernel.condition, comp_zero]

    have next_filtration_mem_of_graded_mono
        {ι : Type} {A B : GradedObject ι (ModuleCat.{v} ℤ)}
        {F : KIP126.Algebra.Filtration A} {G : KIP126.Algebra.Filtration B} (f : KIP126.Algebra.FilteredMorphism F G)
        (s : ℤ) (i : ι) [Mono (f.associatedGradedMap s i)]
        (a : A i) (ha : a ∈ (ModuleCat.subobjectModule (A i)) (F.F s i))
        (hb : f.map i a ∈ (ModuleCat.subobjectModule (B i)) (G.F (s+1) i)) :
        a ∈ (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, hy⟩ := hb
      open KIP126.Synthetic.PageExtension in
      have hxy : elementMap y ≫ (G.F (s+1) i).arrow =
          elementMap x ≫ (F.F s i).arrow ≫ f.map i := by
        ext z
        simp [elementMap]
        change _ = _ at hy
        exact congrArg _ hy
      obtain ⟨x', hx'⟩ := next_filtration_lift_of_graded_mono f s i _ _ hxy
      refine ⟨x' (ULift.up 1), ?_⟩
      have he := congrArg (fun h => h.hom (ULift.up 1))
        (congrArg (fun h => h ≫ (F.F s i).arrow) hx')
      simpa [Category.assoc, Subobject.ofLE_arrow,
        KIP126.Synthetic.PageExtension.elementMap, one_smul] using he

    have next_tower_filtration_of_infinity_injective
        (A B : SyntheticObject)
        (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
        (q : Tridegree)
        (hf : Function.Injective ((D.family.functor.map f).eInftyMap q).hom)
        (a : BiHom (q.2.1-q.1) q.2.2 (A.obj D.nu D.hopfAndDetector))
        (ha : a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector) q.1 (q.2.1-q.1,q.2.2))
        (hb : a ≫ f ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector) (q.1+1) (q.2.1-q.1,q.2.2)) :
        a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector) (q.1+1) (q.2.1-q.1,q.2.2) := by
      obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
      let fm : KIP126.Algebra.FilteredMorphism
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAlgebra
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAlgebra :=
        { map := c.aMap, preserves := c.filtration_compat }
      have hc := c.iso_compat q
      simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
        TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
      rw [hce] at hc
      change (D.family.functor.map f).eInftyMap q ≫ ((D.convergence B).identification q).hom =
        ((D.convergence A).identification q).hom ≫ fm.associatedGradedMap q.1 (q.2.1-q.1,q.2.2) at hc
      have he (a : (towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector)).associatedGraded q.1 (q.2.1-q.1,q.2.2)) :
          ((D.convergence B).identification q).hom
            ((D.family.functor.map f).eInftyMap q (((D.convergence A).identification q).inv a)) =
          fm.associatedGradedMap q.1 (q.2.1-q.1,q.2.2) a := by
        have h := congrArg (fun h => h.hom (((D.convergence A).identification q).inv a)) hc
        simp only [ModuleCat.comp_apply] at h
        exact h.trans (congrArg _ (((D.convergence A).identification q).toLinearEquiv.apply_symm_apply a))
      haveI : Mono (fm.associatedGradedMap q.1 (q.2.1-q.1,q.2.2)) := by
        apply (ModuleCat.mono_iff_injective _).mpr
        intro a b hab
        apply ((D.convergence A).identification q).symm.toLinearEquiv.injective
        apply hf
        apply ((D.convergence B).identification q).toLinearEquiv.injective
        exact (he a).trans (hab.trans (he b).symm)
      have hm : a ∈ (ModuleCat.subobjectModule _)
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F (q.1+1) (q.2.1-q.1,q.2.2)) := by
        apply next_filtration_mem_of_graded_mono fm q.1 (q.2.1-q.1,q.2.2) a
        · simpa only [KIP126.SpectralSequence.Filtration.toAlgebra,towerFiltration,
            OrderIso.apply_symm_apply] using ha
        · change c.aMap (q.2.1-q.1,q.2.2) a ∈ _
          rw [hca]
          simp only [KIP126.SpectralSequence.Filtration.toAlgebra,towerFiltration,
            OrderIso.apply_symm_apply]
          exact hb
      simpa only [towerFiltration,OrderIso.apply_symm_apply] using hm

    have next_tower_filtration_of_infinity_injective_regraded
        (A B : SyntheticObject)
        (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
        (s m w : ℤ)
        (hf : Function.Injective ((D.family.functor.map f).eInftyMap (s,m+s,w)).hom)
        (a : BiHom m w (A.obj D.nu D.hopfAndDetector))
        (ha : a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector) s (m,w))
        (hb : a ≫ f ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector) (s+1) (m,w)) :
        a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector) (s+1) (m,w) := by
      have h0 : ∀ (a : BiHom (m+s-s) w (A.obj D.nu D.hopfAndDetector)),
          a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
            (A.obj D.nu D.hopfAndDetector) s (m+s-s,w) →
          a ≫ f ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
            (B.obj D.nu D.hopfAndDetector) (s+1) (m+s-s,w) →
          a ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
            (A.obj D.nu D.hopfAndDetector) (s+1) (m+s-s,w) :=
        next_tower_filtration_of_infinity_injective A B f (s,m+s,w) hf
      rw [add_sub_cancel_right] at h0
      exact h0 a ha hb

    apply next_tower_filtration_of_infinity_injective_regraded (.quotient j (.nu Y))
      (.quotient i (.nu Y)) _ s m w _ a ha hb
    by_cases hlower : 0 ≤ m+s-w
    · have hw : 0 ≤ m+s-w ∧ m+s-w < i := ⟨hlower,hupper⟩
      intro x y hxy
      apply (synthetic.eInfty.presentation.finiteWindow (Y.obj D.hopfAndDetector) j (by omega)
        (s,m+s) w (by constructor <;> omega)).injective
      have hcycles : cycles H (Y.obj D.hopfAndDetector) ((j:ℤ)-(m+s)+w) (s,m+s) ≤
          cycles H (Y.obj D.hopfAndDetector) ((i:ℤ)-(m+s)+w) (s,m+s) :=
        cycles_antitone H (Y.obj D.hopfAndDetector) (s,m+s) (by omega)
      apply KIP126.Algebra.NestedQuotient.cycle_map_injective hcycles
      change quotientMap H (Y.obj D.hopfAndDetector) (by omega) (le_refl _) (s,m+s) _ =
        quotientMap H (Y.obj D.hopfAndDetector) (by omega) (le_refl _) (s,m+s) _
      rw [← synthetic.eInfty.maps.rho_finite (Y.obj D.hopfAndDetector) i j hi hij (s,m+s) w hw x,
        ← synthetic.eInfty.maps.rho_finite (Y.obj D.hopfAndDetector) i j hi hij (s,m+s) w hw y]
      exact congrArg (synthetic.eInfty.presentation.finiteWindow
        (Y.obj D.hopfAndDetector) i hi (s,m+s) w hw) hxy
    · have hwindow : ¬ (0 ≤ m+s-w ∧ m+s-w < j) := by omega
      haveI : Subsingleton (finiteEInftyModel H (Y.obj D.hopfAndDetector) j (s,m+s) w) := by
        simp only [finiteEInftyModel,hwindow,ite_false]
        infer_instance
      have hzero : Subsingleton (((D.family.obj (XModLambdaN
          (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)).sequence.ssData (s,m+s,w)).eInfty) :=
        (synthetic.eInfty.presentation.finite (Y.obj D.hopfAndDetector) j (by omega)
          (s,m+s) w).injective.subsingleton
      intro a b _
      exact @Subsingleton.elim _ hzero a b
  obtain ⟨xx,yy,hxx,hyy,hxxrho,hyyrho⟩ :=
    KIP126.Main.ExtensionLaws.finite_representatives_lift D synthetic X Y f
      rEarlier rLater n s t x y hr hle hn hnUpper hx hy W
  let Blater := (SyntheticObject.quotient (rLater-1) (.nu Y)).obj D.nu D.hopfAndDetector
  let FL : ℤ → AddSubgroup (BiHom p.1 p.2 Blater) :=
    fun k => (towerFiltrationSubmodule unit Blater k p).toAddSubgroup
  let ra : Alater ⟶ Aearly := (D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let rb : Blater ⟶ Bearly := (D.quotientTower (D.nu.functor.obj (Y.obj D.hopfAndDetector))).rho
    (rEarlier-1) (rLater-1) (Nat.sub_le_sub_right hle 1)
  let ge : Aearly ⟶ Bearly := finiteExtensionMap D X Y f (rEarlier-1)
  let gl : Alater ⟶ Blater := finiteExtensionMap D X Y f (rLater-1)
  let IA := extensionSourceIso unit gl (D.convergence (.quotient (rLater-1)
    (extensionSourceObject D X Y f))) p s
  let IB := extensionTargetIso unit gl (D.convergence (.quotient (rLater-1) (.nu Y))) p (s+n)
  let IEA := extensionSourceIso unit ge (D.convergence (.quotient (rEarlier-1)
    (extensionSourceObject D X Y f))) p s
  let IEB := extensionTargetIso unit ge (D.convergence (.quotient (rEarlier-1) (.nu Y))) p (s+n)
  haveI : Epi ((towerFiltration unit Alater).toAssociatedGraded s p) :=
    inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi ((towerFiltration unit Blater).toAssociatedGraded (s+n) p) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective
    ((towerFiltration unit Alater).toAssociatedGraded s p)).mp inferInstance (IA.hom xx)
  obtain ⟨br,hbr⟩ := (ModuleCat.epi_iff_surjective
    ((towerFiltration unit Blater).toAssociatedGraded (s+n) p)).mp inferInstance (IB.hom yy)
  let α : BiHom p.1 p.2 Alater := ((towerFiltration unit Alater).F s p).arrow ar
  let β : BiHom p.1 p.2 Blater := ((towerFiltration unit Blater).F (s+n) p).arrow br
  have hα : α ∈ L s := by
    have h : α ∈ (ModuleCat.subobjectModule _) ((towerFiltration unit Alater).F s p) := ⟨ar,rfl⟩
    simp only [towerFiltration, OrderIso.apply_symm_apply] at h
    exact h
  have hβ : β ∈ FL (s+n) := by
    have h : β ∈ (ModuleCat.subobjectModule _) ((towerFiltration unit Blater).F (s+n) p) := ⟨br,rfl⟩
    simp only [towerFiltration, OrderIso.apply_symm_apply] at h
    exact h
  obtain ⟨_,a0r,b0r,ha0b0,ha0,hb0⟩ :=
    (extension_equation_iff_representatives ge
      (D.convergence (.quotient (rEarlier-1) (extensionSourceObject D X Y f)))
      (D.convergence (.quotient (rEarlier-1) (.nu Y))) p s n W.source W.target).mp W.equation
  let α0 : BiHom p.1 p.2 Aearly := ((towerFiltration unit Aearly).F s p).arrow a0r
  let β0 : BiHom p.1 p.2 Bearly := ((towerFiltration unit Bearly).F (s+n) p).arrow b0r
  have map_preserves {U V : Syn} (h : U ⟶ V) (k : ℤ)
      (z : BiHom p.1 p.2 U) (hz : z ∈ towerFiltrationSubmodule unit U k p) :
      z ≫ h ∈ towerFiltrationSubmodule unit V k p := by
    obtain ⟨a,ha⟩ := hz
    refine ⟨a ≫ adamsTowerInduced unit h k.toNat,?_⟩
    change (a ≫ adamsTowerInduced unit h k.toNat) ≫ adamsTowerMap unit V 0 k.toNat (Nat.zero_le _) = z ≫ h
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc]
    exact congrArg (fun b => b ≫ h) ha
  have actual_representative_grade_naturality
      {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
      {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
      {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H}
      (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
      {UA UB : Syn} (gA : A.obj D.nu D.hopfAndDetector ⟶ UA) (gB : B.obj D.nu D.hopfAndDetector ⟶ UB)
      (p : ℤ×ℤ) (k : ℤ)
      (a : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (A.obj D.nu D.hopfAndDetector)).F k p) : ModuleCat.{v} ℤ))
      (b : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (B.obj D.nu D.hopfAndDetector)).F k p) : ModuleCat.{v} ℤ))
      (hab : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F k p).arrow a ≫ f =
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F k p).arrow b) :
      (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gB (D.convergence B) p k).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b) =
      (D.family.functor.map f).eInftyMap (k,p.1+k,p.2)
        ((extensionSourceIso (nuCoefficientUnit H.unit D.nu) gA (D.convergence A) p k).inv
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p a)) := by
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
    have hc := c.iso_compat (k,p.1+k,p.2)
    simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
      TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
    rw [hce] at hc
    have transport {I : Type} (P Q : I → ModuleCat.{v} ℤ) (F : ∀i, P i ⟶ Q i)
        {i j : I} (h : i=j) {U V : ModuleCat.{v} ℤ} (a : U ⟶ P i) (b : V ⟶ Q i)
        (g : U ⟶ V) (he : g≫b=a≫F i) :
        (a≫eqToHom (congrArg P h))≫F j=g≫(b≫eqToHom (congrArg Q h)) := by
      subst j
      simpa only [eqToHom_refl,Category.comp_id] using he.symm
    have hn :
        (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gA (D.convergence A) p k).hom ≫
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat k p =
        (D.family.functor.map f).eInftyMap (k,p.1+k,p.2) ≫
          (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gB (D.convergence B) p k).hom := by
      exact transport (I:=ℤ×ℤ) (i:=(p.1+k-k,p.2)) (j:=p)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).associatedGraded k m)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).associatedGraded k m)
        (fun m => Filtration.inducedAssocGradedMap c.aMap c.filtration_compat k m)
        (show (p.1+k-k,p.2)=p by ext <;> simp)
        ((D.convergence A).identification (k,p.1+k,p.2)).hom
        ((D.convergence B).identification (k,p.1+k,p.2)).hom
        ((D.family.functor.map f).eInftyMap (k,p.1+k,p.2)) hc
    have hb : (c.filtration_compat k p).choose a = b := by
      apply (ModuleCat.mono_iff_injective
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F k p).arrow).mp inferInstance
      have he := ConcreteCategory.congr_hom (c.filtration_compat k p).choose_spec a
      change ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F k p).arrow
        ((c.filtration_compat k p).choose a) =
        c.aMap p (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F k p).arrow a) at he
      have hm : c.aMap p
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F k p).arrow a) =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F k p).arrow a ≫ f := by
        rw [hca]
        rfl
      exact he.trans (hm.trans hab)
    have hp : Filtration.inducedAssocGradedMap c.aMap c.filtration_compat k p
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p a) =
        (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b := by
      have hsq : (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p ≫
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat k p =
          (c.filtration_compat k p).choose ≫
            (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p :=
        cokernel.π_desc _ _ _
      have he := ConcreteCategory.congr_hom hsq a
      simp only [ModuleCat.comp_apply] at he
      exact he.trans (congrArg
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p) hb)
    apply (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gB (D.convergence B) p k).toLinearEquiv.injective
    have he := ConcreteCategory.congr_hom hn
      ((extensionSourceIso (nuCoefficientUnit H.unit D.nu) gA (D.convergence A) p k).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p a))
    simp only [ModuleCat.comp_apply] at he
    have hA := (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gA (D.convergence A) p k).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p a)
    have hB := (extensionSourceIso (nuCoefficientUnit H.unit D.nu) gB (D.convergence B) p k).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b)
    exact hB.trans (hp.symm.trans
      ((congrArg (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat k p) hA.symm).trans he))
  have grade_difference (A B : SyntheticObject)
      (h : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector)
      {UA UB : Syn} (gA : A.obj D.nu D.hopfAndDetector ⟶ UA) (gB : B.obj D.nu D.hopfAndDetector ⟶ UB)
      (k : ℤ)
      (a : (Subobject.underlying.obj ((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p) : ModuleCat.{v} ℤ))
      (b : (Subobject.underlying.obj ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).F k p) : ModuleCat.{v} ℤ))
      (he : (D.family.functor.map h).eInftyMap (k,p.1+k,p.2)
        ((extensionSourceIso unit gA (D.convergence A) p k).inv
          ((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p a)) =
        (extensionSourceIso unit gB (D.convergence B) p k).inv
          ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b)) :
      ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).F k p).arrow b -
        (syntheticHomotopyMap h p) (((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p).arrow a) ∈
        towerFiltrationSubmodule unit (B.obj D.nu D.hopfAndDetector) (k+1) p := by
    have ha : ((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p).arrow a ∈
        towerFiltrationSubmodule unit (A.obj D.nu D.hopfAndDetector) k p := by
      have hh : ((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p).arrow a ∈
          (ModuleCat.subobjectModule _) ((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p) := ⟨a,rfl⟩
      simpa only [towerFiltration,OrderIso.apply_symm_apply] using hh
    obtain ⟨b',hb'⟩ := tower_filtration_representative_exists (B.obj D.nu D.hopfAndDetector) p k
      (((towerFiltration unit (A.obj D.nu D.hopfAndDetector)).F k p).arrow a ≫ h) (map_preserves h k _ ha)
    have hh := actual_representative_grade_naturality D A B h gA gB p k a b' hb'.symm
    have heq : (towerFiltration unit (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b =
        (towerFiltration unit (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded k p b' :=
      (extensionSourceIso unit gB (D.convergence B) p k).symm.toLinearEquiv.injective (he.symm.trans hh.symm)
    have hm := (element_grade_equal_iff (towerFiltration unit (B.obj D.nu D.hopfAndDetector)).toAlgebra k p b b').mp heq
    change ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).F k p).arrow b -
      ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).F k p).arrow b' ∈
      (ModuleCat.subobjectModule _) ((towerFiltration unit (B.obj D.nu D.hopfAndDetector)).F (k+1) p) at hm
    rw [hb'] at hm
    simp only [towerFiltration,OrderIso.apply_symm_apply] at hm
    exact hm
  have iso_cancel {A B : ModuleCat.{v} ℤ} (e : A ≅ B) (a : A) : e.inv (e.hom a) = a :=
    e.toLinearEquiv.symm_apply_apply a
  have hδ : α0 - ρ α ∈ E (s+1) := by
    apply grade_difference (.quotient (rLater-1) (extensionSourceObject D X Y f))
      (.quotient (rEarlier-1) (extensionSourceObject D X Y f)) ra gl ge s ar a0r
    change (D.family.functor.map ra).eInftyMap (s,p.1+s,p.2)
      (IA.inv ((towerFiltration unit Alater).toAssociatedGraded s p ar)) =
      IEA.inv ((towerFiltration unit Aearly).toAssociatedGraded s p a0r)
    have ha0' : (towerFiltration unit Aearly).toAssociatedGraded s p a0r = IEA.hom W.source := ha0
    rw [har,ha0',iso_cancel,iso_cancel]
    exact hxxrho
  have hβδ : Sub.sub β0 (β ≫ rb) ∈ F (s+n+1) := by
    apply grade_difference (.quotient (rLater-1) (.nu Y)) (.quotient (rEarlier-1) (.nu Y))
      rb (𝟙 _) (𝟙 _) (s+n) br b0r
    change (D.family.functor.map rb).eInftyMap (s+n,p.1+(s+n),p.2)
      (IB.inv ((towerFiltration unit Blater).toAssociatedGraded (s+n) p br)) =
      IEB.inv ((towerFiltration unit Bearly).toAssociatedGraded (s+n) p b0r)
    have hb0' : (towerFiltration unit Bearly).toAssociatedGraded (s+n) p b0r = IEB.hom W.target := hb0
    rw [hbr,hb0',iso_cancel,iso_cancel]
    exact hyyrho
  obtain ⟨α',hα'diff,hres⟩ := hcorrect α0 α hδ
  have hn0 : 0 ≤ n := le_trans (by exact_mod_cast Nat.zero_le (normalizedExponent H f)) hn
  have hα' : α' ∈ L s := by
    have hd : α'-α ∈ L s := towerFiltrationSubmodule_antitone unit Alater p (show s ≤ s+1 by omega) hα'diff
    have h := (L s).add_mem hd hα
    simpa only [sub_add_cancel] using h
  have hsquare : ra ≫ ge = gl ≫ rb :=
    (D.comparisonCompatible.quotient_naturality (D.normalizedMap X Y f).map).rho_naturality (Nat.sub_le_sub_right hle 1)
  have hrhodiff : (Sub.sub (α' ≫ gl) β) ≫ rb ∈ F (s+n+1) := by
    have hh := (F (s+n+1)).sub_mem hβδ hres
    have he : (Sub.sub (α' ≫ gl) β) ≫ rb = (Sub.sub β0 (β ≫ rb)) - g (α0 - ρ α') := by
      change _ = (Sub.sub β0 (β ≫ rb)) - (Sub.sub α0 (α' ≫ ra)) ≫ ge
      have sub_comp_actual {A B C : Syn} (a b : A ⟶ B) (c : B ⟶ C) :
          Sub.sub a b ≫ c = Sub.sub (a ≫ c) (b ≫ c) := Preadditive.sub_comp a b c
      simp only [sub_comp_actual,Category.assoc,hsquare]
      have he0 : α0 ≫ ge = β0 := ha0b0
      rw [he0]
      have algebra {G : Type v} [AddCommGroup G] (a b c : G) :
          Sub.sub c b = Sub.sub a b - Sub.sub a c := by
        change c-b = (a-b)-(a-c)
        abel
      exact algebra β0 (β ≫ rb) (α' ≫ gl ≫ rb)
    rw [he]
    exact hh
  have hstart : Sub.sub (α' ≫ gl) β ∈ FL s :=
    (FL s).sub_mem (map_preserves gl s α' hα')
      (towerFiltrationSubmodule_antitone unit Blater p (by omega) hβ)
  have hreflect : Sub.sub (α' ≫ gl) β ∈ FL (s+n+1) := by
    have he : s + (((n+1).toNat : ℕ) : ℤ) = s+n+1 := by omega
    rw [←he]
    refine KIP126.Main.ExtensionLaws.finite_filtration_reflection
      (syntheticHomotopyMap rb p).hom.toAddMonoidHom FL F
      (fun i j hij z hz => towerFiltrationSubmodule_antitone unit Bearly p hij hz)
      s (n+1).toNat ?_ (Sub.sub (α' ≫ gl) β) hstart ?_
    · intro k hk hkN z hz hrz
      exact next_tower_filtration_of_rho D synthetic Y (rEarlier-1) (rLater-1)
        (by omega) (Nat.sub_le_sub_right hle 1) k p.1 p.2 (by dsimp only [p]; omega) z hz hrz
    · rw [he]
      exact hrhodiff
  have hfinalmem : α' ≫ gl ∈ FL (s+n) := by
    have hd := towerFiltrationSubmodule_antitone unit Blater p (show s+n≤s+n+1 by omega) hreflect
    have hh := (FL (s+n)).add_mem hd hβ
    have he : Sub.sub (α' ≫ gl) β + β = α' ≫ gl := sub_add_cancel _ _
    exact he ▸ hh
  obtain ⟨ar',har'⟩ := tower_filtration_representative_exists Alater p s α' hα'
  obtain ⟨br',hbr'⟩ := tower_filtration_representative_exists Blater p (s+n) (α' ≫ gl) hfinalmem
  refine ⟨{
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := hx
    target_cycle := hy
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := ?_ }⟩
  apply (extension_equation_iff_representatives gl
    (D.convergence (.quotient (rLater-1) (extensionSourceObject D X Y f)))
    (D.convergence (.quotient (rLater-1) (.nu Y))) p s n xx yy).mpr
  refine ⟨hn0,ar',br',?_,?_,?_⟩
  ·
    rw [har',hbr']
  · rw [←har]
    apply (element_grade_equal_iff (towerFiltration unit Alater).toAlgebra s p ar' ar).mpr
    change ((towerFiltration unit Alater).F s p).arrow ar' - ((towerFiltration unit Alater).F s p).arrow ar ∈ (ModuleCat.subobjectModule _) ((towerFiltration unit Alater).F (s+1) p)
    rw [har']
    simp only [towerFiltration,OrderIso.apply_symm_apply]
    exact hα'diff
  · rw [←hbr]
    apply (element_grade_equal_iff (towerFiltration unit Blater).toAlgebra (s+n) p br' br).mpr
    change ((towerFiltration unit Blater).F (s+n) p).arrow br' - ((towerFiltration unit Blater).F (s+n) p).arrow br ∈ (ModuleCat.subobjectModule _) ((towerFiltration unit Blater).F (s+n+1) p)
    rw [hbr']
    simp only [towerFiltration,OrderIso.apply_symm_apply]
    exact hreflect

end KIP126.Main.ExtensionLaws
