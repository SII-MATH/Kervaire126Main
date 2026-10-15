module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
public import KIP126.Def.AdamsSynthetic.Extensions.Crossing.Predicates
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.SpectralSequence.Basic.Proofs
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Consequences
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.Synthetic.QuotientTower.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Computation.Hypotheses
public import Batteries.Data.String.Lemmas
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs
public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
public import KIP126.Def.Algebra.Filtration.Data
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Main.Literature.SourceComparisons.Theorems
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

-- The CSV coordinate calculations use the defining string and list equations.

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven KIP126.Literature.AdamsSynthetic
open KIP126.Algebra KIP126.LinE2 KIP126.Algebra PageRepresentatives
open KIP126.Computation.SphereAndCofiber KIP126.Computation.Near126
open KIP126.SpectralSequence.FinitePageCalculus
  (next_projection_zero_iff_incoming represents_unique differential_target_later_zero represents_d_zero_of_later represents_before represents_add_tail frame_after_second)
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
variable {C:Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn:Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H:Mod2EilenbergMacLane (C:=C)} {M':MilnorCooperations H} {D':AdamsComparison H M' Syn}
    {L':SphereAdamsClasses H} {G:TmfDetectionClasses H}
set_option maxHeartbeats 6000000 in
private theorem raise_filtration_to_eleven
    (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') (R : RealizationDetectionData D')
    (c9 : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (hc9 : Detects (D'.quotientConvergence 9 (by decide)) (9,134,132)
      (D'.quotientLabel 9 9 134 2 (I'.interpretation.basis .sphere 9 134 2)) c9)
    {A : Type v} [AddCommGroup A]
    (Phi : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9) →+ A)
    (hPhi7 : ∀ c : BiHom 125 132 (S_0_0:Syn),
      lambdaMultiply 2 c=0 → Phi (quotientClass 9 c)=0)
    (hPhi9 : Phi c9=0)
    (a : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9)) :
    ∃ b : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 b ∧ Phi b=Phi a := by
  classical
  have represents_zero_iff_boundary {H : Mod2EilenbergMacLane (C:=C)} (X : C) (r : ℤ) (hr : 2≤r)
      (p : ℤ×ℤ) (x : PageRepresentatives.Ambient H X p) :
      RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x 0 ↔
        x ∈ PageRepresentatives.boundaries H X (r-1) p := by
    let P := (adamsTowerInternalSpectralSequence H.unit X).ssData p
    let n : WithTop ℕ := ↑(r-2).toNat
    have hidx : r-1-1=r-2 := by omega
    constructor
    · rintro ⟨_,z,hz,hzr⟩
      change P.pageπ n z=0 at hzr
      obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) z).mp hzr
      change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1-1).toNat p).hom b=x
      rw [hidx]
      refine ⟨b,?_⟩
      rw [←hz,←hb]
      change (Subobject.ofLE (P.B n) (P.Z 0) _ ≫ P.pageπ 0) b =
        (Subobject.ofLE (P.Z n) (P.Z 0) _ ≫ P.pageπ 0)
          ((Subobject.ofLE (P.B n) (P.Z n) _) b)
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    · intro hx
      change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1-1).toNat p).hom b=x at hx
      rw [hidx] at hx
      obtain ⟨b,hb⟩ := hx
      refine ⟨hr,(Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) b,?_,?_⟩
      · change (Subobject.ofLE (P.Z n) (P.Z 0) _ ≫ P.pageπ 0)
          ((Subobject.ofLE (P.B n) (P.Z n) _) b)=x
        rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
        exact hb
      · change P.pageπ n ((Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)) b)=0
        rw [←CategoryTheory.comp_apply]
        change (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n) ≫
          cokernel.π (Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n))) b=0
        rw [cokernel.condition]
        rfl
  have boundary_hit_or_previous {H : Mod2EilenbergMacLane (C:=C)} (X : C) (r : ℤ) (hr : 2≤r)
      (p : ℤ×ℤ) (x : PageRepresentatives.Ambient H X p)
      (hx : x∈PageRepresentatives.boundaries H X r p) :
      x∈PageRepresentatives.boundaries H X (r-1) p ∨
        HitOnPage (adamsTowerInternalSpectralSequence H.unit X) r p x := by
    let E := adamsTowerInternalSpectralSequence H.unit X
    obtain ⟨q,rfl⟩ : ∃ q : ℤ×ℤ, q+E.diffDeg r=p := ⟨p-E.diffDeg r,sub_add_cancel _ _⟩
    let A := E.ssData (q+E.diffDeg r)
    let n := (r-2).toNat
    have hn : (r-1).toNat=n+1 := by dsimp [n]; omega
    change ∃ b, (PageRepresentatives.boundaryMap H X ↑(r-1).toNat (q+E.diffDeg r)).hom b=x at hx
    rw [hn] at hx
    obtain ⟨b,hb⟩ := hx
    let z := (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _)) b
    have hz : A.pageπ ↑(n+1) z=0 := by
      change (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _) ≫
        cokernel.π (Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _))) b=0
      rw [cokernel.condition]
      rfl
    have hnm : (↑n:WithTop ℕ)≤↑(n+1) := by exact_mod_cast Nat.le_succ n
    let y := (Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm) ≫ A.pageπ ↑n) z
    have hym : y∈LinearMap.range (E.d r q).hom :=
      (next_projection_zero_iff_incoming E r (by change (2:ℤ)≤r; exact hr) q z).mp hz
    have hy : RepresentsOnPage E r (q+E.diffDeg r) x y := by
      refine ⟨hr,(Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm)) z,?_,rfl⟩
      change (Subobject.ofLE (A.Z ↑n) (A.Z 0) _ ≫ A.pageπ 0)
        ((Subobject.ofLE (A.Z ↑(n+1)) (A.Z ↑n) (A.Z_anti hnm)) z)=x
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
      change (Subobject.ofLE (A.Z ↑(n+1)) (A.Z 0) _ ≫ A.pageπ 0)
        ((Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑(n+1)) (A.B_le_Z _)) b)=x
      rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hb
    by_cases hy0 : y=0
    · left
      rw [hy0] at hy
      exact (represents_zero_iff_boundary X r hr (q+E.diffDeg r) x).mp hy
    · right
      obtain ⟨a,ha⟩ := hym
      exact ⟨q,rfl,a,y,hy,hy0,by simpa using ha⟩
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
  have sphere_boundary_torsion_lift {D' : AdamsComparison H M' Syn}
      (R : RealizationDetectionData D') (s t : ℤ) (r : ℕ) (hr : 2≤r)
      (x : E2 H SphereSpectrum s t)
      (hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t))
      (hx : HitOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r (s,t) x) :
      ∃ a : BiHom (t-s) t (S_0_0 : Syn),
        D'.sphereFirstQuotient s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
    obtain ⟨a,ha,hat⟩ := R.detection.boundary_lift .sphere s t r hr x hp hx
    let e := SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum) ≫ D'.nu.unitIso.hom
    refine ⟨a≫e,?_,?_⟩
    · have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
        unfold quotientClass
        simp only [Category.assoc]
        exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
      rw [hc,ha]
      exact sphere_first_label_transport s t x
    · simpa only [lambdaMultiply,Category.assoc,Limits.zero_comp] using
        congrArg (fun f=>f≫e) hat
  have lambda_multiply_zero_mono (D' : AdamsComparison H M' Syn) {A : Syn} (a b : ℕ) (hab : a≤b)
      {m w : ℤ} (x : BiHom m w A) (hx : lambdaMultiply a x=0) :
      lambdaMultiply b x=0 := by
    simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at hx ⊢
    rw [lambdaPow_add D'.shiftCoherence (b-a) a b (Nat.sub_add_cancel hab)]
    simp only [Category.assoc,hx,Limits.comp_zero]
  have sphere_boundary_submodule_torsion_lift {D' : AdamsComparison H M' Syn}
      (R : RealizationDetectionData D') (s t : ℤ) (r : ℕ) (hr : 1≤r)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈PageRepresentatives.boundaries H SphereSpectrum r (s,t)) :
      ∃ a : BiHom (t-s) t (S_0_0 : Syn),
        D'.sphereFirstQuotient s t (quotientClass 1 a)=x ∧ lambdaMultiply (r-1) a=0 := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      by_cases hr1 : r=1
      · subst r
        have hx0 : x=0 := by simpa only [Nat.cast_one,PageRepresentatives.boundaries_one,Submodule.mem_bot] using hx
        subst x
        refine ⟨0,?_,?_⟩ <;> simp only [quotientClass,lambdaMultiply,Limits.zero_comp,Limits.comp_zero,map_zero]
      · have hr2 : 2≤r := by omega
        rcases boundary_hit_or_previous SphereSpectrum r (by omega) (s,t) x hx with hp|hh
        · have hprev : x∈PageRepresentatives.boundaries H SphereSpectrum ((r-1:ℕ):ℤ) (s,t) := by
            simpa only [Nat.cast_sub hr,Nat.cast_one] using hp
          obtain ⟨a,ha,hat⟩ := ih (r-1) (by omega) (by omega) hprev
          exact ⟨a,ha,lambda_multiply_zero_mono (D':=D') (r-1-1) (r-1) (by omega) a hat⟩
        · exact sphere_boundary_torsion_lift R s t r hr2 x
            (PageRepresentatives.boundaries_le_permanentCycles H SphereSpectrum (s,t) r hx) hh
  have family_map_data {D' : AdamsComparison H M' Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i = (D'.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D'.family.functor.map f).toSSDataMorphism
    let PX := (D'.family.functor.obj X).ssData i
    let PY := (D'.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D'.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D'.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat.{v} ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
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
  have detected_map {D' : AdamsComparison H M' Syn}
      (X Y : SyntheticObject) (f : X.obj D'.nu D'.hopfAndDetector ⟶ Y.obj D'.nu D'.hopfAndDetector)
      (i : Tridegree) (x : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (ha : Detects (D'.convergence X) i x a) :
      Detects (D'.convergence Y) i (familyPageMap D'.family f 2 i x) (a≫f) := by
    obtain ⟨c,hca,hce⟩ := D'.comparisonCompatible.convergence_natural X Y f
    obtain ⟨e,he,a',ha',hgr⟩ := ha
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D'.nu) (Y.obj D'.nu D'.hopfAndDetector)
    let m := (i.2.1-i.1,i.2.2)
    let k := (c.filtration_compat i.1 m).choose
    have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
      have hh := (c.filtration_compat i.1 m).choose_spec
      change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
      rw [hca] at hh
      exact hh
    have hc : c.eMap i ≫ ((D'.convergence Y).identification i).hom =
        ((D'.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
      have hh := c.iso_compat i
      simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
    have hq : F.toAssociatedGraded i.1 m ≫
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
        k≫G.toAssociatedGraded i.1 m := by
      exact cokernel.π_desc _ _ _
    refine ⟨(D'.family.functor.map f).eInftyMap i e,family_infinity_representative_map f i x e he,k a',?_,?_⟩
    · have hh := ConcreteCategory.congr_hom hk a'
      change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
      change (F.F i.1 m).arrow a'=a at ha'
      rw [ha'] at hh
      exact hh
    · have hh := ConcreteCategory.congr_hom hc e
      rw [hce] at hh
      change ((D'.convergence Y).identification i).hom ((D'.family.functor.map f).eInftyMap i e)=_
      calc
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (((D'.convergence X).identification i).hom e) := hh
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (F.toAssociatedGraded i.1 m a') := by rw [hgr]
        _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'
  have boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)}
      {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
      (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
      x ∈ boundaries H SphereSpectrum (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
    let P := E.ssData p
    obtain ⟨hr,z,hz,hzero⟩ := hx
    change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
    change P.pageπ ↑(r-2).toNat z=0 at hzero
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
    have hrindex : r-1-1=r-2 := by omega
    change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
    rw [hrindex]
    refine ⟨y,?_⟩
    have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
        cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
      dsimp only [boundaryMap,cycleMap,P,E]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    rw [←hf,CategoryTheory.comp_apply,hy]
    exact hz
  have main_af7_all_labels {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) (x : Page D' .sphere 7 132) :
      x=0 ∨ x=I'.interpretation.basis .sphere 7 132 0 := by
    classical
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 149) rfl)
    change (sequence D' .sphere).Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀i:Fin 1,e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 7 132 i.val at he
    have hf : e x=Finsupp.single (0:Fin 1) ((e x) 0) := by
      apply Finsupp.ext
      intro i
      have hi:i=0 := Subsingleton.elim _ _
      subst i
      simp only [Finsupp.single_eq_same]
    have h01 : (e x) 0=0 ∨ (e x) 0=1 := by
      generalize (e x) 0=a
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases h01 with hx|hx
    · left
      apply e.injective
      rw [hf,hx,Finsupp.single_zero,map_zero]
    · right
      rw [hx] at hf
      exact (e.symm_apply_apply x).symm.trans ((congrArg e.symm hf).trans (he 0))
  have main_af7_label_boundary {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.basis .sphere 7 132 0 ∈ boundaries H SphereSpectrum 3 (7,132) := by
    let E := sequence D' .sphere
    have hd : HasDifferential E 3 (4,130) (7,132)
        (I'.interpretation.basis .sphere 4 130 0) (I'.interpretation.basis .sphere 7 132 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,4,130,[0],7,132,[0],"S0_AdamsE2_ss",2437⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 157) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨a,ha,b,hb,h⟩ := hrow
      change HasDifferential E 3 (4,130) (7,132) a b at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0]=true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero,Option.some.injEq] at ha hb
      rw [←ha,←hb] at h
      exact h
    exact boundary_of_zero_representative (H:=H) (r:=4) (p:=(7,132))
      (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) hd)
  have main_af7_torsion_representative {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G)
      (R : RealizationDetectionData D') :
      ∃ c : BiHom 125 132 (S_0_0:Syn),
        D'.sphereFirstQuotient 7 132 (quotientClass 1 c)=I'.interpretation.basis .sphere 7 132 0 ∧
        lambdaMultiply 2 c=0 ∧
        Detects (D'.quotientConvergence 9 (by decide)) (7,132,132)
          (D'.quotientLabel 9 7 132 0 (I'.interpretation.basis .sphere 7 132 0)) (quotientClass 9 c) := by
    obtain ⟨c,hc,ht⟩ := sphere_boundary_submodule_torsion_lift R 7 132 3 (by decide)
      (I'.interpretation.basis .sphere 7 132 0) (main_af7_label_boundary I')
    have hzero : lambdaMultiply 0 c=c := by
      have hc := D'.shiftCoherence.right_unit (125,132) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (125,132) (0,0)).hom.app (S_0_0:Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 125 132:Syn) := by
        change (biShiftAddIso (125,132) (0,0) (125,132) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      change (SyntheticCategory.biShift_comp (125,132) (0,0)).inv.app (S_0_0:Syn) ≫
        SyntheticCategory.biShift_zero.hom.app (Smn 125 132:Syn) ≫ c=c
      rw [←he]
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hd := D'.comparisonCompatible.homotopy_lambda 7 132 0 c
    rw [hzero,hc] at hd
    have hq := detected_map (D':=D') .sphere (.quotient 9 .sphere)
      (XModLambdaN.incl (S_0_0:Syn) 9) (7,132,132) _ c hd
    exact ⟨c,hc,ht,hq⟩
  have candidates_raw {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      HasNonzeroDifferential (sequence D' .sphere) 3 (6,132) (9,134)
        (I'.interpretation.basis .sphere 6 132 0) (I'.interpretation.basis .sphere 9 134 3) ∨
      HasNonzeroDifferential (sequence D' .sphere) 3 (6,132) (9,134)
        (I'.interpretation.basis .sphere 6 132 0) (I'.interpretation.basis .sphere 9 134 3 + I'.interpretation.basis .sphere 9 134 2) := by
    let E := sequence D' .sphere
    have h226 : HasDifferential E 3 (9,134) (12,136)
        ((I'.interpretation.basis .sphere 9 134 1)) ((I'.interpretation.basis .sphere 12 136 0)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 226) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (9,134) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h227 : HasDifferential E 2 (9,134) (11,135)
        ((I'.interpretation.basis .sphere 9 134 0)) ((I'.interpretation.basis .sphere 11 135 3) + (I'.interpretation.basis .sphere 11 135 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 227) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h228 : HasDifferential E 2 (9,134) (11,135)
        ((I'.interpretation.basis .sphere 9 134 4)) ((I'.interpretation.basis .sphere 11 135 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 228) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h251 : HasDifferential E 2 (8,134) (10,135)
        ((I'.interpretation.basis .sphere 8 134 1)) ((I'.interpretation.basis .sphere 10 135 3)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 251) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (8,134) (10,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h252 : HasDifferential E 3 (10,135) (13,137)
        ((I'.interpretation.basis .sphere 10 135 0)) ((I'.interpretation.basis .sphere 13 137 0)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 252) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (10,135) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h253 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 1)) ((I'.interpretation.basis .sphere 12 136 1) + (I'.interpretation.basis .sphere 12 136 2)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 253) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h254 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 2)) ((I'.interpretation.basis .sphere 12 136 3) + (I'.interpretation.basis .sphere 12 136 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 254) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h255 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 4)) ((I'.interpretation.basis .sphere 12 136 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 255) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h174 : ReachesPage E 3 (6,132) (I'.interpretation.basis .sphere 6 132 0) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 174) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    have h224 : ReachesPage E 1000 (9,134) (I'.interpretation.basis .sphere 9 134 2) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 224) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    have h225 : ReachesPage E 7 (9,134) (I'.interpretation.basis .sphere 9 134 3) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 225) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 173) rfl)
    change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 9 134 i.val at he
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 191) rfl)
    change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 11 135 i.val at hf
    obtain ⟨g,hg⟩ := I'.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 182) rfl)
    change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 10 135 i.val at hg
    obtain ⟨k,hk⟩ := I'.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 200) rfl)
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
    change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 12 136 i.val at hk
    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 4 := he 4
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 4 := hf 4
    have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 0 := hg 0
    have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 1 := hg 1
    have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 2 := hg 2
    have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 3 := hg 3
    have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 4 := hg 4
    have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 0 := hk 0
    have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 1 := hk 1
    have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 2 := hk 2
    have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 3 := hk 3
    have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 4 := hk 4
    have dg0 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 0) = 0 := by
      obtain ⟨_,x,y,hx,hy,hd⟩ := h252
      obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
      rw [←hx2.eq_on_page_two] at hx2
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
        (by decide) hx2 ⟨_,hx⟩
    have dg3 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 3)=0 := by
      have hd : E.d 2 (8,134) (I'.interpretation.basis .sphere 8 134 1)=I'.interpretation.basis .sphere 10 135 3 := h251.eq_on_page_two.2
      exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hd⟩
    have dg1 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 1)=I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
    have dg2 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 2)=I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
    have dg4 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 4)=I'.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
    have incoming (x : E.Page 2 (10,135)) : k (E.d 2 (10,135) x) 0=0 := by
      have all (a : Fin 5 →₀ F2) : k (E.d 2 (10,135) (g.symm a)) 0=0 := by
        induction a using Finsupp.induction with
        | zero => simp
        | @single_add i c a hi hc ih =>
          rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
          fin_cases c
          · simp
          · change k (E.d 2 (10,135) (g.symm (Finsupp.single i 1))) 0=0
            rw [hg]
            fin_cases i
            all_goals dsimp only
            all_goals simp only [dg0,dg1,dg2,dg3,dg4,map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hk1,←hk2,←hk3,←hk4,LinearEquiv.apply_symm_apply]
            all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using all (g x)
    obtain ⟨_,b1,t,hb1,ht,hd1⟩ := h226
    have db1 : E.d 3 (9,134) b1=t := hd1
    have tn : t≠0 := by
      intro ht0
      obtain ⟨_,z,hz,hzt⟩ := ht
      have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hzt.trans ht0)
      change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
      change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z = I'.interpretation.basis .sphere 12 136 0 at hz
      rw [hz] at hh
      obtain ⟨u,hu⟩ := hh
      have hh := incoming u
      rw [hu,←hk0,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply] at hh
    obtain ⟨b2late,hb2late⟩ := h224
    obtain ⟨b3late,hb3late⟩ := h225
    obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) hb2late
    obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) hb3late
    have db2 : E.d 3 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb2 ⟨b2late,hb2late⟩
    have db3 : E.d 3 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb3 ⟨b3late,hb3late⟩
    have hrep2 {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
      rw [←hb.eq_on_page_two] at hb
      exact hb
    have d1 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 1)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb1) ⟨b1,hb1⟩
    have d2 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 2)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb2) ⟨b2,hb2⟩
    have d3 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 3)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb3) ⟨b3,hb3⟩
    have d0 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 0)=I'.interpretation.basis .sphere 11 135 3+I'.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
    have d4 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 4)=I'.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
    have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
        (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
        RepresentsOnPage E r p (x+y) (a+b) := by
      obtain ⟨hr,z,hz,ha⟩ := hx
      obtain ⟨_,w,hw,hb⟩ := hy
      exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
    have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
        (c : F2) (h : RepresentsOnPage E r p x a) :
        RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
      split
      · exact RepresentsOnPage.zero h.1
      · exact h
    have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
        f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
      ext i
      simp only [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · generalize f i=b
        fin_cases b <;> simp
      · intro j hj hji
        by_cases hf : f j=0
        · simp [hf]
        · simp [hf,hji]
      · simp
    have frame (y : E.Page 3 (9,134)) (hy : E.d 3 (9,134) y=0) : y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
      let A := E.ssData (9,134)
      haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance y
      let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
      have hx : RepresentsOnPage E 3 (9,134) x y := ⟨by decide,z,rfl,hz⟩
      have dx : E.d 2 (9,134) x=0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hx) ⟨y,hx⟩
      let c : Fin 5 → F2 := e x
      have hcoef := congrArg e.symm (f2_expand (e x))
      simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
      change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
      simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
      have hd := congrArg (E.d 2 (9,134)) hcoef
      rw [dx] at hd
      simp only [map_add,apply_ite,map_zero] at hd
      simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
      have c0 : c 0=0 := by
        by_contra h0
        simp only [h0,ite_false] at hd
        by_cases h4 : c 4=0
        all_goals simp only [h4,ite_true,ite_false] at hd
        all_goals have hh := congrArg (fun z => f z 3) hd
        all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
        all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      have c4 : c 4=0 := by
        by_contra h4
        simp only [c0,h4,ite_true,ite_false,zero_add] at hd
        have hh := congrArg (fun z => f z 4) hd
        simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
        norm_num [Finsupp.single_apply] at hh
      have hform : y=(if c 1=0 then 0 else b1)+((if c 2=0 then 0 else b2)+(if c 3=0 then 0 else b3)) := by
        apply represents_unique hx
        rw [hcoef]
        simp only [c0,c4,ite_true,zero_add,add_zero]
        exact hadd (hif (c 1) hb1) (hadd (hif (c 2) hb2) (hif (c 3) hb3))
      have c1 : c 1=0 := by
        by_contra h1
        have hh := congrArg (E.d 3 (9,134)) hform
        simp only [hy,map_add,apply_ite,map_zero,db1,db2,db3,h1,ite_false,ite_self,add_zero] at hh
        exact tn hh.symm
      simp only [c1,ite_true,zero_add] at hform
      by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
      · exact Or.inl (by simpa only [h2,h3,ite_true,zero_add] using hform)
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,zero_add] using hform)))
      · exact Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,add_zero] using hform))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [h2,h3,ite_false,add_comm] using hform)))
    have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (I'.interpretation.basis .sphere 6 132 0) (0) := by
      have hh := I'.adamsStatements ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 659) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,y,hy,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 []=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hh
      exact hh
    have n660 : ¬ HasDifferential E 3 (6,132) (9,134) (I'.interpretation.basis .sphere 6 132 0) (I'.interpretation.basis .sphere 9 134 2) := by
      have hh := I'.adamsStatements ⟨.sphere,.refutation,3,6,132,[0],9,134,[2],"proofs.db/log",2047478⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 660) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,y,hy,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hh
      exact hh
    obtain ⟨xr,hxr⟩ := h174
    let yr : E.Page 3 (9,134) := E.d 3 (6,132) xr
    have hd : E.d 3 (6,132) xr=yr := rfl
    have hyn : yr≠0 := by
      intro hz
      apply n659
      refine ⟨rfl,xr,0,hxr,RepresentsOnPage.zero (by decide),?_⟩
      change E.d 3 (6,132) xr=0
      exact hd.trans hz
    have hdy : E.d 3 (9,134) yr=0 :=
      IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(6,132)) ⟨xr,hd⟩
    rcases frame yr hdy with h|h|h|h
    · exact (hyn h).elim
    · apply (n660 ?_).elim
      refine ⟨rfl,xr,yr,hxr,?_,?_⟩
      · rw [h]; exact hb2
      · exact hd
    · left
      refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
      rw [h]; exact hb3
    · right
      refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
      rw [h]; exact hadd hb3 hb2
  have main_h6b_third_kernel_frame {D' : AdamsComparison H M' Syn} (I':AdamsComputationTheorems D' L' G) :
      ∃ b2 b3:(sequence D' .sphere).Page 3 (9,134),
        RepresentsOnPage (sequence D' .sphere) 3 (9,134) (I'.interpretation.basis .sphere 9 134 2) b2 ∧
        RepresentsOnPage (sequence D' .sphere) 3 (9,134) (I'.interpretation.basis .sphere 9 134 3) b3 ∧
        ∀y:(sequence D' .sphere).Page 3 (9,134), (sequence D' .sphere).d 3 (9,134) y=0 →
          y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
    let E := sequence D' .sphere
    have h226 : HasDifferential E 3 (9,134) (12,136)
        ((I'.interpretation.basis .sphere 9 134 1)) ((I'.interpretation.basis .sphere 12 136 0)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 226) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (9,134) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h227 : HasDifferential E 2 (9,134) (11,135)
        ((I'.interpretation.basis .sphere 9 134 0)) ((I'.interpretation.basis .sphere 11 135 3) + (I'.interpretation.basis .sphere 11 135 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 227) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h228 : HasDifferential E 2 (9,134) (11,135)
        ((I'.interpretation.basis .sphere 9 134 4)) ((I'.interpretation.basis .sphere 11 135 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 228) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h251 : HasDifferential E 2 (8,134) (10,135)
        ((I'.interpretation.basis .sphere 8 134 1)) ((I'.interpretation.basis .sphere 10 135 3)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 251) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (8,134) (10,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h252 : HasDifferential E 3 (10,135) (13,137)
        ((I'.interpretation.basis .sphere 10 135 0)) ((I'.interpretation.basis .sphere 13 137 0)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 252) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (10,135) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h253 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 1)) ((I'.interpretation.basis .sphere 12 136 1) + (I'.interpretation.basis .sphere 12 136 2)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 253) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h254 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 2)) ((I'.interpretation.basis .sphere 12 136 3) + (I'.interpretation.basis .sphere 12 136 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 254) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h255 : HasDifferential E 2 (10,135) (12,136)
        ((I'.interpretation.basis .sphere 10 135 4)) ((I'.interpretation.basis .sphere 12 136 4)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 255) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h174 : ReachesPage E 3 (6,132) (I'.interpretation.basis .sphere 6 132 0) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 174) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    have h224 : ReachesPage E 1000 (9,134) (I'.interpretation.basis .sphere 9 134 2) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 224) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    have h225 : ReachesPage E 7 (9,134) (I'.interpretation.basis .sphere 9 134 3) := by
      have hh := I'.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 225) rfl)
      dsimp only [AdamsStatement] at hh
      obtain ⟨x,hx,hh⟩ := hh
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hh
      exact hh
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 173) rfl)
    change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 9 134 i.val at he
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 191) rfl)
    change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 11 135 i.val at hf
    obtain ⟨g,hg⟩ := I'.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 182) rfl)
    change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 10 135 i.val at hg
    obtain ⟨k,hk⟩ := I'.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 200) rfl)
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
    change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 12 136 i.val at hk
    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 4 := he 4
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 4 := hf 4
    have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 0 := hg 0
    have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 1 := hg 1
    have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 2 := hg 2
    have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 3 := hg 3
    have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 4 := hg 4
    have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 0 := hk 0
    have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 1 := hk 1
    have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 2 := hk 2
    have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 3 := hk 3
    have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 4 := hk 4
    have dg0 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 0) = 0 := by
      obtain ⟨_,x,y,hx,hy,hd⟩ := h252
      obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
      rw [←hx2.eq_on_page_two] at hx2
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
        (by decide) hx2 ⟨_,hx⟩
    have dg3 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 3)=0 := by
      have hd : E.d 2 (8,134) (I'.interpretation.basis .sphere 8 134 1)=I'.interpretation.basis .sphere 10 135 3 := h251.eq_on_page_two.2
      exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hd⟩
    have dg1 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 1)=I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
    have dg2 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 2)=I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
    have dg4 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 4)=I'.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
    have incoming (x : E.Page 2 (10,135)) : k (E.d 2 (10,135) x) 0=0 := by
      have all (a : Fin 5 →₀ F2) : k (E.d 2 (10,135) (g.symm a)) 0=0 := by
        induction a using Finsupp.induction with
        | zero => simp
        | @single_add i c a hi hc ih =>
          rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
          fin_cases c
          · simp
          · change k (E.d 2 (10,135) (g.symm (Finsupp.single i 1))) 0=0
            rw [hg]
            fin_cases i
            all_goals dsimp only
            all_goals simp only [dg0,dg1,dg2,dg3,dg4,map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hk1,←hk2,←hk3,←hk4,LinearEquiv.apply_symm_apply]
            all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using all (g x)
    obtain ⟨_,b1,t,hb1,ht,hd1⟩ := h226
    have db1 : E.d 3 (9,134) b1=t := hd1
    have tn : t≠0 := by
      intro ht0
      obtain ⟨_,z,hz,hzt⟩ := ht
      have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hzt.trans ht0)
      change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
      change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z = I'.interpretation.basis .sphere 12 136 0 at hz
      rw [hz] at hh
      obtain ⟨u,hu⟩ := hh
      have hh := incoming u
      rw [hu,←hk0,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply] at hh
    obtain ⟨b2late,hb2late⟩ := h224
    obtain ⟨b3late,hb3late⟩ := h225
    obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) hb2late
    obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) hb3late
    have db2 : E.d 3 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb2 ⟨b2late,hb2late⟩
    have db3 : E.d 3 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb3 ⟨b3late,hb3late⟩
    have hrep2 {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
      rw [←hb.eq_on_page_two] at hb
      exact hb
    have d1 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 1)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb1) ⟨b1,hb1⟩
    have d2 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 2)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb2) ⟨b2,hb2⟩
    have d3 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 3)=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb3) ⟨b3,hb3⟩
    have d0 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 0)=I'.interpretation.basis .sphere 11 135 3+I'.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
    have d4 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 4)=I'.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
    have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
        (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
        RepresentsOnPage E r p (x+y) (a+b) := by
      obtain ⟨hr,z,hz,ha⟩ := hx
      obtain ⟨_,w,hw,hb⟩ := hy
      exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
    have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
        (c : F2) (h : RepresentsOnPage E r p x a) :
        RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
      split
      · exact RepresentsOnPage.zero h.1
      · exact h
    have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
        f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
      ext i
      simp only [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · generalize f i=b
        fin_cases b <;> simp
      · intro j hj hji
        by_cases hf : f j=0
        · simp [hf]
        · simp [hf,hji]
      · simp
    have frame (y : E.Page 3 (9,134)) (hy : E.d 3 (9,134) y=0) : y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
      let A := E.ssData (9,134)
      haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance y
      let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
      have hx : RepresentsOnPage E 3 (9,134) x y := ⟨by decide,z,rfl,hz⟩
      have dx : E.d 2 (9,134) x=0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hx) ⟨y,hx⟩
      let c : Fin 5 → F2 := e x
      have hcoef := congrArg e.symm (f2_expand (e x))
      simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
      change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
      simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
      have hd := congrArg (E.d 2 (9,134)) hcoef
      rw [dx] at hd
      simp only [map_add,apply_ite,map_zero] at hd
      simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
      have c0 : c 0=0 := by
        by_contra h0
        simp only [h0,ite_false] at hd
        by_cases h4 : c 4=0
        all_goals simp only [h4,ite_true,ite_false] at hd
        all_goals have hh := congrArg (fun z => f z 3) hd
        all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
        all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      have c4 : c 4=0 := by
        by_contra h4
        simp only [c0,h4,ite_true,ite_false,zero_add] at hd
        have hh := congrArg (fun z => f z 4) hd
        simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
        norm_num [Finsupp.single_apply] at hh
      have hform : y=(if c 1=0 then 0 else b1)+((if c 2=0 then 0 else b2)+(if c 3=0 then 0 else b3)) := by
        apply represents_unique hx
        rw [hcoef]
        simp only [c0,c4,ite_true,zero_add,add_zero]
        exact hadd (hif (c 1) hb1) (hadd (hif (c 2) hb2) (hif (c 3) hb3))
      have c1 : c 1=0 := by
        by_contra h1
        have hh := congrArg (E.d 3 (9,134)) hform
        simp only [hy,map_add,apply_ite,map_zero,db1,db2,db3,h1,ite_false,ite_self,add_zero] at hh
        exact tn hh.symm
      simp only [c1,ite_true,zero_add] at hform
      by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
      · exact Or.inl (by simpa only [h2,h3,ite_true,zero_add] using hform)
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,zero_add] using hform)))
      · exact Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,add_zero] using hform))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [h2,h3,ite_false,add_comm] using hform)))
    exact ⟨b2,b3,hb2,hb3,frame⟩
  have main_h6b_finite_cosets {D' : AdamsComparison H M' Syn} (I':AdamsComputationTheorems D' L' G)
      (x:Page D' .sphere 9 134) (hx:x∈cycles H SphereSpectrum 7 (9,134)) :
      x∈boundaries H SphereSpectrum 3 (9,134) ∨
      x-I'.interpretation.basis .sphere 9 134 2∈boundaries H SphereSpectrum 3 (9,134) := by
    let E:=sequence D' .sphere
    let B:=boundaries H SphereSpectrum 3 (9,134)
    let u:Page D' .sphere 9 134:=I'.interpretation.basis .sphere 9 134 2
    let v:Page D' .sphere 9 134:=I'.interpretation.basis .sphere 9 134 3
    have hu:u+u=0 := by
      obtain ⟨e,he⟩:=I'.basis ⟨.sphere,9,134,["391,1","390,1","69,1,82,1","18,1,190,1","0,1,375,1"]⟩ (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 173) rfl)
      change E.Page 2 (9,134)≃ₗ[ℤ](Fin 5→₀F2) at e
      apply e.injective
      ext i
      simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply]
      generalize e u i=a
      fin_cases a <;> decide
    have hnu:-u=u := by
      exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using hu)
    have hv:v∈B ∨ v-u∈B := by
      rcases candidates_raw I' with h|h
      · left
        exact boundary_of_zero_representative (H:=H) (r:=4) (p:=(9,134))
          (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h.toHasDifferential)
      · right
        have hb:v+u∈B := boundary_of_zero_representative (H:=H) (r:=4) (p:=(9,134))
          (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h.toHasDifferential)
        simpa only [sub_eq_add_neg,hnu] using hb
    obtain ⟨b2,b3,hb2,hb3,frame⟩:=main_h6b_third_kernel_frame I'
    obtain ⟨a8,ha8⟩:ReachesPage E 8 (9,134) x:=
      (isCycle_iff_represents H SphereSpectrum 8 (by decide) (9,134) x).mp ⟨by decide,hx⟩
    obtain ⟨a3,ha3⟩:=represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤8) ha8
    have hd:E.d 3 (9,134) a3=0:=represents_d_zero_of_later
      (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a8,ha8⟩
    have hdiff {y:E.Page 2 (9,134)} {a:E.Page 3 (9,134)}
        (hxa:RepresentsOnPage E 3 (9,134) x a)
        (hya:RepresentsOnPage E 3 (9,134) y a) : x-y∈B := by
      have hh:RepresentsOnPage E 3 (9,134) (x-y) 0 := by
        obtain ⟨hr,z,hz,hza⟩:=hxa
        obtain ⟨_,w,hw,hwa⟩:=hya
        refine ⟨hr,z-w,by rw [map_sub,hz,hw],?_⟩
        rw [map_sub,hza,hwa,sub_self]
      exact boundaries_monotone H SphereSpectrum (9,134) (by decide : (2:ℤ)≤3)
        (boundary_of_zero_representative (H:=H) (r:=3) (p:=(9,134)) hh)
    rcases frame a3 hd with h|h|h|h
    · left
      rw [h] at ha3
      exact boundaries_monotone H SphereSpectrum (9,134) (by decide : (2:ℤ)≤3)
        (boundary_of_zero_representative (H:=H) (r:=3) (p:=(9,134)) ha3)
    · right
      rw [h] at ha3
      exact hdiff ha3 hb2
    · rw [h] at ha3
      have hh:=hdiff ha3 hb3
      change x-v∈B at hh
      rcases hv with hv|hv
      · left
        have he:(x-v)+v=x:=sub_add_cancel x v
        simpa only [he] using B.add_mem hh hv
      · right
        have he:(x-v)+(v-u)=x-u:=by abel
        simpa only [he] using B.add_mem hh hv
    · rw [h] at ha3
      have hb:RepresentsOnPage E 3 (9,134) (v+u) (b3+b2) := by
        obtain ⟨hr,z,hz,hza⟩:=hb3
        obtain ⟨_,w,hw,hwa⟩:=hb2
        exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,hza,hwa]⟩
      have hh:=hdiff ha3 hb
      rcases hv with hv|hv
      · right
        have he:(x-(v+u))+v=x-u:=by abel
        simpa only [he] using B.add_mem hh hv
      · left
        have he:(x-(v+u))+(v-u)=x := by
          calc
            _=x-(u+u) := by abel
            _=x := by rw [hu,sub_zero]
        simpa only [he] using B.add_mem hh hv
  have nu_af10_frame {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      ∃ a : (sequence D' .sphere).Page 3 (10,135),
      ∃ b : (sequence D' .sphere).Page 3 (13,137),
        RepresentsOnPage (sequence D' .sphere) 3 (10,135) (I'.interpretation.basis .sphere 10 135 0) a ∧
        RepresentsOnPage (sequence D' .sphere) 3 (13,137) (I'.interpretation.basis .sphere 13 137 0) b ∧
        (sequence D' .sphere).d 3 (10,135) a=b ∧
        ∀ z : (sequence D' .sphere).Page 3 (10,135), z=0 ∨ z=a := by
    let E := sequence D' .sphere
    have h251 : HasDifferential E 2 (8,134) (10,135)
        (I'.interpretation.basis .sphere 8 134 1) (I'.interpretation.basis .sphere 10 135 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 251) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (8,134) (10,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h252 : HasDifferential E 3 (10,135) (13,137)
        (I'.interpretation.basis .sphere 10 135 0) (I'.interpretation.basis .sphere 13 137 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 252) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (10,135) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h253 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 1) (I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 253) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h254 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 2) (I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 254) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h255 : HasDifferential E 2 (10,135) (12,136)
        (I'.interpretation.basis .sphere 10 135 4) (I'.interpretation.basis .sphere 12 136 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 255) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,135) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 182) rfl)
    change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
    change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 10 135 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 3 := he 3
    have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 10 135 4 := he 4
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 200) rfl)
    change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 12 136 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 12 136 4 := hf 4
    obtain ⟨_,a0,b0,ha0,hb0,hd⟩ := h252
    have hd' : E.d 3 (10,135) a0=b0 := hd
    have hz3 : RepresentsOnPage E 3 (10,135) (I'.interpretation.basis .sphere 10 135 3) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h251
    have dz {p : ℤ×ℤ} {x : E.Page 2 p} (hx : ReachesPage E 3 p x) : E.d 2 p x=0 := by
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
      rw [←hb.eq_on_page_two] at hb
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨a,ha⟩
    have hd0 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 0)=0 := dz ⟨a0,ha0⟩
    have hd1 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 1)=
        I'.interpretation.basis .sphere 12 136 1 + I'.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
    have hd2 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 2)=
        I'.interpretation.basis .sphere 12 136 3 + I'.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
    have hd3 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 3)=0 := dz ⟨0,hz3⟩
    have hd4 : E.d 2 (10,135) (I'.interpretation.basis .sphere 10 135 4)=
        I'.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
    have frame (a : E.Page 3 (10,135)) : a=0 ∨ a=a0 := by
      let A := E.ssData (10,135)
      haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance a
      let x : E.Page 2 (10,135) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤1)) ≫ A.pageπ 0) z
      have hxa : RepresentsOnPage E 3 (10,135) x a := ⟨by decide,z,rfl,hza⟩
      have hc : E.d 2 (10,135) x=0 := dz ⟨a,hxa⟩
      have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
        apply Finsupp.ext
        intro i
        fin_cases i <;> simp
      have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
        rw [←heq,LinearEquiv.symm_apply_apply]
      generalize hc0 : e x 0=c0 at hxe
      generalize hc1 : e x 1=c1 at hxe
      generalize hc2 : e x 2=c2 at hxe
      generalize hc3 : e x 3=c3 at hxe
      generalize hc4 : e x 4=c4 at hxe
      fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
        rw [hxe] at hc hxa
        exact Or.inl (represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤3)))
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he4] at hc hxa
        simp only [hd4] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he3] at hc hxa
        exact Or.inl (represents_unique hxa hz3)
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he3, he4] at hc hxa
        simp only [map_add,hd3,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2] at hc hxa
        simp only [hd2] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he4] at hc hxa
        simp only [map_add,hd2,hd4] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he3] at hc hxa
        simp only [map_add,hd2,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he2, he3, he4] at hc hxa
        simp only [map_add,hd2,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1] at hc hxa
        simp only [hd1] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he4] at hc hxa
        simp only [map_add,hd1,hd4] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he3] at hc hxa
        simp only [map_add,hd1,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he3, he4] at hc hxa
        simp only [map_add,hd1,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2] at hc hxa
        simp only [map_add,hd1,hd2] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he4] at hc hxa
        simp only [map_add,hd1,hd2,hd4] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he3] at hc hxa
        simp only [map_add,hd1,hd2,hd3,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
        rw [hxe] at hc hxa
        simp only [he1, he2, he3, he4] at hc hxa
        simp only [map_add,hd1,hd2,hd3,hd4,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0] at hc hxa
        exact Or.inr (represents_unique hxa ha0)
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he4] at hc hxa
        simp only [map_add,hd0,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he3] at hc hxa
        exact Or.inr (by simpa only [add_zero] using represents_unique hxa (represents_add_tail ha0 hz3))
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he3, he4] at hc hxa
        simp only [map_add,hd0,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 4) hc
        simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2] at hc hxa
        simp only [map_add,hd0,hd2,zero_add] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he4] at hc hxa
        simp only [map_add,hd0,hd2,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he3] at hc hxa
        simp only [map_add,hd0,hd2,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he2, he3, he4] at hc hxa
        simp only [map_add,hd0,hd2,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 3) hc
        simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1] at hc hxa
        simp only [map_add,hd0,hd1,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he3] at hc hxa
        simp only [map_add,hd0,hd1,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he3, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2] at hc hxa
        simp only [map_add,hd0,hd1,hd2,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd4,zero_add] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he3] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
      · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
        try simp only [map_add] at hxe
        rw [hxe] at hc hxa
        simp only [he0, he1, he2, he3, he4] at hc hxa
        simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
        have hh := congrArg (fun y=>f y 1) hc
        simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    exact ⟨a0,b0,ha0,hb0,hd',frame⟩
  have nu_af10_d3_target_nonzero {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G)
      {a : (sequence D' .sphere).Page 3 (13,137)}
      (ha : RepresentsOnPage (sequence D' .sphere) 3 (13,137)
        (I'.interpretation.basis .sphere 13 137 0) a) : a≠0 := by
    let E := sequence D' .sphere
    have h279 : HasDifferential E 3 (8,134) (11,136)
        (I'.interpretation.basis .sphere 8 134 3) (I'.interpretation.basis .sphere 11 136 1) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 279) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,134) (11,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h280 : HasDifferential E 3 (8,134) (11,136)
        (I'.interpretation.basis .sphere 8 134 2) (I'.interpretation.basis .sphere 11 136 2) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 280) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,134) (11,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h282 : HasDifferential E 4 (11,136) (15,139)
        (I'.interpretation.basis .sphere 11 136 0) (I'.interpretation.basis .sphere 15 139 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 282) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 4 (11,136) (15,139) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h283 : HasDifferential E 2 (11,136) (13,137)
        (I'.interpretation.basis .sphere 11 136 4) (I'.interpretation.basis .sphere 13 137 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 283) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (11,136) (13,137) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h281 : ReachesPage E 5 (11,136) (I'.interpretation.basis .sphere 11 136 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 281) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 5 (11,136) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 208) rfl)
    change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 13 137 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 2 := he 2
    have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I'.interpretation.basis .sphere 13 137 3 := he 3
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 192) rfl)
    change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 11 136 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 11 136 4 := hf 4
    let ell (x : E.Page 2 (13,137)) : F2 := e x 0
    have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
        (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
        RepresentsOnPage E r p (x-y) (a-b) := by
      obtain ⟨hr,z,hz,ha⟩ := hx
      obtain ⟨_,w,hw,hb⟩ := hy
      exact ⟨hr,z-w,by rw [map_sub,hz,hw],by rw [map_sub,ha,hb]⟩
    have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
        (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
      rw [←hb.eq_on_page_two] at hb
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
    have hd0 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 0)=0 := by
      obtain ⟨_,a,b,ha,_,_⟩ := h282
      exact dz (by decide) ⟨a,ha⟩
    have hd1 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 1)=0 := by
      obtain ⟨_,a,b,_,hb,_⟩ := h279
      exact dz (by decide) ⟨b,hb⟩
    have hd2 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 2)=0 := by
      obtain ⟨_,a,b,_,hb,_⟩ := h280
      exact dz (by decide) ⟨b,hb⟩
    have hd3 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 3)=0 := dz (by decide) h281
    have hd4 : E.d 2 (11,136) (I'.interpretation.basis .sphere 11 136 4)=I'.interpretation.basis .sphere 13 137 3 := h283.eq_on_page_two.2
    have incoming_zero (x : E.Page 2 (11,136)) : ell (E.d 2 (11,136) x)=0 := by
      have hall (a : Fin 5 →₀ F2) : ell (E.d 2 (11,136) (f.symm a))=0 := by
        dsimp only [ell]
        induction a using Finsupp.induction with
        | zero => simp
        | @single_add i c a hi hci ih =>
          rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
          fin_cases c
          · simp
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single i 1))) 0=0
            fin_cases i
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 0 1))) 0=0
              simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 1 1))) 0=0
              simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 2 1))) 0=0
              simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 3 1))) 0=0
              simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
            · change e (E.d 2 (11,136) (f.symm (Finsupp.single 4 1))) 0=0
              rw [hf4,hd4,←he3,LinearEquiv.apply_symm_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
    have nz3 {x : E.Page 2 (13,137)} (hx : ell x=1) {a : E.Page 3 (13,137)}
        (ha : RepresentsOnPage E 3 (13,137) x a) : a≠0 := by
      intro ha0
      obtain ⟨_,z,hz2,hz3⟩ := ha
      obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,136) z).mp (hz3.trans ha0)
      change E.d 2 (11,136) u = (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z at hu
      change (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z=x at hz2
      have hh := incoming_zero u
      rw [hu,hz2,hx] at hh
      exact one_ne_zero hh
    apply nz3 (x:=I'.interpretation.basis .sphere 13 137 0) ?_ ha
    dsimp only [ell]
    rw [←he0,LinearEquiv.apply_symm_apply]
    simp
  have nu_af10_cycles_boundary {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      cycles H SphereSpectrum 4 (10,135) ≤ boundaries H SphereSpectrum 2 (10,135) := by
    intro x hx
    obtain ⟨a4,ha4⟩ := (isCycle_iff_represents H SphereSpectrum 5 (by decide) (10,135) x).mp
      ⟨by decide, by simpa using hx⟩
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha4
    have hd : (sequence D' .sphere).d 3 (10,135) a3=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a4,ha4⟩
    obtain ⟨a,b,ha,hb,hab,frame⟩ := nu_af10_frame I'
    have haz : a3=0 := by
      rcases frame a3 with h|h
      · exact h
      · exact (nu_af10_d3_target_nonzero I' hb (hab.symm.trans (by simpa only [h] using hd))).elim
    rw [haz] at ha3
    exact boundary_of_zero_representative (H:=H) (r:=3) (p:=(10,135)) ha3
  have finite_sphere_zero_of_classical_quotient {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q : ℕ) (hq : 0<q) (s t w : ℤ)
      (hw : 0≤t-w ∧ t-w<q)
      (hc : Subsingleton (CycleQuotient H SphereSpectrum ((q:ℤ)-t+w) (1+t-w) (s,t))) :
      IsZero (((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,w)).eInfty) := by
    let e := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) w hw
    haveI := hc
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom q)).eInftyMap (s,t,w)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv q)).eInftyMap (s,t,w)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have main_af8_cycles_boundary {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      cycles H SphereSpectrum 8 (8,133) ≤ boundaries H SphereSpectrum 2 (8,133) := by
    let E := sequence D' .sphere
    have h200 : HasDifferential E 3 (8,133) (11,135)
        (I'.interpretation.basis .sphere 8 133 0) (I'.interpretation.basis .sphere 11 135 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,133,[0],11,135,[0],"S0_AdamsE2_ss",2629⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 200) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,133) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h201 : HasDifferential E 2 (8,133) (10,134)
        (I'.interpretation.basis .sphere 8 133 1) (I'.interpretation.basis .sphere 10 134 2 + I'.interpretation.basis .sphere 10 134 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 201) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (8,133) (10,134) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h226 : HasDifferential E 3 (9,134) (12,136)
        (I'.interpretation.basis .sphere 9 134 1) (I'.interpretation.basis .sphere 12 136 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 226) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (9,134) (12,136) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h227 : HasDifferential E 2 (9,134) (11,135)
        (I'.interpretation.basis .sphere 9 134 0) (I'.interpretation.basis .sphere 11 135 3 + I'.interpretation.basis .sphere 11 135 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 227) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h228 : HasDifferential E 2 (9,134) (11,135)
        (I'.interpretation.basis .sphere 9 134 4) (I'.interpretation.basis .sphere 11 135 4) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 228) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (9,134) (11,135) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    have h224 : ReachesPage E 1000 (9,134) (I'.interpretation.basis .sphere 9 134 2) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 224) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 1000 (9,134) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    have h225 : ReachesPage E 7 (9,134) (I'.interpretation.basis .sphere 9 134 3) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 225) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 7 (9,134) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 161) rfl)
    change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 8 133 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I'.interpretation.basis .sphere 8 133 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I'.interpretation.basis .sphere 8 133 1 := he 1
    obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 173) rfl)
    change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 9 134 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 9 134 4 := hf 4
    obtain ⟨g,hg⟩ := I'.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 191) rfl)
    change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
    change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 11 135 i.val at hg
    have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 0 := hg 0
    have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 1 := hg 1
    have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 2 := hg 2
    have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 3 := hg 3
    have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 11 135 4 := hg 4
    obtain ⟨k,hk⟩ := I'.basis ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 181) rfl)
    change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
    change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 10 134 i.val at hk
    have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 10 134 0 := hk 0
    have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 10 134 1 := hk 1
    have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 10 134 2 := hk 2
    have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 10 134 3 := hk 3
    have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 10 134 4 := hk 4
    have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
        (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
      rw [←hb.eq_on_page_two] at hb
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
    have hd0 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 0) =
        I'.interpretation.basis .sphere 11 135 3 + I'.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
    have hd1 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 1) = 0 := by
      obtain ⟨_,x,y,hx,_,_⟩ := h226
      exact dz (by decide) ⟨x,hx⟩
    have hd2 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 2) = 0 := dz (by decide) h224
    have hd3 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 3) = 0 := dz (by decide) h225
    have hd4 : E.d 2 (9,134) (I'.interpretation.basis .sphere 9 134 4) =
        I'.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
    have incoming_zero (x : E.Page 2 (9,134)) : g (E.d 2 (9,134) x) 0=0 := by
      have hall (a : Fin 5 →₀ F2) : g (E.d 2 (9,134) (f.symm a)) 0=0 := by
        induction a using Finsupp.induction with
        | zero => simp
        | @single_add i c a hi hci ih =>
          rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
          fin_cases c
          · simp
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single i 1))) 0=0
            fin_cases i
            · change g (E.d 2 (9,134) (f.symm (Finsupp.single 0 1))) 0=0
              simp only [hf0,hd0,map_add,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
            · change g (E.d 2 (9,134) (f.symm (Finsupp.single 1 1))) 0=0
              simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
            · change g (E.d 2 (9,134) (f.symm (Finsupp.single 2 1))) 0=0
              simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
            · change g (E.d 2 (9,134) (f.symm (Finsupp.single 3 1))) 0=0
              simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
            · change g (E.d 2 (9,134) (f.symm (Finsupp.single 4 1))) 0=0
              simp only [hf4,hd4,←hg4,LinearEquiv.apply_symm_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
    obtain ⟨_,a,b,ha,hb,hd⟩ := h200
    have hd' : E.d 3 (8,133) a=b := hd
    have hbne : b≠0 := by
      intro hb0
      obtain ⟨_,z,hx,hz⟩ := hb
      have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,134) z).mp (hz.trans hb0)
      change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
        (E.ssData (11,135)).pageπ 0) z ∈ LinearMap.range (E.d 2 (9,134)).hom at hh
      change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
        (E.ssData (11,135)).pageπ 0) z=I'.interpretation.basis .sphere 11 135 0 at hx
      rw [hx] at hh
      obtain ⟨u,hu⟩ := hh
      have hzero := incoming_zero u
      rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
      norm_num [Finsupp.single_apply] at hzero
    have hn : E.d 2 (8,133) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
      rw [he1]
      have hh : E.d 2 (8,133) (I'.interpretation.basis .sphere 8 133 1) =
        I'.interpretation.basis .sphere 10 134 2 + I'.interpretation.basis .sphere 10 134 4 := h201.eq_on_page_two.2
      rw [hh]
      intro hz
      have hz' := congrArg (fun x=>k x 2) hz
      simp only [map_add,map_zero,←hk2,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hz'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hz'
    have frame : ∀ q : E.Page 3 (8,133), q=0 ∨ q=a :=
      frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
    have ker (q : E.Page 3 (8,133)) (hq : E.d 3 (8,133) q=0) : q=0 := by
      rcases frame q with hh|hh
      · exact hh
      · exact (hbne (by simpa only [hh,hd'] using hq)).elim
    intro x hx
    obtain ⟨a9,ha9⟩ := (isCycle_iff_represents H SphereSpectrum 9 (by decide) (8,133) x).mp
      ⟨by decide, by simpa using hx⟩
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤9) ha9
    have hd3 : E.d 3 (8,133) a3=0 :=
      represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a9,ha9⟩
    rw [ker a3 hd3] at ha3
    exact boundary_of_zero_representative (H:=H) (r:=3) (p:=(8,133)) ha3
  have main_af10_cycles_boundary {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      cycles H SphereSpectrum 6 (10,135) ≤ boundaries H SphereSpectrum 4 (10,135) := by
    exact (cycles_antitone H SphereSpectrum (10,135) (by decide : (4:ℤ)≤6)).trans
      ((nu_af10_cycles_boundary I').trans
        (boundaries_monotone H SphereSpectrum (10,135) (by decide : (2:ℤ)≤4)))
  have main_low_even_quotient_zero {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) (s:ℤ) (hs:s=8 ∨ s=10) :
      Subsingleton (CycleQuotient H SphereSpectrum (16-s) (s-6) (s,125+s)) := by
    have hc:cycles H SphereSpectrum (16-s) (s,125+s) ≤ boundaries H SphereSpectrum (s-6) (s,125+s) := by
      rcases hs with rfl|rfl
      · exact main_af8_cycles_boundary I'
      · exact main_af10_cycles_boundary I'
    have hz (x : CycleQuotient H SphereSpectrum (16-s) (s-6) (s,125+s)) : x=0 := by
      obtain ⟨x⟩:=x
      exact (NestedQuotient.projection_eq_zero x).mpr (hc x.property)
    exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
  have main_low_even_filtration_gap {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) (BHS:EInftyComparison D')
      (s:ℤ) (hs:s=8 ∨ s=10)
      (a:BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (s+1) a := by
    apply (D'.quotientConvergence 9 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      s (s+1) 125 132 (by omega)
    intro j hj hj'
    have : j=s := by omega
    subst j
    exact finite_sphere_zero_of_classical_quotient BHS 9 (by decide) s (125+s) 132
      (by rcases hs with rfl|rfl <;> norm_num)
      (by convert main_low_even_quotient_zero I' s hs using 1; congr 1 <;> omega)
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
  have finite_detection_peel {D' : AdamsComparison H M' Syn}
      (q : ℕ) (hq : 0<q) (i : Tridegree)
      (x : (D'.family.quotient (S_0_0 : Syn) q).E₂ i)
      (hframe : ∀ e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData i).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 i x e)
      (c : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
      (hc : Detects (D'.quotientConvergence q hq) i x c)
      (a : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a) :
      ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (i.1+1)
        (a-(if b then c else 0)) := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) q)
    have ham : a ∈ (ModuleCat.subobjectModule
        (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (i.2.1-i.1,i.2.2)))
        (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let gr := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
    let e := ((D'.quotientConvergence q hq).identification i).inv gr
    have he : ((D'.quotientConvergence q hq).identification i).hom e=gr :=
      ConcreteCategory.congr_hom ((D'.quotientConvergence q hq).identification i).inv_hom_id gr
    rcases hframe e with he0|hex
    · refine ⟨false,?_⟩
      simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
      have hzero : Detects (D'.quotientConvergence q hq) i 0 a := by
        refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,a',ha',?_⟩
        rw [he0] at he
        exact he
      exact detects_zero_filtration (D'.quotientConvergence q hq) i hzero
    · refine ⟨true,?_⟩
      simp only [↓reduceIte]
      have hax : Detects (D'.quotientConvergence q hq) i x a := ⟨e,hex,a',ha',he⟩
      exact detects_sub_filtration (D'.quotientConvergence q hq) i hax hc
  have finite_sphere_infty_frame_of_cosets {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (y0 : E2 H SphereSpectrum s t)
      (hframe : ∀ x : E2 H SphereSpectrum s t,
        x∈cycles H SphereSpectrum ((q:ℤ)-k) (s,t) →
        x∈boundaries H SphereSpectrum (k+1) (s,t) ∨
        x-y0∈boundaries H SphereSpectrum (k+1) (s,t))
      (e : ((D'.family.quotient (S_0_0:Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
      e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0:Syn) q) 2 (s,t,t-k)
        (D'.quotientLabel q s t k y0) e := by
    by_cases hne:e=0
    · exact Or.inl hne
    right
    let P:=BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let f:=XModLambdaN.map D'.nu.unitIso.hom q
    let g:=XModLambdaN.map D'.nu.unitIso.inv q
    have hgf:g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq:(D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k)≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    obtain ⟨c,hc⟩:=Quotient.exists_rep (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e))
    have hn:¬c.val∈boundaries H SphereSpectrum (k+1) (s,t) := by
      intro hb
      have hz:NestedQuotient.projection _ (boundaries H SphereSpectrum (1+t-(t-k)) (s,t)) c=0:= by
        apply (NestedQuotient.projection_eq_zero c).mpr
        convert hb using 1; congr 1; omega
      have hzP:P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=0:=hc.symm.trans hz
      have hzE:(D'.family.functor.map g).eInftyMap (s,t,t-k) e=0:=P.injective (hzP.trans (map_zero P).symm)
      apply hne
      rw [←heq,hzE,map_zero]
    have hcq : c.val∈cycles H SphereSpectrum ((q:ℤ)-k) (s,t) := by
      convert c.property using 1; congr 1; omega
    have hb:= (hframe c.val hcq).resolve_left hn
    have hY:y0∈cycles H SphereSpectrum ((q:ℤ)-k) (s,t) := by
      have hh:=(cycles H SphereSpectrum ((q:ℤ)-k) (s,t)).sub_mem hcq
        (boundaries_le_cycles H SphereSpectrum (s,t) (k+1) ((q:ℤ)-k) hb)
      simpa only [sub_sub_cancel] using hh
    let y:cycles H SphereSpectrum (q-t+(t-k)) (s,t):=⟨y0,by
      convert hY using 1; congr 1; omega⟩
    have hcy:NestedQuotient.projection _ _ c=NestedQuotient.projection
        (cycles H SphereSpectrum (q-t+(t-k)) (s,t))
        (boundaries H SphereSpectrum (1+t-(t-k)) (s,t)) y := by
      apply sub_eq_zero.mp
      rw [←map_sub]
      apply (NestedQuotient.projection_eq_zero (c-y)).mpr
      convert hb using 1 <;> congr 1; omega
    have hy:HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k y0)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e) := by
      apply (BHS.labels.1 .sphere q hq (s,t) k hkq y _).mpr
      exact hc.symm.trans hcy
    have hl:familyPageMap D'.family f 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k y0)=D'.quotientLabel q s t k y0 := by
      rw [←sphere_quotient_label_to_nu (D':=D') q k s t y0]
      calc
        _=familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k y0) :=
          ConcreteCategory.congr_hom (family_page_comp (D':=D') g f 2 (s,t,t-k)) _
        _=D'.quotientLabel q s t k y0 := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0:Syn) q)).ssData (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have hh:=family_infinity_representative_map f (s,t,t-k) _ _ hy
    rw [hl,heq] at hh
    exact hh
  have finite_sphere_peel_of_cosets {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (y0 : E2 H SphereSpectrum s t)
      (hframe : ∀ x : E2 H SphereSpectrum s t,
        x∈cycles H SphereSpectrum ((q:ℤ)-k) (s,t) →
        x∈boundaries H SphereSpectrum (k+1) (s,t) ∨
        x-y0∈boundaries H SphereSpectrum (k+1) (s,t))
      (c : BiHom (t-s) (t-k) (XModLambdaN (S_0_0:Syn) q))
      (hc : Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k y0) c)
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0:Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a) :
      ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (s+1)
        (a-(if b then c else 0)) := by
    exact finite_detection_peel q hq (s,t,t-k) (D'.quotientLabel q s t k y0)
      (finite_sphere_infty_frame_of_cosets BHS q k hq hkq s t y0 hframe) c hc a ha
  have finite_sphere_outside_window_zero {D' : AdamsComparison H M' Syn} (BHS:EInftyComparison D')
      (q:ℕ) (hq:0<q) (s t w:ℤ) (hw:¬(0≤t-w ∧ t-w<q)) :
      IsZero (((D'.family.quotient (S_0_0:Syn) q).sequence.ssData (s,t,w)).eInfty) := by
    let P:=BHS.presentation.finite SphereSpectrum q hq (s,t) w
    haveI : Subsingleton (finiteEInftyModel H SphereSpectrum q (s,t) w) := by
      dsimp only [finiteEInftyModel]
      rw [if_neg hw]
      infer_instance
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty) :=
      P.injective.subsingleton
    let hn:=ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum q).sequence.ssData (s,t,w)).eInfty)
    let f:=(D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom q)).eInftyMap (s,t,w)
    let g:=(D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv q)).eInftyMap (s,t,w)
    have hfg:g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have finite_sphere_filtration_floor {D' : AdamsComparison H M' Syn} (BHS:EInftyComparison D')
      (q:ℕ) (hq:0<q) (m w:ℤ) (N:ℕ) (hN:m+N≤w)
      (a:BiHom m w (XModLambdaN (S_0_0:Syn) q)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N a := by
    have hfloor:FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 0 a := by
      refine ⟨a,?_⟩
      change a≫adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 0 _=a
      rw [adamsTowerMap_self]
      exact Category.comp_id _
    apply ((D'.quotientConvergence q hq).filtrationAtLeast_iff_of_eInfty_isZero 0 N m w
      (by omega) ?_ a).mp hfloor
    intro j hj hj'
    exact finite_sphere_outside_window_zero BHS q hq j (m+j) w (by omega)
  have ha7 := finite_sphere_filtration_floor BHS 9 (by decide) 125 132 7 (by decide) a
  obtain ⟨c7,hc7,ht7,hd7⟩ := main_af7_torsion_representative I' R
  have frame7 : ∀ x : E2 H SphereSpectrum 7 132,
      x∈cycles H SphereSpectrum ((9:ℤ)-0) (7,132) →
      x∈boundaries H SphereSpectrum (0+1) (7,132) ∨
      x-(show E2 H SphereSpectrum 7 132 from I'.interpretation.basis .sphere 7 132 0)∈boundaries H SphereSpectrum (0+1) (7,132) := by
    intro x hx
    rcases main_af7_all_labels I' x with h|h
    · left; rw [h]; exact Submodule.zero_mem _
    · right; rw [h,sub_self]; exact Submodule.zero_mem _
  obtain ⟨b7,hb7⟩ := finite_sphere_peel_of_cosets BHS 9 0 (by decide) (by decide)
    7 132 (I'.interpretation.basis .sphere 7 132 0) frame7 (quotientClass 9 c7) hd7 a ha7
  let a9 := a-(if b7 then quotientClass 9 c7 else 0)
  have ha9 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a9 :=
    (main_low_even_filtration_gap I' BHS 8 (Or.inl rfl) a9).mp hb7
  obtain ⟨b9,hb9⟩ := finite_sphere_peel_of_cosets BHS 9 2 (by decide) (by decide)
    9 134 (I'.interpretation.basis .sphere 9 134 2) (main_h6b_finite_cosets I') c9 hc9 a9 ha9
  refine ⟨a9-(if b9 then c9 else 0),
    (main_low_even_filtration_gap I' BHS 10 (Or.inr rfl) _).mp hb9,?_⟩
  have hz7 : Phi (quotientClass 9 c7)=0 := hPhi7 c7 ht7
  dsimp only [a9]
  cases b7 <;> cases b9 <;>
    simp only [Bool.false_eq_true,↓reduceIte,map_sub,hz7,hPhi9,sub_zero]

set_option maxHeartbeats 3000000 in
private theorem theta_b_eta_fifth_mod_nine_zero_from_choice
    (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I'.interpretation.sphere 13 137 correction))
    (etaAux : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M' D'.toAdamsComparisonData etaAux)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M' D'.toAdamsComparisonData theta)
    (b : BiHom 62 70 (S_0_0 : Syn))
    (hb : SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b) :
    quotientClass 9 (lambdaMultiply 5 (sphereProduct etaAux (sphereProduct theta b))) = 0 := by
  have no_outgoing_stem125_low (I' : AdamsComputationTheorems D' L' G)
      (q : ℤ) (hq : q ≤ 4) : NoOutgoingAt (sequence D' .sphere) q (q+125) := by
    set_option maxRecDepth 10000 in
      intro r hr x
      have hz : Subsingleton ((sequence D' .sphere).Page r (q,q+125)) := by
        by_cases hneg : q < 0
        · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+125) hneg
        · have hq0 : 0 ≤ q := by omega
          have hd : (⟨.sphere, q.toNat, (q+125).toNat, []⟩ : Raw.Degree) ∈ Raw.degrees := by
            interval_cases q <;> simp [Raw.degrees]
          obtain ⟨e, _⟩ := I'.basis _ hd
          change Page D' .sphere q.toNat (q+125).toNat ≃ₗ[ℤ]
            (Fin 0 →₀ KIP126.Algebra.F2) at e
          have he : Subsingleton (Page D' .sphere q.toNat (q+125).toNat) :=
            e.injective.subsingleton
          apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+125) (by omega) hr
          simpa only [Computation.SphereAndCofiber.Page, Computation.SphereAndCofiber.sequence, Computation.SphereAndCofiber.object, ClassicalObject.obj, Int.toNat_of_nonneg hq0, Int.toNat_of_nonneg (by omega : 0 ≤ q+125),
            Int.toNat_of_nonneg] using he
      rw [hz.elim x 0, map_zero]

  have theta_quotient_frame
      (I' : AdamsComputationTheorems D' L' G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
      (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
      ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
        ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
          q=0 ∨ q=NestedQuotient.projection _ _ x' := by
    let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
    let P := E.ssData (s,t)
    have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
      have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
        intro r hr
        change E.d r (s-r,t-(r-1))=0
        rw [show t-(r-1)=(s-r)+125 by omega]
        ext z
        exact no_outgoing_stem125_low I' (s-r) (by omega) r (by omega) z
      have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
      change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
      simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
    obtain ⟨z,hz,_,hall⟩ := hx
    change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
    let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
    refine ⟨x',rfl,?_⟩
    have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
        (hzero : P.pageπ ⊤ z'=0) :
        PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
          PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
      obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
      have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
      change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
        (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
      rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
      refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
      rw [←hb]
      change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
        (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
      congr 1
      dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
    rintro ⟨y⟩
    obtain ⟨z',hz'⟩ := y.property
    rcases hall (P.pageπ ⊤ z') with h0|h1
    · left
      apply (NestedQuotient.projection_eq_zero y).mpr
      rw [←hz']
      exact zero_of_infinity_zero z' h0
    · right
      apply sub_eq_zero.mp
      change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
      rw [←map_sub]
      apply (NestedQuotient.projection_eq_zero (y-x')).mpr
      change y.val-x ∈ _
      rw [←hz',←hz,←map_sub]
      exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])

  /- BHS label agreement and the actual nu-unit map transport common infinity
  representatives to the synthetic sphere, including the zero case. -/
  have theta_sphere_frame
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D')
      (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
      (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
      ∀ e : ((D'.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
        e=0 ∨ HasInfinityRepresentative D'.family.sphere 2 (s,t,t-k) (D'.sphereE2 s t k x) e := by
    have family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
        familyPageMap D'.family f 2 i = (D'.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
      let F := (D'.family.functor.map f).toSSDataMorphism
      let PX := (D'.family.functor.obj X).ssData i
      let PY := (D'.family.functor.obj Y).ssData i
      let nX : WithTop ℕ := ↑(2-(D'.family.functor.obj X).r₀).toNat
      let nY : WithTop ℕ := ↑(2-(D'.family.functor.obj Y).r₀).toNat
      change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
        (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
        @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
      have hX : nX=0 := by dsimp only [nX]; rw [D'.family.firstPage X]; rfl
      have hY : nY=0 := by dsimp only [nY]; rw [D'.family.firstPage Y]; rfl
      have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
          (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
          (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
          eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
        subst n
        subst m
        simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
      exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _
    have map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
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
    obtain ⟨x',hx',hframe⟩ := theta_quotient_frame I' s t k hst hsk x hx
    intro e
    let i : Tridegree := (s,t,t-k)
    let f := (D'.family.functor.map D'.nu.unitIso.hom).eInftyMap i
    let g := (D'.family.functor.map D'.nu.unitIso.inv).eInftyMap i
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
    let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
    have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
    have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
      have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
          q=0 ∨ q=NestedQuotient.projection _ _ x' := by
        rw [heqcut]
        exact hframe
      exact hh (nuE (g e))
    rcases hfq with h0|h1
    · left
      have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
      rw [←hback,hg0,map_zero]
    · right
      have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
      have hh := map_infinity D'.nu.unitIso.hom i _ _ hr
      have hlabel : familyPageMap D'.family D'.nu.unitIso.hom 2 i
          (targetNuLabel D' .sphere s t k x'.val) = D'.sphereE2 s t k x := by
        rw [hx']
        dsimp only [targetNuLabel]
        rw [family_map_data,family_map_data]
        dsimp only [i] at *
        change ((D'.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
          (D'.family.functor.map D'.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
        rw [←SSDataMorphism.pageMap_comp]
        have hp := D'.comparisonCompatible.sphere_nu s t k x
        rw [family_map_data] at hp
        have hm : ((D'.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
            (D'.family.functor.map D'.nu.unitIso.hom).toSSDataMorphism) =
            (D'.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D'.nu.functor.obj SphereSpectrum) ≫ D'.nu.unitIso.hom)).toSSDataMorphism := by
          change (D'.family.functor.map _ ≫ D'.family.functor.map _).toSSDataMorphism = _
          rw [←CategoryTheory.Functor.map_comp]
        rw [hm]
        exact hp
      change HasInfinityRepresentative D'.family.sphere 2 i _ (f (g e)) at hh
      rw [hback,hlabel] at hh
      exact hh

  /- Actual convergence gives either nonzero leading detection or membership
  in the next actual tower filtration. -/
  have theta_detection_step
      (i : Tridegree) (x : (D'.family.sphere).E₂ i)
      (hframe : ∀ e : ((D'.family.sphere).sequence.ssData i).eInfty,
        e=0 ∨ HasInfinityRepresentative D'.family.sphere 2 i x e)
      (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a) :
      DetectsNonzero D'.sphereConvergence i x a ∨
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (i.1+1) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
        (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
    let e := (D'.sphereConvergence.identification i).inv q
    have he : (D'.sphereConvergence.identification i).hom e=q :=
      ConcreteCategory.congr_hom (D'.sphereConvergence.identification i).inv_hom_id q
    by_cases he0 : e=0
    · right
      have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
        rw [he0,map_zero] at he
        exact he.symm
      have hmem := (subobject_cokernel_π_eq_zero_iff
        (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
        (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
      rw [ha'] at hmem
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
    · left
      have hr := (hframe e).resolve_left he0
      exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
  /- The two complete frames and the intervening finite-page gap yield the
  three branches, retaining an actual lambda preimage in the last branch. -/
  have stem124_weight129_filtration11_branches
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D')
      (x13 : E2 H SphereSpectrum 13 137)
      (h13 : ClassicalInfinityGenerated 13 137 x13)
      (h11 : Subsingleton ((Computation.SphereAndCofiber.sequence D' .sphere).Page 5 (11,135)))
      (h12 : Subsingleton ((Computation.SphereAndCofiber.sequence D' .sphere).Page 4 (12,136)))
      (a : BiHom 124 129 (S_0_0 : Syn))
      (ha11 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a) :
      SphereDetected D' 13 137 8 x13 a ∨
        ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 9 b=a := by
    have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
        (hpage : Subsingleton ((sequence D' .sphere).Page 6 (s, t))) :
        Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
      set_option backward.isDefEq.respectTransparency false in
        let E := (sequence D' .sphere).ssData (s, t)
        haveI : Subsingleton (E.page 4) := hpage
        have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
            PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
          rintro x ⟨z, hz⟩
          let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
          have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
          obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
            (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
          refine ⟨y, ?_⟩
          change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
          have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
              PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
              PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
            dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.SphereAndCofiber.sequence, object]
            rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
          rw [← hfactor, CategoryTheory.comp_apply]
          apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
          exact (congrArg (fun f => f z)
            (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
        have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
          rintro ⟨x⟩
          change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
          apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
          exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
        exact ⟨fun x y => (hall x).trans (hall y).symm⟩

    have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a →
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 a := by
      apply (D'.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
        11 13 124 129 (by omega) ?_ a).mp
      intro j hj hj'
      have hpage : Subsingleton ((Computation.SphereAndCofiber.sequence D' .sphere).Page 6 (j,124+j)) := by
        interval_cases j
        · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
            (by omega) (by omega) h11
        · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
            (by omega) (by omega) h12
      haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
          (1+(124+j)-129) (j,124+j)) :=
        permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
      let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 129 (by omega)
      haveI : Subsingleton (((D'.family.nu D'.nu SphereSpectrum).sequence.ssData (j,124+j,129)).eInfty) := e.injective.subsingleton
      let hnu := ModuleCat.isZero_of_subsingleton
        (((D'.family.nu D'.nu SphereSpectrum).sequence.ssData (j,124+j,129)).eInfty)
      let f := (D'.family.functor.map D'.nu.unitIso.hom).eInftyMap (j,124+j,129)
      let g := (D'.family.functor.map D'.nu.unitIso.inv).eInftyMap (j,124+j,129)
      have hfg : g ≫ f = 𝟙 _ := by
        dsimp only [f,g]
        rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
          CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
      exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
    have ha13 := hgap ha11
    have hf13 := theta_sphere_frame I' BHS 13 137 8 (by omega) (by omega) x13 h13
    rcases theta_detection_step (13,137,129) (D'.sphereE2 13 137 8 x13) hf13 a ha13 with hdet|ha14
    · exact Or.inl hdet
    right
    have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
        (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s x) :
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s (x ≫ f) := by
      obtain ⟨z,hz⟩ := hx
      refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat,?_⟩
      change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat) ≫
        adamsTowerMap (nuCoefficientUnit H.unit D'.nu) Y 0 s.toNat _ = x ≫ f
      change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) X 0 s.toNat _ = x at hz
      rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
      rfl
    have h := BHS.filtration_lambda .sphere 124 129 14 (by omega) (a ≫ D'.nu.unitIso.inv)
    change FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14 (a ≫ D'.nu.unitIso.inv) ↔
      ∃ b : BiHom 124 138 (D'.nu.functor.obj SphereSpectrum), lambdaMultiply 9 b=a ≫ D'.nu.unitIso.inv at h
    obtain ⟨b,hb⟩ := h.mp (hmap D'.nu.unitIso.inv a ha14)
    refine ⟨b ≫ D'.nu.unitIso.hom,?_⟩
    simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D'.nu.unitIso.hom) hb

  have eta_weight129_branches_filtration_fifteen
      (I' : AdamsComputationTheorems D' L' G) (SF : Derived.SphereFacts I'.interpretation)
      (etaAux : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M' D'.toAdamsComparisonData etaAux)
      (b : BiHom 124 129 (S_0_0 : Syn))
      (hbranch : SphereDetected D' 13 137 8 (I'.interpretation.sphere 13 137 correction)
          b ∨
        ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 9 a=b) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 (sphereProduct etaAux b) := by
    have hη0 : lambdaMultiply 0 etaAux=etaAux := by
      have hc := D'.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
        change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ etaAux=etaAux
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hηd := D'.comparisonCompatible.homotopy_lambda 1 2 0 etaAux
    rw [hη0,hη] at hηd
    rcases hbranch with h13 | ⟨a,ha⟩
    · have hp : Sphere.Internal.product H M' (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M' 1) (I'.interpretation.sphere 13 137 correction)=0 := by
        have h := I'.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
        dsimp only at h
        rw [I'.distinguishedClasses.h1] at h
        exact h.symm.trans SF.h1_correction_zero
      have hd := D'.multiplicationCompatible 1 2 13 137 0 8
        (Sphere.Internal.hi H M' 1) (I'.interpretation.sphere 13 137 correction)
        etaAux b hηd h13.1
      change Detects D'.sphereConvergence (14,139,131)
        (D'.sphereE2 14 139 8 (Sphere.Internal.product H M' (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M' 1) (I'.interpretation.sphere 13 137 correction)))
        (sphereProduct etaAux b) at hd
      rw [hp,map_zero] at hd
      exact detects_zero_filtration D'.sphereConvergence (14,139,131) hd
    · have had := D'.comparisonCompatible.homotopy_lambda 14 138 9 a
      rw [ha] at had
      have hd := D'.multiplicationCompatible 1 2 14 138 0 9
        (Sphere.Internal.hi H M' 1) (D'.sphereFirstQuotient 14 138 (quotientClass 1 a))
        etaAux b hηd had
      change Detects D'.sphereConvergence (15,140,131) _ (sphereProduct etaAux b) at hd
      obtain ⟨e,he,a',ha',hgr⟩ := hd
      rw [←ha']
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 15 (125,131)).arrow a'∈
          (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,131)))
            ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 15 (125,131)) := ⟨a',rfl⟩
      simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

  have eta_weight129_filtration_eleven
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
      (h13 : ClassicalInfinityGenerated 13 137 (I'.interpretation.sphere 13 137 correction))
      (etaAux : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M' D'.toAdamsComparisonData etaAux)
      (a : BiHom 124 129 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 (sphereProduct etaAux a) := by
    exact eta_weight129_branches_filtration_fifteen I' SF etaAux hη a
      (stem124_weight129_filtration11_branches I' BHS _ h13
        SF.e5_stem124_af11 SF.e4_stem124_af12 a ha)
  have sphere_quotient_high_filtration_zero (BHS : EInftyComparison D')
      (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
      (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
      (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) N z) : z=0 := by
    let O : SyntheticObject := .quotient q .sphere
    have hsep : ∀ z : BiHom m w (O.obj D'.nu D'.hopfAndDetector),
        (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) j z) → z=0 :=
      D'.homotopySeparated O m w
    refine (D'.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
    intro j hj
    let i : Tridegree := (j,m+j,w)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
    have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
    haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
      dsimp only [PageRepresentatives.finiteEInftyModel]
      rw [if_neg hh]
      infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro e
    have he : (D'.family.functor.map g).eInftyMap i e=0 :=
      P.injective (Subsingleton.elim _ _)
    have h := congrArg (fun a=>(D'.family.functor.map f).eInftyMap i a) he
    change ((D'.family.functor.map g).eInftyMap i ≫ (D'.family.functor.map f).eInftyMap i) e=_ at h
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
    simpa only [ConcreteCategory.id_apply,map_zero] using h

  have eta_weight129_mod_nine_zero
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
      (h13 : ClassicalInfinityGenerated 13 137 (I'.interpretation.sphere 13 137 correction))
      (etaAux : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M' D'.toAdamsComparisonData etaAux)
      (a : BiHom 124 129 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a) :
      quotientClass 9 (sphereProduct etaAux a) = 0 := by
    have hf := eta_weight129_filtration_eleven I' BHS SF h13 etaAux hη a ha
    have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
        (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s x) :
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s (x ≫ f) := by
      obtain ⟨z,hz⟩ := hx
      refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat,?_⟩
      change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat) ≫
        adamsTowerMap (nuCoefficientUnit H.unit D'.nu) Y 0 s.toNat _ = x ≫ f
      change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) X 0 s.toNat _ = x at hz
      rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
      rfl
    exact sphere_quotient_high_filtration_zero BHS.eInfty 9 (by decide) 125 131 15
      (by decide) _ (hmap (XModLambdaN.incl (S_0_0 : Syn) 9) _ hf)
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

  have main_eta_right_five (D' : AdamsComparison H M' Syn)
      (etaAux : BiHom 1 2 (S_0_0 : Syn))
      {X : Syn} (c : BiHom 124 134 X) :
      sphereAction etaAux (lambdaMultiply 5 c) = lambdaMultiply 5 (sphereAction etaAux c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (1,2) (124,134) (0,-5)
      (125,136) (124,129) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
      Int.reduceSub, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 5
      ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 5
      ((SyntheticCategory.biShift (124,134)).map etaAux))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-5)).inv.naturality etaAux)]
    rfl

  have lambda_filtration_preserved {A : Syn} {m w : ℤ}
      (k : ℕ) (s : ℤ) (a : BiHom m w A)
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s (lambdaMultiply k a) := by
    obtain ⟨z,hz⟩ := ha
    refine ⟨lambdaMultiply k z,?_⟩
    change lambdaMultiply k z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 s.toNat _ = _
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 s.toNat _ = a at hz
    dsimp only [lambdaMultiply]
    simp only [Category.assoc,hz]

  have theta_b_eta_fifth_mod_nine_zero
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
      (h13 : ClassicalInfinityGenerated 13 137 (I'.interpretation.sphere 13 137 correction))
      (etaAux : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M' D'.toAdamsComparisonData etaAux)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (htheta : Detects D'.sphereConvergence (2,64,64)
        (D'.sphereE2 2 64 0 (Sphere.Internal.hiSquare H M' 5)) theta)
      (b : BiHom 62 70 (S_0_0 : Syn))
      (hb : SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b) :
      quotientClass 9 (lambdaMultiply 5 (sphereProduct etaAux (sphereProduct theta b))) = 0 := by
    have hp := I'.products ⟨2,64,8,70⟩ (by simp [Raw.products]) h5Sq B
    dsimp only at hp
    rw [I'.distinguishedClasses.h5_square] at hp
    have hz : Sphere.Internal.product H M' (s:=2) (t:=64) (s':=8) (t':=70)
        (Sphere.Internal.hiSquare H M' 5) (I'.interpretation.sphere 8 70 B)=0 :=
      hp.symm.trans SF.h5Sq_B_zero
    have hd := D'.multiplicationCompatible 2 64 8 70 0 0
      (Sphere.Internal.hiSquare H M' 5) (I'.interpretation.sphere 8 70 B) theta b htheta hb.1
    change Detects D'.sphereConvergence (10,134,134)
      (D'.sphereE2 10 134 0 (Sphere.Internal.product H M' (s:=2) (t:=64) (s':=8) (t':=70)
        (Sphere.Internal.hiSquare H M' 5) (I'.interpretation.sphere 8 70 B)))
      (sphereProduct theta b) at hd
    rw [hz,map_zero] at hd
    have hf : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 (sphereProduct theta b) :=
      detects_zero_filtration D'.sphereConvergence (10,134,134) hd
    have hf5 := lambda_filtration_preserved 5 11 (sphereProduct theta b) hf
    have hv := eta_weight129_mod_nine_zero I' BHS SF h13 etaAux hη (lambdaMultiply 5 (sphereProduct theta b)) hf5
    change quotientClass 9 (sphereAction etaAux (lambdaMultiply 5 (sphereProduct theta b)))=0 at hv
    rw [main_eta_right_five D'] at hv
    exact hv
  have htheta0 : lambdaMultiply 0 theta=theta := by
    have hc := D'.shiftCoherence.right_unit (62,64) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 62 64 : Syn) := by
      change (biShiftAddIso (62,64) (0,0) (62,64) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn) ≫ theta=theta
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hthetad := D'.comparisonCompatible.homotopy_lambda 2 64 0 theta
  rw [htheta0,htheta] at hthetad
  exact theta_b_eta_fifth_mod_nine_zero I' BHS SF h13 etaAux hη theta hthetad b hb

set_option maxHeartbeats 3000000 in
private theorem exists_filtration_eleven_representative
    (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (R : RealizationDetectionData D')
    (SF : Derived.SphereFacts I'.interpretation)
    (h13 : ClassicalInfinityGenerated 13 137 (I'.interpretation.sphere 13 137 correction))
    (eta : BiHom 1 2 (S_0_0:Syn)) (heta : EtaChoice M' D'.toAdamsComparisonData eta)
    (h0 : BiHom 0 1 (S_0_0:Syn))
    (theta : BiHom 62 64 (S_0_0:Syn)) (htheta : ThetaChoice M' D'.toAdamsComparisonData theta)
    (b : BiHom 62 70 (S_0_0:Syn))
    (hb : SphereDetected D' 8 70 0 (I'.interpretation.sphere 8 70 B) b)
    (zTheta : BiHom 125 134 (S_0_0:Syn))
    (hzTheta : SphereDetected D' 9 134 0
      (I'.interpretation.sphere 9 134 (mulAt dataH6 B)) zTheta)
    (hshuffle : lambdaMultiply 2 (sphereProduct h0 zTheta)=
      lambdaMultiply 3 (sphereProduct eta (sphereProduct theta b)))
    (z : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
    (hzn : lambdaMultiply 2 (sphereAction h0 z)≠0) :
    ∃ y : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 y ∧
      lambdaMultiply 2 (sphereAction h0 y)≠0 := by
  classical
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
  have main_h0_right_two_132 (D' : AdamsComparison H M' Syn)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      {X : Syn} (c : BiHom 125 132 X) :
      sphereAction h0 (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction h0 c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (0,1) (125,132) (0,-2)
      (125,133) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
      Int.reduceSub, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 2
      ((SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 2
      ((SyntheticCategory.biShift (125,132)).map h0))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,132) (0,-2)).inv.naturality h0)]
    rfl
  have main_h0_right_two_134 (D' : AdamsComparison H M' Syn)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      {X : Syn} (c : BiHom 125 134 X) :
      sphereAction h0 (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction h0 c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (0,1) (125,134) (0,-2)
      (125,135) (125,132) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
      Int.reduceSub, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 2
      ((SyntheticCategory.biShift_comp (0,1) (125,134)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 2
      ((SyntheticCategory.biShift (125,134)).map h0))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,134) (0,-2)).inv.naturality h0)]
    rfl
  have main_lambda_two_three_136 (D' : AdamsComparison H M' Syn)
      {X : Syn} (c : BiHom 125 136 X) :
      lambdaMultiply 2 (lambdaMultiply 3 c) = lambdaMultiply 5 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,136) (0,-3) (0,-2)
      (125,133) (0,-5) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
    erw [← reassoc_of% (lambdaPow_naturality 2
      ((SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 2 (lambdaPow 3 (Smn 125 136)))]
    erw [← Category.assoc, ha]
    erw [lambdaPow_add D'.shiftCoherence 3 2 5 (by decide) (Smn 125 136)]
    simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.assoc]
    rfl
  have main_af7_correction_killed
      (D' : AdamsComparison H M' Syn) (h0 : BiHom 0 1 (S_0_0:Syn))
      (c : BiHom 125 132 (S_0_0:Syn)) (hc : lambdaMultiply 2 c=0) :
      lambdaMultiply 2 (sphereAction h0 (quotientClass 9 c))=0 := by
    have hh := main_h0_right_two_132 D' h0 c
    rw [hc] at hh
    have hz : lambdaMultiply 2 (sphereAction h0 c)=0 := by
      exact hh.symm.trans (by simp only [sphereAction,Limits.comp_zero])
    simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc,Limits.zero_comp] using
      congrArg (fun a => a≫XModLambdaN.incl (S_0_0:Syn) 9) hz
  have main_af9_correction_killed
      (D' : AdamsComparison H M' Syn) (h0 : BiHom 0 1 (S_0_0:Syn))
      (z : BiHom 125 134 (S_0_0:Syn))
      (p : BiHom 125 136 (S_0_0:Syn))
      (hz : lambdaMultiply 2 (sphereAction h0 z)=lambdaMultiply 3 p)
      (hp : quotientClass 9 (lambdaMultiply 5 p)=0) :
      lambdaMultiply 2 (sphereAction h0 (quotientClass 9 (lambdaMultiply 2 z)))=0 := by
    have hh : lambdaMultiply 2 (sphereAction h0 (lambdaMultiply 2 z))=lambdaMultiply 5 p := by
      rw [main_h0_right_two_134 D',hz,main_lambda_two_three_136 D']
    have hq := congrArg (fun a => a≫XModLambdaN.incl (S_0_0:Syn) 9) hh
    change _=quotientClass 9 (lambdaMultiply 5 p) at hq
    rw [hp] at hq
    simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc] using hq
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
  have detected_map {D' : AdamsComparison H M' Syn}
      (X Y : SyntheticObject) (f : X.obj D'.nu D'.hopfAndDetector ⟶ Y.obj D'.nu D'.hopfAndDetector)
      (i : Tridegree) (x : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (ha : Detects (D'.convergence X) i x a) :
      Detects (D'.convergence Y) i (familyPageMap D'.family f 2 i x) (a≫f) := by
    obtain ⟨c,hca,hce⟩ := D'.comparisonCompatible.convergence_natural X Y f
    obtain ⟨e,he,a',ha',hgr⟩ := ha
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (X.obj D'.nu D'.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D'.nu) (Y.obj D'.nu D'.hopfAndDetector)
    let m := (i.2.1-i.1,i.2.2)
    let k := (c.filtration_compat i.1 m).choose
    have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
      have hh := (c.filtration_compat i.1 m).choose_spec
      change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
      rw [hca] at hh
      exact hh
    have hc : c.eMap i ≫ ((D'.convergence Y).identification i).hom =
        ((D'.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
      have hh := c.iso_compat i
      simpa only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
    have hq : F.toAssociatedGraded i.1 m ≫
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
        k≫G.toAssociatedGraded i.1 m := by
      exact cokernel.π_desc _ _ _
    refine ⟨(D'.family.functor.map f).eInftyMap i e,family_infinity_representative_map f i x e he,k a',?_,?_⟩
    · have hh := ConcreteCategory.congr_hom hk a'
      change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
      change (F.F i.1 m).arrow a'=a at ha'
      rw [ha'] at hh
      exact hh
    · have hh := ConcreteCategory.congr_hom hc e
      rw [hce] at hh
      change ((D'.convergence Y).identification i).hom ((D'.family.functor.map f).eInftyMap i e)=_
      calc
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (((D'.convergence X).identification i).hom e) := hh
        _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
            (F.toAssociatedGraded i.1 m a') := by rw [hgr]
        _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'
  have detects_infinity_equal {D' : AdamsComparison H M' Syn}
      (X : SyntheticObject) (i : Tridegree)
      (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D'.nu D'.hopfAndDetector))
      (x y : (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)).E₂ i)
      (ha : Detects (D'.convergence X) i x a)
      (hb : Detects (D'.convergence X) i y a) :
      ∃ e, HasInfinityRepresentative (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)) 2 i x e ∧
        HasInfinityRepresentative (D'.family.obj (X.obj D'.nu D'.hopfAndDetector)) 2 i y e := by
    obtain ⟨e,he,a',ha',hga⟩ := ha
    obtain ⟨f,hf,b',hb',hgb⟩ := hb
    have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
    have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
    exact ⟨e,he,hef.symm ▸ hf⟩
  have main_h6b_zero_weight_label {D' : AdamsComparison H M' Syn}
      (BHS : EInftyComparison D') (x : E2 H SphereSpectrum 9 134)
      (a : BiHom (134-9) (134-0) (S_0_0 : Syn))
      (ha : Detects D'.sphereConvergence (9,134,134-0) (D'.sphereE2 9 134 0 x) a) :
      D'.sphereFirstQuotient 9 134 (quotientClass 1 a)=x := by
    let y := D'.sphereFirstQuotient 9 134 (quotientClass 1 a)
    have hd := detected_map (D':=D') .sphere (.quotient 1 .sphere)
      (XModLambdaN.incl (S_0_0 : Syn) 1) (9,134,134-0) _ a ha
    have hd' := D'.comparisonCompatible.first_quotient 9 134 y
    have hy : (D'.sphereFirstQuotient 9 134).symm y=quotientClass 1 a := by
      exact (D'.sphereFirstQuotient 9 134).symm_apply_apply _
    rw [hy] at hd'
    obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (9,134,134-0)
      (quotientClass 1 a) _ _ hd hd'
    change HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) 1) 2 (9,134,134-0)
      (D'.quotientLabel 1 9 134 0 x) e at he
    change HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) 1) 2 (9,134,134-0)
      (D'.quotientLabel 1 9 134 0 y) e at hf
    let g := XModLambdaN.map D'.nu.unitIso.inv 1
    have he' := family_infinity_representative_map g (9,134,134-0) _ _ he
    have hf' := family_infinity_representative_map g (9,134,134-0) _ _ hf
    have hlx := sphere_quotient_label_to_nu (D':=D') 1 0 9 134 x
    have hly := sphere_quotient_label_to_nu (D':=D') 1 0 9 134 y
    change familyPageMap D'.family g 2 (9,134,134-0) (D'.quotientLabel 1 9 134 0 x)=_ at hlx
    change familyPageMap D'.family g 2 (9,134,134-0) (D'.quotientLabel 1 9 134 0 y)=_ at hly
    rw [hlx] at he'
    rw [hly] at hf'
    let xx : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (9,134) :=
      ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
    let yy : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (9,134) :=
      ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
    have hxq := (BHS.labels.1 .sphere 1 (by decide) (9,134) 0 (by decide) xx _).mp he'
    have hyq := (BHS.labels.1 .sphere 1 (by decide) (9,134) 0 (by decide) yy _).mp hf'
    have heq := hxq.symm.trans hyq
    change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (9,134)) xx =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (9,134)) yy at heq
    have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (9,134)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
    have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
    change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (9,134) at hm
    have ht : 1+134-(134-0)=1 := by omega
    change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (9,134) at hm
    rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
    exact (sub_eq_zero.mp hm).symm
  have h6b_label {D' : AdamsComparison H M' Syn} (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 9 134 (mulAt dataH6 B) = I'.interpretation.basis .sphere 9 134 2 := by
    have hc := I'.monomials (⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 173) rfl) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
    have heq : (mulAt dataH6 B)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ * generator ⟨82,by decide⟩ = projection (monomialOfString "69,1,82,1")
      have hs : "69,1,82,1" ≠ "" := by decide
      have hp : (("69,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1, 82, 1] := by
        have split : "69,1,82,1".splitOn "," = ["69", "1", "82", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have main_af9_correction_detected {D' : AdamsComparison H M' Syn}
      (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (z : BiHom 125 134 (S_0_0:Syn))
      (hz : SphereDetected D' 9 134 0 (I'.interpretation.sphere 9 134 (mulAt dataH6 B)) z) :
      Detects (D'.quotientConvergence 9 (by decide)) (9,134,132)
        (D'.quotientLabel 9 9 134 2 (I'.interpretation.basis .sphere 9 134 2))
        (quotientClass 9 (lambdaMultiply 2 z)) := by
    have hfirst := main_h6b_zero_weight_label BHS _ z hz.1
    have hl := D'.comparisonCompatible.homotopy_lambda 9 134 2 z
    rw [hfirst,h6b_label I'] at hl
    exact detected_map (D':=D') .sphere (.quotient 9 .sphere)
      (XModLambdaN.incl (S_0_0:Syn) 9) (9,134,132) _ (lambdaMultiply 2 z) hl
  have main_strip_preserving_nonzero {D' : AdamsComparison H M' Syn}
      (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') (R : RealizationDetectionData D')
      (h0 : BiHom 0 1 (S_0_0:Syn))
      (zTheta : BiHom 125 134 (S_0_0:Syn))
      (hzTheta : SphereDetected D' 9 134 0
        (I'.interpretation.sphere 9 134 (mulAt dataH6 B)) zTheta)
      (p : BiHom 125 136 (S_0_0:Syn))
      (hshuffle : lambdaMultiply 2 (sphereAction h0 zTheta)=lambdaMultiply 3 p)
      (hp : quotientClass 9 (lambdaMultiply 5 p)=0)
      (z : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9))
      (hzn : lambdaMultiply 2 (sphereAction h0 z)≠0) :
      ∃ y : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9),
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 y ∧
        lambdaMultiply 2 (sphereAction h0 y)≠0 := by
    let Phi : BiHom 125 132 (XModLambdaN (S_0_0:Syn) 9) →+
        BiHom 125 131 (XModLambdaN (S_0_0:Syn) 9) := {
      toFun := fun a => lambdaMultiply 2 (sphereAction h0 a)
      map_zero' := by simp only [sphereAction,lambdaMultiply,Limits.comp_zero]
      map_add' := by intro a b; simp only [sphereAction,lambdaMultiply,Preadditive.comp_add] }
    have hc9 := main_af9_correction_detected I' BHS zTheta hzTheta
    have hkill9 : Phi (quotientClass 9 (lambdaMultiply 2 zTheta))=0 :=
      main_af9_correction_killed D' h0 zTheta p hshuffle hp
    obtain ⟨y,hy,he⟩ := raise_filtration_to_eleven I' BHS R
      (quotientClass 9 (lambdaMultiply 2 zTheta)) hc9 Phi
      (fun c hc => main_af7_correction_killed D' h0 c hc) hkill9 z
    exact ⟨y,hy,fun h => hzn (he.symm.trans h)⟩
  exact main_strip_preserving_nonzero I' BHS.eInfty R h0 zTheta hzTheta
    (sphereProduct eta (sphereProduct theta b)) hshuffle
    (theta_b_eta_fifth_mod_nine_zero_from_choice I' BHS SF h13 eta heta theta htheta b hb) z hzn

end
end KIP126.Main.SectionSeven
