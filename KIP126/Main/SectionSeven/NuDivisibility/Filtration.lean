module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.RelationCertificates
public import Batteries.Tactic.OpenPrivate
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import Init.Data.String.Lemmas.Splits
public import KIP126.Def.SpectralSequence.FilteredComplex.Crossing.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.Synthetic.QuotientTower.Proofs
public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Data
public import KIP126.Def.StableHomotopy.Toda.Law.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Main.Computation.SphereAndCofiber.Consequences
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.Classes.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.AdamsSynthetic.SectionSeven.Predicates

-- The CSV coordinate calculations use the defining string and list equations.
import all Init.Data.List.SplitOn.Basic
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
open KIP126.Literature.AdamsSynthetic
noncomputable section


section NuTargetProof
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Algebra KIP126.Literature.AdamsSynthetic KIP126.Computation.SphereAndCofiber
open KIP126.Algebra KIP126.LinE2 PageRepresentatives KIP126.Computation.Near126
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] adamsTowerInternalD adamsTowerSSData KIP126.LinE2.homogeneousPart
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : KIP126.AdamsSynthetic.SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
private theorem sphere_class_identifications (I' : AdamsComputationTheorems D' L' G) :
    I'.interpretation.sphere 8 134 W = L'.W ∧
    I'.interpretation.sphere 10 134 U = L'.U M' ∧
    I'.interpretation.sphere 14 139 T = L'.target M' := by
  have hU := I'.products ⟨2, 2, 8, 132⟩ (by simp [Raw.products]) h0Sq (atom .x_124_8)
  have h14 := I'.products ⟨1, 2, 1, 16⟩ (by simp [Raw.products]) dataH1 (atom .h4)
  have hT := I'.products ⟨2, 18, 12, 121⟩ (by simp [Raw.products])
    (mulAt dataH1 (atom .h4)) (atom .x_109_12)
  dsimp only at hU h14 hT
  have hAssoc : T = mulAt (mulAt dataH1 (atom .h4)) (atom .x_109_12) := by
    apply Subtype.ext
    exact (mul_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · change I'.interpretation.sphere 8 134
      (atom .x_126_8_4 + atom .x_126_8) = L'.x_126_8_4 + L'.x_126_8
    rw [map_add, I'.distinguishedClasses.x_126_8_4, I'.distinguishedClasses.x_126_8]
  · simpa only [U, SphereAdamsClasses.U, I'.distinguishedClasses.h0_square, I'.distinguishedClasses.x_124_8] using hU
  · rw [hAssoc, hT, h14, I'.distinguishedClasses.h1, I'.distinguishedClasses.h4, I'.distinguishedClasses.x_109_12]
    rfl

private theorem nu_target_of_finite_nonzero
    (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
    (A : AdamsAlgebraStructures D') (ab : AlgebraDetectionCompatibility D' A)
    (nu : BiHom 3 4 (S_0_0 : Syn))
    (hnu : D'.sphereFirstQuotient 1 4 (quotientClass 1 nu)=Sphere.Internal.hi H M' 2)
    (hprod : ∀ x : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M' (s:=1) (t:=4) (s':=13) (t':=135) (Sphere.Internal.hi H M' 2) x=0)
    (a0 : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9))
    (ha0 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a0)
    (hne : sphereAction nu a0≠0) : TargetNuDivisible D' (L'.target M') nu := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a) (hb : KIP126.SpectralSequence.RepresentsOnPage E r p x b) : a = b := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_unique ha hb
  have represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : KIP126.SpectralSequence.RepresentsOnPage E r p x a)
      (ht : KIP126.SpectralSequence.ReachesPage E t p x) : E.d r p a = 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_d_zero_of_later hr0 hrt ha ht
  have represents_before
      {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
      {x : E.Page 2 p} {xt : E.Page t p}
      (hr : 2 ≤ r) (hrt : r ≤ t) (ht : KIP126.SpectralSequence.RepresentsOnPage E t p x xt) :
      ∃ xr, KIP126.SpectralSequence.RepresentsOnPage E r p x xr := by
    exact KIP126.SpectralSequence.FinitePageCalculus.represents_before hr hrt ht
  have differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {t : ℤ} {q : ℤ×ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
      (hr0 : E.r₀ ≤ r) (hrt : r < t)
      (h : KIP126.SpectralSequence.HasDifferential E r p q x y) : KIP126.SpectralSequence.RepresentsOnPage E t q y 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.differential_target_later_zero hr0 hrt h
  have boundary_of_zero_representative
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
  have middle_expand {N : ℕ} (f : Fin N →₀ F2) :
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
  have nu_target_p_cosets (I' : AdamsComputationTheorems D' L' G) :
      ∀ x : Page D' .sphere 11 133,
        x∈boundaries H SphereSpectrum 3 (11,133) ∨
        x-I'.interpretation.basis .sphere 11 133 1∈boundaries H SphereSpectrum 3 (11,133) := by
    classical
    let E := sequence D' .sphere
    have h267 : HasDifferential E 3 (8,131) (11,133)
        ((I'.interpretation.basis .sphere 8 131 0)) ((I'.interpretation.basis .sphere 11 133 0) + (I'.interpretation.basis .sphere 11 133 1)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,8,131,[0],11,133,[0, 1],"S0_AdamsE2_ss",2621⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 267) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (8,131) (11,133) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,11,133,["371,1", "69,1,79,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 189) rfl)
    change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 11 133 i.val at he

    have hb : I'.interpretation.basis .sphere 11 133 0 + I'.interpretation.basis .sphere 11 133 1 ∈
        boundaries H SphereSpectrum 3 (11,133) :=
      boundary_of_zero_representative (r:=4) (p:=(11,133))
        (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h267)
    have he0 : e.symm (Finsupp.single (0:Fin 2) 1)=I'.interpretation.basis .sphere 11 133 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 2) 1)=I'.interpretation.basis .sphere 11 133 1 := he 1
    have hn : -I'.interpretation.basis .sphere 11 133 1=I'.interpretation.basis .sphere 11 133 1 := by
      rw [←he1]
      change -e.symm (Finsupp.single (1:Fin 2) 1)=e.symm (Finsupp.single (1:Fin 2) 1)
      rw [←map_neg]
      congr 1
      ext i
      simp
    intro x
    let c : Fin 2 → F2 := e x
    have hcoef := congrArg e.symm (middle_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1))+
      ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1))+0) at hcoef
    simp only [he0,he1,add_zero] at hcoef
    by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
    · left
      rw [hcoef]
      simpa only [h0,h1,if_true,zero_add] using (boundaries H SphereSpectrum 3 (11,133)).zero_mem
    · right
      rw [hcoef]
      simp only [h0,h1,if_false,if_true,zero_add,sub_self]
      exact Submodule.zero_mem _
    · right
      rw [hcoef]
      simpa only [h0,h1,if_false,if_true,add_zero,sub_eq_add_neg,hn] using hb
    · left
      rw [hcoef]
      simpa only [h0,h1,if_false] using hb
  have nu_target_q_cosets (I' : AdamsComputationTheorems D' L' G) :
      ∀ x : Page D' .sphere 12 134,
        x∈boundaries H SphereSpectrum 3 (12,134) ∨
        x-I'.interpretation.basis .sphere 12 134 0∈boundaries H SphereSpectrum 3 (12,134) := by
    classical
    let E := sequence D' .sphere
    have h294 : HasDifferential E 2 (10,133) (12,134)
        ((I'.interpretation.basis .sphere 10 133 0)) ((I'.interpretation.basis .sphere 12 134 2)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,10,133,[0],12,134,[2],"S0_AdamsE2_ss",2682⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 294) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (10,133) (12,134) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    have h295 : HasDifferential E 3 (9,132) (12,134)
        ((I'.interpretation.basis .sphere 9 132 0)) ((I'.interpretation.basis .sphere 12 134 1)) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,3,9,132,[0],12,134,[1],"S0_AdamsE2_ss",2683⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 295) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 3 (9,132) (12,134) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      exact hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
      exact List.mem_of_getElem? (l := Raw.degrees) (i := 198) rfl)
    change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 12 134 i.val at he

    let P := boundaries H SphereSpectrum 3 (12,134)
    have hb1 : I'.interpretation.basis .sphere 12 134 1 ∈ P :=
      boundary_of_zero_representative (r:=4) (p:=(12,134))
        (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h295)
    have hb2 : I'.interpretation.basis .sphere 12 134 2 ∈ P :=
      boundary_of_zero_representative (r:=4) (p:=(12,134))
        (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h294)
    have he0 : e.symm (Finsupp.single (0:Fin 3) 1)=I'.interpretation.basis .sphere 12 134 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 3) 1)=I'.interpretation.basis .sphere 12 134 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 3) 1)=I'.interpretation.basis .sphere 12 134 2 := he 2
    have hif (c : F2) {a : Page D' .sphere 12 134} (h : a∈P) :
        (if c=0 then 0 else a)∈P := by split; exact P.zero_mem; exact h
    intro x
    let c : Fin 3 → F2 := e x
    have hcoef := congrArg e.symm (middle_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1))+
      ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1))+
      ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1))+0)) at hcoef
    simp only [he0,he1,he2,add_zero] at hcoef
    have hm := P.add_mem (hif (c 1) hb1) (hif (c 2) hb2)
    by_cases h0 : c 0=0
    · left
      rw [hcoef]
      simpa only [h0,if_true,zero_add] using hm
    · right
      rw [hcoef]
      simp only [h0,if_false]
      convert hm using 1 <;> first | rfl | abel
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i ≫ familyPageMap D'.family g r i = familyPageMap D'.family (f ≫ g) r i := by
    rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map
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
  have sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
          ConcreteCategory.congr_hom (family_page_comp (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
        _ = targetNuLabel D' .sphere s t k x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          dsimp only [targetNuLabel]
          congr 1
    have hlabel : familyPageMap D'.family f 2 (s,t,t-k) (D'.quotientLabel q s t k x)=
        finiteTargetLabel D' .sphere q s t k x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D'.nu.unitIso.inv q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)) :=
          (ConcreteCategory.congr_hom (family_page_comp D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)).symm
        _ = finiteTargetLabel D' .sphere q s t k x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
    exact hlabel
  have finite_sphere_infinity_cycle_label_exists
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
      ∃ x : E2 H SphereSpectrum s t,
        x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
        HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
          (D'.quotientLabel q s t k x) e := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq : (D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k) ≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    obtain ⟨c,hc⟩ := Quotient.exists_rep (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e))
    have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hc.symm
    have hl : familyPageMap D'.family f 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k c.val)=D'.quotientLabel q s t k c.val := by
      rw [←sphere_quotient_label_to_nu q k s t c.val]
      calc
        _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k c.val) :=
          ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
        _ = D'.quotientLabel q s t k c.val := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
            (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
    rw [hl,heq] at h
    refine ⟨c.val,?_,h⟩
    convert c.property using 1; congr 1; omega
  have finite_sphere_filtration_has_cycle_label
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a) :
      ∃ x : E2 H SphereSpectrum s t,
        x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
        Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) q)
    have ham : a ∈ (ModuleCat.subobjectModule
        (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (t-s,t-k)))
        (F.F s (t-s,t-k)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let gr := F.toAssociatedGraded s (t-s,t-k) a'
    let e := ((D'.quotientConvergence q hq).identification (s,t,t-k)).inv gr
    have he : ((D'.quotientConvergence q hq).identification (s,t,t-k)).hom e=gr :=
      ConcreteCategory.congr_hom ((D'.quotientConvergence q hq).identification (s,t,t-k)).inv_hom_id gr
    obtain ⟨x,hc,hx⟩ := finite_sphere_infinity_cycle_label_exists BHS q k hq hkq s t e
    exact ⟨x,hc,e,hx,a',ha',he⟩
  have sphere_quotient_label_from_nu (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) = D'.quotientLabel q s t k x := by
    rw [←sphere_quotient_label_to_nu q k s t x]
    have hcomp := ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.map D'.nu.unitIso.inv q) (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k))
      (D'.quotientLabel q s t k x)
    have hgf : XModLambdaN.map D'.nu.unitIso.inv q ≫ XModLambdaN.map D'.nu.unitIso.hom q = 𝟙 _ := by
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hid : familyPageMap D'.family (𝟙 (XModLambdaN (S_0_0 : Syn) q)) 2 (s,t,t-k) = 𝟙 _ := by
      rw [family_map_data,CategoryTheory.Functor.map_id]
      exact SSDataMorphism.pageMap_id
        (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-k) (↑(2-2:ℤ).toNat)
    exact hcomp.trans (by rw [hgf]; erw [hid]; rfl)
  have detected_map
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
  have finite_detection_peel
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
  have finite_sphere_frame
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (c : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
      (hframe : ∀ y : PageRepresentatives.CycleQuotient H SphereSpectrum
          ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
        y=0 ∨ y=NestedQuotient.projection _ _ c) :
      ∀ e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
          (D'.quotientLabel q s t k c.val) e := by
    intro e
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq : (D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k) ≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    rcases hframe (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)) with hz|hz
    · left
      have hzero : (D'.family.functor.map g).eInftyMap (s,t,t-k) e=0 :=
        P.injective (hz.trans (map_zero P).symm)
      rw [hzero,map_zero] at heq
      exact heq.symm
    · right
      have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hz
      have hl : familyPageMap D'.family f 2 (s,t,t-k)
          (finiteTargetLabel D' .sphere q s t k c.val)=D'.quotientLabel q s t k c.val := by
        rw [←sphere_quotient_label_to_nu q k s t c.val]
        calc
          _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k c.val) :=
            ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
          _ = D'.quotientLabel q s t k c.val := by
            rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
            exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
              (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
              (s,t,t-k) ↑(2-2:ℤ).toNat) _
      have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
      rw [hl,heq] at h
      exact h
  have nu_target_finite_peel_permanent
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x)
      (hcoset : ∀ y : E2 H SphereSpectrum s t,
        y∈boundaries H SphereSpectrum (1+k) (s,t) ∨
        y-x∈boundaries H SphereSpectrum (1+k) (s,t))
      (c0 : BiHom (t-s) t (S_0_0 : Syn))
      (hc0 : D'.sphereFirstQuotient s t (quotientClass 1 c0)=x)
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a) :
      ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) (s+1)
        (a-(if b then quotientClass q (lambdaMultiply k c0) else 0)) := by
    let c : cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t) :=
      ⟨x,permanentCycles_le_cycles H SphereSpectrum (s,t) _ hx⟩
    have hframe : ∀ z : CycleQuotient H SphereSpectrum ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
        z=0 ∨ z=NestedQuotient.projection _ _ c := by
      intro z
      obtain ⟨z⟩ := z
      change NestedQuotient.projection _ _ z=0 ∨
        NestedQuotient.projection _ _ z=NestedQuotient.projection _ _ c
      rcases hcoset z.val with hz | hz
      · left
        exact (NestedQuotient.projection_eq_zero z).mpr (by convert hz using 1; congr 1; omega)
      · right
        apply sub_eq_zero.mp
        rw [←map_sub]
        apply (NestedQuotient.projection_eq_zero (z-c)).mpr
        change z.val-x ∈ boundaries H SphereSpectrum (1+t-(t-k)) (s,t)
        convert hz using 1; congr 1; omega
    have frame := finite_sphere_frame BHS q k hq hk s t c hframe
    have hc := D'.comparisonCompatible.homotopy_lambda s t k c0
    rw [hc0] at hc
    have hcq := detected_map .sphere (.quotient q .sphere) (XModLambdaN.incl _ q)
      (s,t,t-k) (D'.sphereE2 s t k x) (lambdaMultiply k c0) hc
    exact finite_detection_peel q hq (s,t,t-k) (D'.quotientLabel q s t k x) frame
      (quotientClass q (lambdaMultiply k c0)) hcq a ha
  have sphere_first_label_transport (s t : ℤ)
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
  have sphere_permanent_first_quotient_lift
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
  have named_survival_labels
      {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
      {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
      {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
      {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I' : AdamsComputationTheorems D' L' G) :
      I'.interpretation.sphere 10 134 U = I'.interpretation.basis .sphere 10 134 4 ∧
      I'.interpretation.sphere 11 133 P = I'.interpretation.basis .sphere 11 133 1 ∧
      I'.interpretation.sphere 12 134 Q = I'.interpretation.basis .sphere 12 134 0 := by
    have u_label : I'.interpretation.sphere 10 134 U = I'.interpretation.basis .sphere 10 134 4 := by
      have hc := I'.monomials (⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ : Raw.Degree) (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 181) rfl) rfl
      obtain ⟨z,hz,he⟩ := hc (4 : Fin 5)
      have heq : U=z := by
        apply Subtype.ext
        rw [hz]
        change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨367,by decide⟩ = projection (monomialOfString "0,2,367,1")
        have hs : "0,2,367,1" ≠ "" := by decide
        have hp : (("0,2,367,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,367,1] := by
          have split : "0,2,367,1".splitOn "," = ["0","2","367","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,if_neg hs,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
      rw [heq]
      exact he
    have p_label : I'.interpretation.sphere 11 133 P = I'.interpretation.basis .sphere 11 133 1 := by
      have hc := I'.monomials (⟨.sphere,11,133,["371,1","69,1,79,1"]⟩ : Raw.Degree) (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 189) rfl) rfl
      obtain ⟨z,hz,he⟩ := hc (1 : Fin 2)
      have heq : P=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨69,by decide⟩ * generator ⟨79,by decide⟩ = projection (monomialOfString "69,1,79,1")
        have hs : "69,1,79,1" ≠ "" := by decide
        have hp : (("69,1,79,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1,79,1] := by
          have split : "69,1,79,1".splitOn "," = ["69","1","79","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,if_neg hs,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
      rw [heq]
      exact he
    have q_label : I'.interpretation.sphere 12 134 Q = I'.interpretation.basis .sphere 12 134 0 := by
      have hc := I'.monomials (⟨.sphere,12,134,["18,1,188,1","0,1,371,1","0,1,69,1,79,1"]⟩ : Raw.Degree) (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 198) rfl) rfl
      obtain ⟨z,hz,he⟩ := hc (0 : Fin 3)
      have heq : Q=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨18,by decide⟩ * generator ⟨188,by decide⟩ = projection (monomialOfString "18,1,188,1")
        have hs : "18,1,188,1" ≠ "" := by decide
        have hp : (("18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,188,1] := by
          have split : "18,1,188,1".splitOn "," = ["18","1","188","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,if_neg hs,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
      rw [heq]
      exact he
    exact ⟨u_label,p_label,q_label⟩
  have nu_target_pq_lift_peel
      (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
      (a : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a) :
      ∃ (p : BiHom 122 133 (S_0_0 : Syn)) (q : BiHom 122 134 (S_0_0 : Syn))
        (bp bq : Bool),
        D'.sphereFirstQuotient 11 133 (quotientClass 1 p)=I'.interpretation.sphere 11 133 P ∧
        D'.sphereFirstQuotient 12 134 (quotientClass 1 q)=I'.interpretation.sphere 12 134 Q ∧
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13
          (a-((if bp then (show BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) from quotientClass 9 (lambdaMultiply 6 p)) else 0)+
            (if bq then (show BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) from quotientClass 9 (lambdaMultiply 7 q)) else 0))) := by
    obtain ⟨_,hP,hQ⟩ := named_survival_labels I'
    have hp : IsPermanentCycle (sequence D' .sphere) (11,133) (I'.interpretation.sphere 11 133 P) := by
      obtain ⟨z,hz,_⟩ := SF.p_permanent
      exact ⟨z,hz⟩
    have hq : IsPermanentCycle (sequence D' .sphere) (12,134) (I'.interpretation.sphere 12 134 Q) := by
      obtain ⟨z,hz,_⟩ := SF.q_permanent
      exact ⟨z,hz⟩
    obtain ⟨p,hp0⟩ := sphere_permanent_first_quotient_lift BHS 11 133 (I'.interpretation.sphere 11 133 P) hp
    obtain ⟨q,hq0⟩ := sphere_permanent_first_quotient_lift BHS 12 134 (I'.interpretation.sphere 12 134 Q) hq
    have cp : ∀ y : E2 H SphereSpectrum 11 133,
        y∈boundaries H SphereSpectrum 7 (11,133) ∨
        y-I'.interpretation.sphere 11 133 P∈boundaries H SphereSpectrum 7 (11,133) := by
      intro y
      rw [hP]
      rcases nu_target_p_cosets I' y with hh | hh
      · exact Or.inl (boundaries_monotone H SphereSpectrum (11,133) (by decide : (3:ℤ)≤7) hh)
      · exact Or.inr (boundaries_monotone H SphereSpectrum (11,133) (by decide : (3:ℤ)≤7) hh)
    have cq : ∀ y : E2 H SphereSpectrum 12 134,
        y∈boundaries H SphereSpectrum 8 (12,134) ∨
        y-I'.interpretation.sphere 12 134 Q∈boundaries H SphereSpectrum 8 (12,134) := by
      intro y
      rw [hQ]
      rcases nu_target_q_cosets I' y with hh | hh
      · exact Or.inl (boundaries_monotone H SphereSpectrum (12,134) (by decide : (3:ℤ)≤8) hh)
      · exact Or.inr (boundaries_monotone H SphereSpectrum (12,134) (by decide : (3:ℤ)≤8) hh)
    obtain ⟨bp,hbp⟩ := nu_target_finite_peel_permanent BHS.eInfty 9 6 (by decide) (by decide)
      11 133 (I'.interpretation.sphere 11 133 P) hp cp p hp0 a ha
    let v : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) := quotientClass 9 (lambdaMultiply 6 p)
    change FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 (a-(if bp then v else 0)) at hbp
    obtain ⟨bq,hbq⟩ := nu_target_finite_peel_permanent BHS.eInfty 9 7 (by decide) (by decide)
      12 134 (I'.interpretation.sphere 12 134 Q) hq cq q hq0 (a-(if bp then v else 0)) hbp
    refine ⟨p,q,bp,bq,hp0,hq0,?_⟩
    simpa only [v,sub_sub,Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub] using hbq
  have sphere_label_to_nu (k : ℕ) (s t : ℤ) (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)=
        targetNuLabel D' .sphere s t k x := by
    let nx : (D'.family.obj ((SyntheticCategory.biShift (0,0)).obj
        (D'.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
      simpa only [ClassicalObject.obj,add_zero] using D'.nuE2 .sphere 0 s t k x
    have hc : familyPageMap D'.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D'.sphereE2 s t k x := by
      convert D'.comparisonCompatible.sphere_nu s t k x using 1; simp [nx,ClassicalObject.obj]
    calc
      _ = familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D'.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y=>familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D'.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) ≫ D'.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (family_page_comp (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D' .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have sphere_boundary_detects_zero (BHS : EInftyComparison D') (k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈boundaries H SphereSpectrum (1+k) (s,t)) :
      Detects D'.sphereConvergence (s,t,t-k) (D'.sphereE2 s t k x) 0 := by
    let P := BHS.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
    let z : permanentCycles H SphereSpectrum (s,t) := ⟨x,boundaries_le_permanentCycles H SphereSpectrum (s,t) (1+k) hx⟩
    have hz : NestedQuotient.projection _ (boundaries H SphereSpectrum (1+t-(t-k)) (s,t)) z=0 := by
      apply (NestedQuotient.projection_eq_zero z).mpr
      convert hx using 1; congr 1; omega
    have hn : HasInfinityRepresentative (D'.family.nu D'.nu SphereSpectrum) 2 (s,t,t-k)
        (targetNuLabel D' .sphere s t k x) 0 := by
      apply (BHS.labels.2 .sphere (s,t) k z 0).mpr
      exact P.map_zero.trans hz.symm
    have hf := family_infinity_representative_map D'.nu.unitIso.hom (s,t,t-k) _ _ hn
    rw [map_zero] at hf
    have hlabel : familyPageMap D'.family D'.nu.unitIso.hom 2 (s,t,t-k)
        (targetNuLabel D' .sphere s t k x)=D'.sphereE2 s t k x := by
      rw [←sphere_label_to_nu k s t x]
      have hc := ConcreteCategory.congr_hom (family_page_comp D'.nu.unitIso.inv D'.nu.unitIso.hom 2 (s,t,t-k))
        (D'.sphereE2 s t k x)
      rw [D'.nu.unitIso.inv_hom_id] at hc
      have hid : familyPageMap D'.family (𝟙 (S_0_0 : Syn)) 2 (s,t,t-k)=𝟙 _ := by
        rw [family_map_data,CategoryTheory.Functor.map_id]
        exact SSDataMorphism.pageMap_id (D'.family.functor.obj (S_0_0 : Syn)).ssData (s,t,t-k) ↑(2-2:ℤ).toNat
      exact hc.trans (ConcreteCategory.congr_hom hid _)
    rw [hlabel] at hf
    exact ⟨0,hf,0,map_zero _,by simp only [map_zero]⟩
  have sphere_infinity_zero_of_permanent_quotient
      (BHS : EInftyComparison D') (s t w : ℤ) (hw : 0≤t-w)
      (hc : Subsingleton (PermanentQuotient H SphereSpectrum (1+t-w) (s,t))) :
      IsZero (((D'.family.obj (S_0_0 : Syn)).sequence.ssData (s,t,w)).eInfty) := by
    let e := BHS.presentation.nuWindow SphereSpectrum (s,t) w (by dsimp only; omega)
    haveI := hc
    haveI : Subsingleton (((D'.family.nu D'.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nu D'.nu SphereSpectrum).sequence.ssData (s,t,w)).eInfty)
    let f := (D'.family.functor.map D'.nu.unitIso.hom).eInftyMap (s,t,w)
    let g := (D'.family.functor.map D'.nu.unitIso.inv).eInftyMap (s,t,w)
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        Iso.inv_hom_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (IsZero.iff_id_eq_zero _).mpr
    exact hgf.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have nu_target_sphere_gap (BHS : EInftyComparison D')
      (hpage : Subsingleton ((sequence D' .sphere).Page 5 (13,138)))
      (a : BiHom 125 135 (S_0_0 : Syn)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14 a := by
    apply D'.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero 13 14 125 135 (by decide)
    intro j hj hj'
    have : j=13 := by omega
    subst j
    apply sphere_infinity_zero_of_permanent_quotient BHS 13 138 135 (by decide)
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨z⟩ := z
    apply (NestedQuotient.projection_eq_zero z).mpr
    have hc := permanentCycles_le_cycles H SphereSpectrum (13,138) 4 z.property
    obtain ⟨zr,hzr⟩ := (isCycle_iff_represents H SphereSpectrum 5 (by decide) (13,138) z.val).mp ⟨by decide,hc⟩
    haveI : Subsingleton ((adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C:=C))).Page 5 (13,138)) := hpage
    have hz : zr=0 := Subsingleton.elim _ _
    rw [hz] at hzr
    exact boundary_of_zero_representative (r:=5) (p:=(13,138)) (x:=z.val) hzr
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
  have map_filtration {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D'.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D'.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have sphere_permanent_frame
      (BHS : EInftyComparison D') (k : ℕ) (s t : ℤ)
      (c : PageRepresentatives.permanentCycles H SphereSpectrum (s,t))
      (hframe : ∀ y : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-k)) (s,t),
        y=0 ∨ y=NestedQuotient.projection _ _ c) :
      ∀ e : ((D'.family.obj (S_0_0 : Syn)).sequence.ssData (s,t,t-k)).eInfty,
        e=0 ∨ HasInfinityRepresentative (D'.family.obj (S_0_0 : Syn)) 2 (s,t,t-k)
          (D'.sphereE2 s t k c.val) e := by
    intro e
    let P := BHS.presentation.nuWindow SphereSpectrum (s,t) (t-k)
      (by omega)
    let f := D'.nu.unitIso.hom
    let g := D'.nu.unitIso.inv
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      exact Iso.inv_hom_id _
    have heq : (D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k) ≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    rcases hframe (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)) with hz|hz
    · left
      have hzero : (D'.family.functor.map g).eInftyMap (s,t,t-k) e=0 :=
        P.injective (hz.trans (map_zero P).symm)
      rw [hzero,map_zero] at heq
      exact heq.symm
    · right
      have hn := (BHS.labels.2 .sphere (s,t) k c _).mpr hz
      have hl : familyPageMap D'.family f 2 (s,t,t-k)
          (targetNuLabel D' .sphere s t k c.val)=D'.sphereE2 s t k c.val := by
        rw [←sphere_label_to_nu k s t c.val]
        calc
          _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.sphereE2 s t k c.val) :=
            ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
          _ = D'.sphereE2 s t k c.val := by
            rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
            exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
              (D'.family.functor.obj ((S_0_0 : Syn))).ssData
              (s,t,t-k) ↑(2-2:ℤ).toNat) _
      have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
      rw [hl,heq] at h
      exact h
  have target_permanent_quotient_frame
      (T : E2 H SphereSpectrum 14 139)
      (ht : T∈permanentCycles H SphereSpectrum (14,139))
      (hf : ∃ a : (sequence D' .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D' .sphere) 6 (14,139) T a ∧
        ∀ y : (sequence D' .sphere).Page 6 (14,139),y=0 ∨ y=a) :
      ∀ z : PermanentQuotient H SphereSpectrum 5 (14,139),
        z=0 ∨ z=NestedQuotient.projection _ _ ⟨T,ht⟩ := by
    obtain ⟨a,ha,hall⟩ := hf
    intro z
    obtain ⟨z⟩ := z
    change NestedQuotient.projection _ _ z=0 ∨ NestedQuotient.projection _ _ z=NestedQuotient.projection _ _ ⟨T,ht⟩
    have hc := permanentCycles_le_cycles H SphereSpectrum (14,139) 5 z.property
    obtain ⟨b,hb⟩ := (isCycle_iff_represents H SphereSpectrum 6 (by decide) (14,139) z.val).mp ⟨by decide,hc⟩
    rcases hall b with hz|hz
    · left
      apply (NestedQuotient.projection_eq_zero z).mpr
      rw [hz] at hb
      exact boundary_of_zero_representative (r:=6) (p:=(14,139)) (x:=z.val) hb
    · right
      apply sub_eq_zero.mp
      rw [←map_sub]
      apply (NestedQuotient.projection_eq_zero
        (B := boundaries H SphereSpectrum 5 (14,139))
        (z-(⟨T,ht⟩ : permanentCycles H SphereSpectrum (14,139)))).mpr
      have hr : RepresentsOnPage (sequence D' .sphere) 6 (14,139) (z.val-T) 0 := by
        change RepresentsOnPage (sequence D' .sphere) 6 (14,139) z.val b at hb
        obtain ⟨hr,z1,hz1,hb1⟩ := hb
        obtain ⟨_,z2,hz2,ha2⟩ := ha
        refine ⟨hr,z1-z2,?_,?_⟩
        · simp only [map_sub,hz1,hz2]
        · simp only [map_sub,hb1,ha2,hz,sub_self]
      exact boundary_of_zero_representative (r:=6) (p:=(14,139)) (x:=z.val-T) hr
  have nu_target_sphere_detected
      (BHS : EInftyComparison D') (T : E2 H SphereSpectrum 14 139)
      (ht : T∈permanentCycles H SphereSpectrum (14,139))
      (hf : ∃ a : (sequence D' .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D' .sphere) 6 (14,139) T a ∧
        ∀ y : (sequence D' .sphere).Page 6 (14,139),y=0 ∨ y=a)
      (a : BiHom 125 135 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14 a)
      (hne : quotientClass 9 (lambdaMultiply 4 a) ≠ 0) :
      Detects D'.sphereConvergence (14,139,135) (D'.sphereE2 14 139 4 T) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)
    have ham : a∈(ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,135)))
        (F.F 14 (125,135)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let gr := F.toAssociatedGraded 14 (125,135) a'
    let e := (D'.sphereConvergence.identification (14,139,135)).inv gr
    have he : (D'.sphereConvergence.identification (14,139,135)).hom e=gr :=
      ConcreteCategory.congr_hom (D'.sphereConvergence.identification (14,139,135)).inv_hom_id gr
    have hframe := sphere_permanent_frame BHS 4 14 139 ⟨T,ht⟩ (target_permanent_quotient_frame T ht hf)
    rcases hframe e with hz|hz
    · have hd0 : Detects D'.sphereConvergence (14,139,135) 0 a := by
        refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,a',ha',?_⟩
        rw [hz] at he
        exact he
      have hh := detects_zero_filtration D'.sphereConvergence (14,139,135) hd0
      have hl := lambda_filtration_preserved 4 15 a hh
      have hq := map_filtration (XModLambdaN.incl (S_0_0 : Syn) 9) (lambdaMultiply 4 a) hl
      exact False.elim (hne (sphere_quotient_high_filtration_zero BHS 9 (by decide) 125 131 15 (by decide) _ hq))
    · exact ⟨e,hz,a',ha',he⟩
  have nu_target_sphere_products_filtration (BHS : EInftyComparison D')
      (nu : BiHom 3 4 (S_0_0 : Syn))
      (hnu : D'.sphereFirstQuotient 1 4 (quotientClass 1 nu)=Sphere.Internal.hi H M' 2)
      (P : E2 H SphereSpectrum 11 133) (Q : E2 H SphereSpectrum 12 134)
      (hp : Sphere.Internal.product H M' (s:=1) (t:=4) (s':=11) (t':=133)
        (Sphere.Internal.hi H M' 2) P∈boundaries H SphereSpectrum 2 (12,137))
      (hq : Sphere.Internal.product H M' (s:=1) (t:=4) (s':=12) (t':=134)
        (Sphere.Internal.hi H M' 2) Q∈boundaries H SphereSpectrum 2 (13,138))
      (hpage : Subsingleton ((sequence D' .sphere).Page 5 (13,138)))
      (p : BiHom 122 133 (S_0_0 : Syn)) (q : BiHom 122 134 (S_0_0 : Syn))
      (hlp : D'.sphereFirstQuotient 11 133 (quotientClass 1 p)=P)
      (hlq : D'.sphereFirstQuotient 12 134 (quotientClass 1 q)=Q) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14
        (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 1 p)) ∧
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14
        (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 2 q)) := by
    have hn := D'.comparisonCompatible.homotopy_lambda 1 4 1 nu
    rw [hnu] at hn
    constructor
    · have hpd := D'.comparisonCompatible.homotopy_lambda 11 133 1 p
      rw [hlp] at hpd
      have hd := D'.multiplicationCompatible 1 4 11 133 1 1
        (Sphere.Internal.hi H M' 2) P (lambdaMultiply 1 nu) (lambdaMultiply 1 p) hn hpd
      let v : E2 H SphereSpectrum 12 137 := Sphere.Internal.product H M'
        (s:=1) (t:=4) (s':=11) (t':=133) (Sphere.Internal.hi H M' 2) P
      have hb : v∈boundaries H SphereSpectrum 3 (12,137) :=
        boundaries_monotone H SphereSpectrum (12,137) (by decide : (2:ℤ)≤3) hp
      have hz := sphere_boundary_detects_zero BHS 2 12 137 v hb
      have hf : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13
          (sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 1 p)) := by
        simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,Nat.reduceAdd,Nat.cast_ofNat] using
          detects_sub_filtration D'.sphereConvergence (12,137,135) hd hz
      exact (nu_target_sphere_gap BHS hpage _).mp hf
    · have hqd := D'.comparisonCompatible.homotopy_lambda 12 134 2 q
      rw [hlq] at hqd
      have hd := D'.multiplicationCompatible 1 4 12 134 1 2
        (Sphere.Internal.hi H M' 2) Q (lambdaMultiply 1 nu) (lambdaMultiply 2 q) hn hqd
      let v : E2 H SphereSpectrum 13 138 := Sphere.Internal.product H M'
        (s:=1) (t:=4) (s':=12) (t':=134) (Sphere.Internal.hi H M' 2) Q
      have hb : v∈boundaries H SphereSpectrum 4 (13,138) :=
        boundaries_monotone H SphereSpectrum (13,138) (by decide : (2:ℤ)≤4) hq
      have hz := sphere_boundary_detects_zero BHS 3 13 138 v hb
      simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,Nat.reduceAdd,Nat.cast_ofNat] using
        detects_sub_filtration D'.sphereConvergence (13,138,135) hd hz
  have finite_sphere_boundary_detects_zero
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈boundaries H SphereSpectrum (1+k) (s,t)) :
      Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) 0 := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let z : cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t) :=
      ⟨x,boundaries_le_cycles H SphereSpectrum (s,t) (1+k) _ hx⟩
    have hz : NestedQuotient.projection _ (boundaries H SphereSpectrum (1+t-(t-k)) (s,t)) z=0 := by
      apply (NestedQuotient.projection_eq_zero z).mpr
      convert hx using 1; congr 1; omega
    have hn : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) 0 := by
      apply (BHS.labels.1 .sphere q hq (s,t) k hk z 0).mpr
      change P 0 = NestedQuotient.projection _ _ z
      simpa only [map_zero] using hz.symm
    have h := family_infinity_representative_map (XModLambdaN.map D'.nu.unitIso.hom q)
      (s,t,t-k) _ _ hn
    rw [sphere_quotient_label_from_nu q k s t x,map_zero] at h
    exact ⟨0,h,0,by simp only [map_zero],by simp only [map_zero]⟩
  have nu_target_remainder_zero
      (BHS : EInftyComparison D') (A : AdamsAlgebraStructures D') (ab : AlgebraDetectionCompatibility D' A)
      (nu : BiHom 3 4 (S_0_0 : Syn))
      (hd : Detects D'.sphereConvergence (1,4,4)
        (D'.sphereE2 1 4 0 (Sphere.Internal.hi H M' 2)) nu)
      (hprod : ∀ x : E2 H SphereSpectrum 13 135,
        Sphere.Internal.product H M' (s:=1) (t:=4) (s':=13) (t':=135)
          (Sphere.Internal.hi H M' 2) x = 0)
      (a : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 a) :
      sphereAction nu a=0 := by
    obtain ⟨x,_,hx⟩ := finite_sphere_filtration_has_cycle_label BHS 9 8 (by decide) (by decide) 13 135 a ha
    have hm := ab.finite_action 9 (by decide) 1 4 13 135 0 8
      (Sphere.Internal.hi H M' 2) x nu a hd hx
    rw [hprod x] at hm
    have hz := finite_sphere_boundary_detects_zero BHS 9 8 (by decide) (by decide) 14 139 0
      (Submodule.zero_mem _)
    have hf : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 (sphereAction nu a) := by
      simpa only [sub_zero,homotopyRegrade,Int.reduceAdd,Int.reduceSub,SyntheticObject.obj] using
        detects_sub_filtration (D'.quotientConvergence 9 (by decide)) (14,139,131) hm hz
    exact sphere_quotient_high_filtration_zero BHS 9 (by decide) 125 131 15 (by decide) _ hf
  have boundary_by_is_boundary {p : ℤ×ℤ}
      {x : (sequence D' .sphere).Page 2 p}
      (hx : IsBoundaryBy (sequence D' .sphere) 2 p x) :
      x∈boundaries H SphereSpectrum 2 p := by
    let S := (sequence D' .sphere).ssData p
    obtain ⟨hr,b,hb⟩ := hx
    change (Subobject.ofLE (S.B 1) (S.B ⊤) _ ≫
      Subobject.ofLE (S.B ⊤) (S.Z ⊤) _ ≫ Subobject.ofLE (S.Z ⊤) (S.Z 0) _ ≫ S.pageπ 0) b=x at hb
    change ∃ b, (boundaryMap H SphereSpectrum 1 p).hom b=x
    refine ⟨b,?_⟩
    change (Subobject.ofLE (S.B 1) (S.Z 0) _ ≫ S.pageπ 0) b=x
    rw [←Category.assoc,←Category.assoc,Subobject.ofLE_comp_ofLE,Subobject.ofLE_comp_ofLE] at hb
    exact hb
  have nu_target_pq_boundaries (I' : AdamsComputationTheorems D' L' G) (SF : Derived.SphereFacts I'.interpretation) :
      Sphere.Internal.product H M' (s:=1) (t:=4) (s':=11) (t':=133)
        (Sphere.Internal.hi H M' 2) (I'.interpretation.sphere 11 133 P) ∈ boundaries H SphereSpectrum 2 (12,137) ∧
      Sphere.Internal.product H M' (s:=1) (t:=4) (s':=12) (t':=134)
        (Sphere.Internal.hi H M' 2) (I'.interpretation.sphere 12 134 Q) ∈ boundaries H SphereSpectrum 2 (13,138) := by
    have hp := boundary_by_is_boundary SF.p_h2_boundary
    have hq := boundary_by_is_boundary SF.q_h2_boundary
    constructor
    · rw [←I'.distinguishedClasses.h2,←I'.products ⟨1,4,11,133⟩ (by simp [Raw.products])]
      have hm : mulAt (atom .h2) P=mulAt P (atom .h2) := by
        apply Subtype.ext
        exact mul_comm _ _
      rw [hm]
      exact hp
    · rw [←I'.distinguishedClasses.h2,←I'.products ⟨1,4,12,134⟩ (by simp [Raw.products])]
      have hm : mulAt (atom .h2) Q=mulAt Q (atom .h2) := by
        apply Subtype.ext
        exact mul_comm _ _
      rw [hm]
      exact hq
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
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have lambda_one_shift (coh : BiShiftCoherence Syn) (a : ℤ×ℤ) (A : Syn) :
      lambdaPow 1 ((SyntheticCategory.biShift a).obj A)=
        (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
    rw [lambdaPow_one coh,lambdaPow_one coh]
    simpa only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc] using coh.lambda_comm a A
  have nu_target_lambda_left (D' : AdamsComparison H M' Syn)
      (etaShuffle : BiHom 3 4 (S_0_0 : Syn))
      (a : BiHom 122 132 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 1 etaShuffle) a = lambdaMultiply 1 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv D'.shiftCoherence (3,4) (122,132) (0,-1)
      (125,136) (122,131) (125,135) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv D'.shiftCoherence (3,4) (0,-1) (122,132)
      (3,3) (122,131) (125,135) (by decide) (by decide) (by decide) (by decide) S
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at h₁ h₂
    have hp :
      (SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S ≫
        lambdaPow 1 (Smn 125 136) ≫
        (SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app S =
      (SyntheticCategory.biShift_comp (3,3) (122,132)).inv.app S ≫
        (SyntheticCategory.biShift (122,132)).map
          ((SyntheticCategory.biShift_comp (3,4) (0,-1)).inv.app S) ≫
        (SyntheticCategory.biShift (122,132)).map (lambdaPow 1 (Smn 3 4)) := by
      rw [←lambdaPow_naturality]
      change (SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S ≫
        (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app S) ≫
        lambdaPow 1 ((SyntheticCategory.biShift (122,132)).obj (Smn 3 4)) = _
      rw [lambda_one_shift D'.shiftCoherence (122,132) (Smn 3 4)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app S)]
      erw [h₁]
      simp only [Category.assoc,Smn,S,Int.natCast_one,Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (122,132)).map (lambdaPow 1 (Smn 3 4))) h₂.symm)
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (122,132)).map etaShuffle ≫ a) hp).symm
  have nu_target_four_one (D' : AdamsComparison H M' Syn) {X : Syn} (c : BiHom 125 136 X) :
      lambdaMultiply 4 (lambdaMultiply 1 c)=lambdaMultiply 5 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,136) (0,-1) (0,-4)
      (125,135) (0,-5) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
    erw [←reassoc_of% (lambdaPow_naturality 4 ((SyntheticCategory.biShift_comp (125,136) (0,-1)).inv.app (S_0_0 : Syn)))]
    erw [←reassoc_of% (lambdaPow_naturality 4 (lambdaPow 1 (Smn 125 136)))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add D'.shiftCoherence 1 4 5 (by decide) (Smn 125 136)]
    simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
    rfl
  have nu_target_five_one (D' : AdamsComparison H M' Syn) {X : Syn} (c : BiHom 122 133 X) :
      lambdaMultiply 5 (lambdaMultiply 1 c)=lambdaMultiply 6 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (122,133) (0,-1) (0,-5)
      (122,132) (0,-6) (122,127) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
    erw [←reassoc_of% (lambdaPow_naturality 5 ((SyntheticCategory.biShift_comp (122,133) (0,-1)).inv.app (S_0_0 : Syn)))]
    erw [←reassoc_of% (lambdaPow_naturality 5 (lambdaPow 1 (Smn 122 133)))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add D'.shiftCoherence 1 5 6 (by decide) (Smn 122 133)]
    simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
    rfl
  have nu_target_five_two (D' : AdamsComparison H M' Syn) {X : Syn} (c : BiHom 122 134 X) :
      lambdaMultiply 5 (lambdaMultiply 2 c)=lambdaMultiply 7 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (122,134) (0,-2) (0,-5)
      (122,132) (0,-7) (122,127) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Nat.cast_ofNat,Int.reduceSub]
    erw [←reassoc_of% (lambdaPow_naturality 5 ((SyntheticCategory.biShift_comp (122,134) (0,-2)).inv.app (S_0_0 : Syn)))]
    erw [←reassoc_of% (lambdaPow_naturality 5 (lambdaPow 2 (Smn 122 134)))]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add D'.shiftCoherence 2 5 7 (by decide) (Smn 122 134)]
    simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv,eqToIso.inv,eqToHom_refl,Category.id_comp,Category.assoc]
    rfl
  have nu_target_lambda_right_five (D' : AdamsComparison H M' Syn)
      (etaAux : BiHom 3 4 (S_0_0 : Syn))
      (c : BiHom 122 132 (S_0_0 : Syn)) :
      sphereAction etaAux (lambdaMultiply 5 c) = lambdaMultiply 5 (sphereAction etaAux c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (3,4) (122,132) (0,-5)
      (125,136) (122,127) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat,
      Int.reduceSub, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 5
      ((SyntheticCategory.biShift_comp (3,4) (122,132)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 5
      ((SyntheticCategory.biShift (122,132)).map etaAux))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (122,132) (0,-5)).inv.naturality etaAux)]
    rfl
  have nu_target_lambda_four_product (D' : AdamsComparison H M' Syn)
      (nu : BiHom 3 4 (S_0_0 : Syn)) (a : BiHom 122 132 (S_0_0 : Syn)) :
      lambdaMultiply 4 (sphereProduct (lambdaMultiply 1 nu) a)=
        sphereProduct nu (lambdaMultiply 5 a) := by
    change lambdaMultiply 4 (sphereAction (lambdaMultiply 1 nu) a)=sphereAction nu (lambdaMultiply 5 a)
    rw [nu_target_lambda_left D',nu_target_four_one D',nu_target_lambda_right_five D']
  have vanishes_mod_lambda_iff_multiple
      (n : ℕ) {X : Syn} (m w : ℤ) (z : BiHom m (w-(n:ℤ)) X) :
      VanishesModLambda n z ↔ ∃ b : BiHom m w X, lambdaMultiply n b=z := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(n:ℤ))
    let e : F.obj (Smn m w : Syn) ≅ Smn m (w-(n:ℤ)) :=
      (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).app S_0_0 ≪≫
        eqToIso (by congr 1; simp [sub_eq_add_neg])
    have he (b : BiHom m w X) : lambdaMultiply n b=e.inv≫F.map b≫lambdaPow n X := by
      have he' : lambdaMultiply n b=e.inv≫lambdaPow n (Smn m w)≫b := by
        unfold lambdaMultiply
        change eqToHom (by congr 1; simp) ≫
          (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0 ≫
          lambdaPow n (Smn m w) ≫ b =
          (eqToHom (by congr 1; simp) ≫
            (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0) ≫
          lambdaPow n (Smn m w) ≫ b
        exact (Category.assoc _ _ _).symm
      rw [he',←lambdaPow_naturality n b]
    constructor
    · intro hz
      obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors n z).mp hz
      let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).preimage (e.hom≫a)
      have hb : F.map b=e.hom≫a :=
        (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).map_preimage _
      refine ⟨b,?_⟩
      rw [he,hb]
      simp only [Category.assoc,e.inv_hom_id_assoc]
      exact ha
    · rintro ⟨b,rfl⟩
      apply (vanishesModLambda_iff_factors n (lambdaMultiply n b)).mpr
      exact ⟨e.inv≫F.map b,by rw [Category.assoc,←he]⟩
  have lambda_four_one (D' : AdamsComparison H M' Syn)
      (c : BiHom 125 140 (S_0_0 : Syn)) :
      lambdaMultiply 4 (lambdaMultiply 1 c) = lambdaMultiply 5 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,140) (0,-1) (0,-4)
      (125,139) (0,-5) (125,135) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
    erw [← reassoc_of% (lambdaPow_naturality 4
      ((SyntheticCategory.biShift_comp (125,140) (0,-1)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 4 (lambdaPow 1 (Smn 125 140)))]
    erw [← Category.assoc, ha]
    erw [lambdaPow_add D'.shiftCoherence 1 4 5 (by decide) (Smn 125 140)]
    simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.assoc]
    rfl
  have nu_target_sphere_four_split
      (BHS : SyntheticComparisonTheorems D') (T : E2 H SphereSpectrum 14 139)
      (hT : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (14,139) T)
      (a : BiHom 125 135 (S_0_0 : Syn))
      (ha : Detects D'.sphereConvergence (14,139,135) (D'.sphereE2 14 139 4 T) a) :
      ∃ t : BiHom 125 139 (S_0_0 : Syn),
        D'.sphereFirstQuotient 14 139 (quotientClass 1 t)=T ∧ lambdaMultiply 4 t=a := by
    obtain ⟨t00,ht0⟩ := sphere_permanent_first_quotient_lift BHS 14 139 T hT
    let t0 : BiHom 125 139 (S_0_0 : Syn) := t00
    change D'.sphereFirstQuotient 14 139 (quotientClass 1 t0)=T at ht0
    let a0 : BiHom 125 135 (S_0_0 : Syn) := lambdaMultiply 4 t0
    have ha0 : Detects D'.sphereConvergence (14,139,135) (D'.sphereE2 14 139 4 T) a0 := by
      have h := D'.comparisonCompatible.homotopy_lambda 14 139 4 t0
      rw [ht0] at h
      exact h
    have hdiff : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 (a-a0) :=
      detects_sub_filtration D'.sphereConvergence (14,139,135) ha ha0
    have hnu := map_filtration D'.nu.unitIso.inv (a-a0) hdiff
    have hlam := BHS.filtration_lambda .sphere 125 135 15 (by omega) ((a-a0)≫D'.nu.unitIso.inv)
    change FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 ((a-a0)≫D'.nu.unitIso.inv) ↔
      ∃ b : BiHom 125 140 (D'.nu.functor.obj SphereSpectrum), lambdaMultiply 5 b=(a-a0)≫D'.nu.unitIso.inv at hlam
    obtain ⟨b,hb⟩ := hlam.mp hnu
    let c : BiHom 125 140 (S_0_0 : Syn) := b≫D'.nu.unitIso.hom
    have hc : lambdaMultiply 5 c=a-a0 := by
      simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
        congrArg (fun x=>x≫D'.nu.unitIso.hom) hb
    let lc : BiHom 125 139 (S_0_0 : Syn) := lambdaMultiply 1 c
    have hq : quotientClass 1 lc=0 := by
      exact (vanishes_mod_lambda_iff_multiple 1 125 140 lc).mpr ⟨c,rfl⟩
    refine ⟨t0+lc,?_,?_⟩
    · change D'.sphereFirstQuotient 14 139 ((t0+lc)≫XModLambdaN.incl _ 1)=T
      rw [Preadditive.add_comp,map_add]
      change D'.sphereFirstQuotient 14 139 (quotientClass 1 t0)+
        D'.sphereFirstQuotient 14 139 (quotientClass 1 lc)=T
      rw [ht0,hq,map_zero,add_zero]
    · let c7 : BiHom 125 135 (S_0_0 : Syn) := lambdaMultiply 5 c
      have he1 : (show BiHom 125 135 (S_0_0 : Syn) from lambdaMultiply 4 lc)=c7 :=
        lambda_four_one D' c
      have he : (show BiHom 125 135 (S_0_0 : Syn) from lambdaMultiply 4 (t0+lc))=a0+c7 := by
        calc
          _ = a0+(show BiHom 125 135 (S_0_0 : Syn) from lambdaMultiply 4 lc) := by
            simp only [a0,lambdaMultiply,Preadditive.comp_add]
          _ = a0+c7 := by rw [he1]
      change (show BiHom 125 135 (S_0_0 : Syn) from lambdaMultiply 4 (t0+lc))=a
      rw [he]
      have hc7 : c7=a-a0 := hc
      rw [hc7]
      abel
  have target_page_six_frame (I' : AdamsComputationTheorems D' L' G) :
      (∃ a : (sequence D' .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D' .sphere) 6 (14,139) (L'.target M') a ∧
        ∀ y : (sequence D' .sphere).Page 6 (14,139), y=0 ∨ y=a) ∧
      ReachesPage (sequence D' .sphere) 1000 (14,139) (L'.target M') := by
    classical

    have represents_unique
        {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a b : E.Page r p}
        (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
      obtain ⟨hr, z, hz, hza⟩ := ha
      obtain ⟨_, z', hz', hzb⟩ := hb
      let D' := E.ssData p
      let n : WithTop ℕ := ↑(2 - E.r₀).toNat
      let m : WithTop ℕ := ↑(r - E.r₀).toNat
      have hnm : n ≤ m := by
        dsimp only [n, m]
        exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
      apply sub_eq_zero.mp
      rw [← hza, ← hzb, ← map_sub]
      apply (subobject_cokernel_π_eq_zero_iff (D'.B m) (D'.Z m) (D'.B_le_Z m) _).mpr
      have heq : D'.pageπ n ((Subobject.ofLE _ _ (D'.Z_anti hnm)) (z-z')) = 0 := by
        change (Subobject.ofLE _ _ (D'.Z_anti hnm) ≫ D'.pageπ n) (z-z') = 0
        rw [map_sub, hz, hz', sub_self]
      have hh := (subobject_cokernel_π_eq_zero_iff (D'.B n) (D'.Z n) (D'.B_le_Z n) _).mp heq
      have he : (D'.Z n).arrow ((Subobject.ofLE _ _ (D'.Z_anti hnm)) (z-z')) =
          (D'.Z m).arrow (z-z') := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D'.Z_anti hnm)) _
      rw [he] at hh
      exact (ModuleCat.subobjectModule D'.V).monotone (D'.B_mono hnm) hh

    have represents_d_zero_of_later
        {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
        {a : E.Page r p} (ha : RepresentsOnPage E r p x a)
        (ht : ReachesPage E t p x) : E.d r p a = 0 := by
      obtain ⟨b, ht2, z, hz, _⟩ := ht
      let D' := E.ssData p
      let nt : WithTop ℕ := ↑(t-E.r₀).toNat
      let nr : WithTop ℕ := ↑(r-E.r₀).toNat
      let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
      have hrs : nr ≤ ns := by
        dsimp only [nr, ns]
        exact_mod_cast (show (r-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
      have hst : ns ≤ nt := by
        dsimp only [ns, nt]
        exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
      let zr := (Subobject.ofLE (D'.Z nt) (D'.Z nr) (D'.Z_anti (hrs.trans hst))) z
      have hrep : RepresentsOnPage E r p x (D'.pageπ nr zr) := by
        refine ⟨ha.1, zr, ?_, rfl⟩
        dsimp only [zr]
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
        exact hz
      rw [represents_unique ha hrep]
      change D'.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
      rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
      refine ⟨(Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z, ?_⟩
      change (Subobject.ofLE (D'.Z ns) (D'.Z nr) (D'.Z_anti hrs) ≫ D'.pageπ nr)
        ((Subobject.ofLE (D'.Z nt) (D'.Z ns) (D'.Z_anti hst)) z) = D'.pageπ nr zr
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      rfl

    have represents_before
        {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p : ℤ × ℤ}
        {x : E.Page 2 p} {xt : E.Page t p}
        (hr : 2 ≤ r) (hrt : r ≤ t) (ht : RepresentsOnPage E t p x xt) :
        ∃ xr, RepresentsOnPage E r p x xr := by
      obtain ⟨_, z, hz, _⟩ := ht
      let D' := E.ssData p
      have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(t-E.r₀).toNat := by
        exact_mod_cast (show (r-E.r₀).toNat ≤ (t-E.r₀).toNat by omega)
      let zr := (Subobject.ofLE (D'.Z ↑(t-E.r₀).toNat) (D'.Z ↑(r-E.r₀).toNat) (D'.Z_anti hrt')) z
      refine ⟨D'.pageπ _ zr, hr, zr, ?_, rfl⟩
      dsimp only [zr]
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      exact hz

    have differential_target_later_zero
        {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
        (hr0 : E.r₀ ≤ r) (hrt : r < t)
        (h : HasDifferential E r p q x y) : RepresentsOnPage E t q y 0 := by
      obtain ⟨rfl, xr, yr, hx, hy, hd⟩ := h
      simp only [eqToHom_refl, Category.comp_id] at hd
      obtain ⟨hr, z, hz2, hzr⟩ := hy
      let A := E.ssData (p + E.diffDeg r)
      let n : ℕ := (r-E.r₀).toNat
      let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
      let m : WithTop ℕ := ↑(t-E.r₀).toNat
      have hnm : (↑(n+1) : WithTop ℕ) ≤ m := by
        dsimp only [n,m]
        exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
      have hn0 : n₀ ≤ ↑n := by
        dsimp only [n₀,n]
        exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
      have hn1 : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
      have hdmem : yr ∈ LinearMap.range (E.d r p).hom := ⟨xr, hd⟩
      rw [← subobjectModule_image, E.B_succ r p hr0, subobjectModule_image] at hdmem
      obtain ⟨b, hb⟩ := hdmem
      let j := Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑n)
        ((A.B_le_Z _).trans (A.Z_anti hn1))
      have hb' : A.pageπ ↑n (j b) = yr := hb
      have hdif : A.pageπ ↑n (z-j b) = 0 := by rw [map_sub, hzr, hb', sub_self]
      have hmem := (subobject_cokernel_π_eq_zero_iff (A.B ↑n) (A.Z ↑n) (A.B_le_Z _) _).mp hdif
      have hmem' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono hn1) hmem
      have hj : (A.Z ↑n).arrow (j b) ∈ (ModuleCat.subobjectModule A.V) (A.B ↑(n+1)) := by
        change (j ≫ (A.Z ↑n).arrow) b ∈ _
        dsimp only [j]
        rw [Subobject.ofLE_arrow]
        exact ⟨b,rfl⟩
      have hzmem := ((ModuleCat.subobjectModule A.V) (A.B ↑(n+1))).add_mem hmem' hj
      rw [map_sub, sub_add_cancel] at hzmem
      obtain ⟨b', hb'⟩ := hzmem
      let i := Subobject.ofLE (A.B ↑(n+1)) (A.Z m) ((A.B_mono hnm).trans (A.B_le_Z _))
      refine ⟨by omega, i b', ?_, ?_⟩
      · have he : (Subobject.ofLE (A.Z m) (A.Z n₀) (A.Z_anti (hn0.trans (hn1.trans hnm))))
            (i b') = (Subobject.ofLE (A.Z ↑n) (A.Z n₀) (A.Z_anti hn0)) z := by
          apply (ModuleCat.mono_iff_injective (A.Z n₀).arrow).mp inferInstance
          change (i ≫ Subobject.ofLE (A.Z m) (A.Z n₀) _ ≫ (A.Z n₀).arrow) b' =
            (Subobject.ofLE (A.Z ↑n) (A.Z n₀) _ ≫ (A.Z n₀).arrow) z
          simpa only [Category.assoc, i, Subobject.ofLE_arrow] using hb'
        exact (congrArg (fun v => A.pageπ n₀ v) he).trans hz2
      · apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
        change (i ≫ (A.Z m).arrow) b' ∈ _
        dsimp only [i]
        rw [Subobject.ofLE_arrow]
        exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) ⟨b',rfl⟩

    have represents_add_tail
        {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
        {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
        (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
        RepresentsOnPage E r p (x+y) (a+b) := by
      obtain ⟨hr,z,hz,ha⟩ := hx
      obtain ⟨_,w,hw,hb⟩ := hy
      exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩

    have t_label (I' : AdamsComputationTheorems D' L' G) :
        I'.interpretation.sphere 14 139 T = I'.interpretation.basis .sphere 14 139 1 := by
      have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl
      have hc := I'.monomials _ hmem rfl
      obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
      have heq : T=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
        have hs : "1,1,7,1,275,1" ≠ "" := by decide
        have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
          have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,if_neg hs,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
      rw [heq]
      exact he

    have t_page6_frame (I' : AdamsComputationTheorems D' L' G) :
        ∃ a : (sequence D' .sphere).Page 6 (14,139),
          RepresentsOnPage (sequence D' .sphere) 6 (14,139) (I'.interpretation.basis .sphere 14 139 1) a ∧
          ∀ y : (sequence D' .sphere).Page 6 (14,139), y=0 ∨ y=a := by
      let E := sequence D' .sphere
      have h342 : ReachesPage E 1000 (14,139) (I'.interpretation.basis .sphere 14 139 1) := by
        have hrow := I'.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
          exact List.mem_of_getElem? (l := Raw.claims) (i := 342) rfl)
        dsimp only [AdamsStatement] at hrow
        obtain ⟨x,hx,hd⟩ := hrow
        change ReachesPage E 1000 (14,139) x at hd
        have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
        simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
          List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
        rw [←hx] at hd
        simpa only [add_assoc] using hd
      have h341 : HasDifferential E 2 (12,138) (14,139)
          (I'.interpretation.basis .sphere 12 138 1) (I'.interpretation.basis .sphere 14 139 2) := by
        have hrow := I'.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
          exact List.mem_of_getElem? (l := Raw.claims) (i := 341) rfl)
        dsimp only [AdamsStatement] at hrow
        obtain ⟨x,hx,y,hy,hd⟩ := hrow
        change HasDifferential E 2 (12,138) (14,139) x y at hd
        have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
        have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
        simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
          List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
        rw [←hx,←hy] at hd
        simpa only [add_assoc] using hd
      have h343 : HasDifferential E 2 (14,139) (16,140)
          (I'.interpretation.basis .sphere 14 139 0) (I'.interpretation.basis .sphere 16 140 2) := by
        have hrow := I'.adamsStatements ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
          exact List.mem_of_getElem? (l := Raw.claims) (i := 343) rfl)
        dsimp only [AdamsStatement] at hrow
        obtain ⟨x,hx,y,hy,hd⟩ := hrow
        change HasDifferential E 2 (14,139) (16,140) x y at hd
        have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
        have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
        simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
          List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
        rw [←hx,←hy] at hd
        simpa only [add_assoc] using hd
      obtain ⟨e,he⟩ := I'.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl)
      change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
      change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 14 139 i.val at he
      have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I'.interpretation.basis .sphere 14 139 0 := he 0
      have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I'.interpretation.basis .sphere 14 139 1 := he 1
      have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I'.interpretation.basis .sphere 14 139 2 := he 2
      obtain ⟨f,hf⟩ := I'.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
        exact List.mem_of_getElem? (l := Raw.degrees) (i := 231) rfl)
      change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
      change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 16 140 i.val at hf
      have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I'.interpretation.basis .sphere 16 140 0 := hf 0
      have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I'.interpretation.basis .sphere 16 140 1 := hf 1
      have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I'.interpretation.basis .sphere 16 140 2 := hf 2
      have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I'.interpretation.basis .sphere 16 140 3 := hf 3
      have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I'.interpretation.basis .sphere 16 140 4 := hf 4
      obtain ⟨a1000,ha1000⟩ := h342
      obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤1000) ha1000
      have hz2 : RepresentsOnPage E 6 (14,139) (I'.interpretation.basis .sphere 14 139 2) 0 :=
        differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h341
      have dz {x : E.Page 2 (14,139)} {b : E.Page 6 (14,139)}
          (hb : RepresentsOnPage E 6 (14,139) x b) : E.d 2 (14,139) x=0 := by
        obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hb
        have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<6) hb2 ⟨b,hb⟩
        simpa only [hb2.eq_on_page_two] using hh
      have hd0 : E.d 2 (14,139) (I'.interpretation.basis .sphere 14 139 0)=I'.interpretation.basis .sphere 16 140 2 := h343.eq_on_page_two.2
      have hd1 : E.d 2 (14,139) (I'.interpretation.basis .sphere 14 139 1)=0 := dz ha
      have hd2 : E.d 2 (14,139) (I'.interpretation.basis .sphere 14 139 2)=0 := dz hz2
      refine ⟨a,ha,?_⟩
      intro y
      let A := E.ssData (14,139)
      haveI : Epi (A.pageπ 4) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 4)).mp inferInstance y
      let x := (Subobject.ofLE (A.Z 4) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤4)) ≫ A.pageπ 0) z
      have hxrep : RepresentsOnPage E 6 (14,139) x y := ⟨by decide,z,rfl,hz⟩
      have hx : E.d 2 (14,139) x=0 := dz hxrep
      have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
        apply Finsupp.ext
        intro i
        fin_cases i <;> simp
      have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
        rw [←heq,LinearEquiv.symm_apply_apply]
      generalize hc0 : e x 0=c0 at hxe
      generalize hc1 : e x 1=c1 at hxe
      generalize hc2 : e x 2=c2 at hxe
      fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
      · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
        rw [hxe] at hx hxrep
        left
        apply represents_unique hxrep
        exact RepresentsOnPage.zero (by decide)
      · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hx hxrep
        left
        apply represents_unique hxrep
        rw [he2]
        exact hz2
      · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
        rw [hxe] at hx hxrep
        right
        apply represents_unique hxrep
        rw [he1]
        exact ha
      · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
        rw [hxe] at hx hxrep
        right
        apply represents_unique hxrep
        rw [he1,he2]
        simpa only [add_zero] using represents_add_tail ha hz2
      · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,add_zero] at hxe
        rw [hxe] at hx hxrep
        simp only [he0, hd0] at hx
        have hh := congrArg (fun y=>f y 2) hx
        rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
        norm_num [Finsupp.single_apply] at hh
      · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hx hxrep
        simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
        have hh := congrArg (fun y=>f y 2) hx
        rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
        norm_num [Finsupp.single_apply] at hh
      · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
        try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
        rw [hxe] at hx hxrep
        simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
        have hh := congrArg (fun y=>f y 2) hx
        rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
        norm_num [Finsupp.single_apply] at hh
      · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
        try simp only [map_add] at hxe
        rw [hxe] at hx hxrep
        simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
        have hh := congrArg (fun y=>f y 2) hx
        rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
        norm_num [Finsupp.single_apply] at hh
    obtain ⟨a,ha,hall⟩ := t_page6_frame I'
    have hlabel := (sphere_class_identifications I').2.2
    have hl : L'.target M' = I'.interpretation.basis .sphere 14 139 1 := hlabel.symm.trans (t_label I')
    constructor
    · exact ⟨a,by rw [hl]; exact ha,hall⟩
    let E := sequence D' .sphere
    have h342 : ReachesPage E 1000 (14,139) (I'.interpretation.basis .sphere 14 139 1) := by
      have hrow := I'.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
        exact List.mem_of_getElem? (l := Raw.claims) (i := 342) rfl)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,hd⟩ := hrow
      change ReachesPage E 1000 (14,139) x at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [←hx] at hd
      simpa only [add_assoc] using hd
    rw [hl]
    exact h342
  have target_lambda_zero_3_4 (D' : AdamsComparison H M' Syn) {X : Syn} (a : BiHom 3 4 X) :
      lambdaMultiply 0 a=a := by
    have hc := D'.shiftCoherence.right_unit (3,4) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 3 4 : Syn) := by
      change (biShiftAddIso (3,4) (0,0) (3,4) (by ext <;> simp)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (3,4) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have target_lambda_zero_125_139 (D' : AdamsComparison H M' Syn) {X : Syn} (a : BiHom 125 139 X) :
      lambdaMultiply 0 a=a := by
    have hc := D'.shiftCoherence.right_unit (125,139) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 125 139 : Syn) := by
      change (biShiftAddIso (125,139) (0,0) (125,139) (by ext <;> simp)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (125,139) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (125,139) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have target_first_label_nonzero_detection (BHS : EInftyComparison D')
      (T : E2 H SphereSpectrum 14 139) (ht : T∈permanentCycles H SphereSpectrum (14,139))
      (htn : T≠0) (t : BiHom 125 139 (S_0_0 : Syn))
      (hlt : D'.sphereFirstQuotient 14 139 (quotientClass 1 t)=T) :
      SphereDetected D' 14 139 0 T t := by
    have hd := D'.comparisonCompatible.homotopy_lambda 14 139 0 t
    rw [hlt,target_lambda_zero_125_139 D'] at hd
    refine ⟨hd,?_⟩
    obtain ⟨e,he,_,_,_⟩ := hd
    refine ⟨e,he,?_⟩
    intro he0
    have hn := family_infinity_representative_map D'.nu.unitIso.inv (14,139,139) _ _ he
    have hlabel : familyPageMap D'.family D'.nu.unitIso.inv 2 (14,139,139)
        (D'.sphereE2 14 139 0 T)=targetNuLabel D' .sphere 14 139 0 T :=
      sphere_label_to_nu 0 14 139 T
    rw [hlabel,he0,map_zero] at hn
    have hz := (BHS.labels.2 .sphere (14,139) 0 ⟨T,ht⟩ 0).mp hn
    rw [map_zero] at hz
    have hh := (NestedQuotient.projection_eq_zero (⟨T,ht⟩ : permanentCycles H SphereSpectrum (14,139))).mp hz.symm
    change T∈boundaries H SphereSpectrum 1 (14,139) at hh
    rw [boundaries_one] at hh
    exact htn hh
  obtain ⟨p,q,bp,bq,hp,hq,hrem⟩ := nu_target_pq_lift_peel I' BHS SF a0 ha0
  let a : BiHom 122 132 (S_0_0 : Syn) :=
    (if bp then (show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 1 p) else 0)+
    (if bq then (show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 2 q) else 0)
  let v : BiHom 125 135 (S_0_0 : Syn) := sphereProduct (lambdaMultiply 1 nu) a
  let b : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) := quotientClass 9 (lambdaMultiply 5 a)
  have hb : b=
      (if bp then (show BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) from quotientClass 9 (lambdaMultiply 6 p)) else 0)+
      (if bq then (show BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) from quotientClass 9 (lambdaMultiply 7 q)) else 0) := by
    let f : BiHom 122 132 (S_0_0 : Syn) →+ BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9) :=
      { toFun := fun c=>quotientClass 9 (lambdaMultiply 5 c)
        map_zero' := by simp only [lambdaMultiply,quotientClass,CategoryTheory.Limits.comp_zero,CategoryTheory.Limits.zero_comp]
        map_add' := by intros; simp only [lambdaMultiply,quotientClass,Preadditive.comp_add,Preadditive.add_comp] }
    have hp5 : f (lambdaMultiply 1 p)=quotientClass 9 (lambdaMultiply 6 p) :=
      congrArg (quotientClass 9) (nu_target_five_one D' p)
    have hq5 : f (lambdaMultiply 2 q)=quotientClass 9 (lambdaMultiply 7 q) :=
      congrArg (quotientClass 9) (nu_target_five_two D' q)
    change f ((if bp then (show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 1 p) else 0)+
      (if bq then (show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 2 q) else 0))=_
    rw [map_add]
    cases bp <;> cases bq <;> simp only [Bool.false_eq_true,↓reduceIte,map_zero,hp5,hq5]
  rw [←hb] at hrem
  have hnud := D'.comparisonCompatible.homotopy_lambda 1 4 0 nu
  rw [hnu,target_lambda_zero_3_4 D'] at hnud
  have hr := nu_target_remainder_zero BHS.eInfty A ab nu hnud hprod (a0-b) hrem
  have hab : sphereAction nu a0=sphereAction nu b := by
    change _ ≫ _ ≫ (a0-b)=0 at hr
    simp only [Preadditive.comp_sub,sub_eq_zero] at hr
    exact hr
  have hvq : quotientClass 9 (lambdaMultiply 4 v)=sphereAction nu b := by
    dsimp only [v,b]
    rw [nu_target_lambda_four_product D']
    simp only [sphereProduct,sphereAction,quotientClass,Category.assoc,Nat.cast_ofNat,Int.reduceSub]
  have hvn : quotientClass 9 (lambdaMultiply 4 v)≠0 := by
    rw [hvq,←hab]
    exact hne
  obtain ⟨hpb,hqb⟩ := nu_target_pq_boundaries I' SF
  obtain ⟨hpf,hqf⟩ := nu_target_sphere_products_filtration BHS.eInfty nu hnu
    (I'.interpretation.sphere 11 133 P) (I'.interpretation.sphere 12 134 Q) hpb hqb SF.e5_stem125_af13 p q hp hq
  have hvf : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 14 v := by
    cases bp <;> cases bq
    · refine ⟨0,?_⟩
      simp only [v,a,Bool.false_eq_true,↓reduceIte,add_zero,sphereProduct,
        CategoryTheory.Limits.comp_zero,map_zero]
    · simpa only [v,a,Bool.false_eq_true,↓reduceIte,zero_add] using hqf
    · simpa only [v,a,Bool.false_eq_true,↓reduceIte,add_zero] using hpf
    · obtain ⟨zp,hzp⟩ := hpf
      obtain ⟨zq,hzq⟩ := hqf
      let zp' : BiHom 125 135 (adamsTower (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn) 14) := zp
      let zq' : BiHom 125 135 (adamsTower (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn) 14) := zq
      refine ⟨zp'+zq',?_⟩
      change (zp'+zq') ≫ _=sphereProduct (lambdaMultiply 1 nu)
        ((show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 1 p)+(show BiHom 122 132 (S_0_0 : Syn) from lambdaMultiply 2 q))
      change zp' ≫ _=sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 1 p) at hzp
      change zq' ≫ _=sphereProduct (lambdaMultiply 1 nu) (lambdaMultiply 2 q) at hzq
      rw [Preadditive.add_comp,hzp,hzq]
      simp only [sphereProduct,Preadditive.comp_add,Nat.cast_ofNat,Int.natCast_one,Int.reduceSub]
  have hl := (sphere_class_identifications I').2.2
  have ht : L'.target M'∈permanentCycles H SphereSpectrum (14,139) := by
    rw [←hl]
    exact SF.t_permanent_cycle
  obtain ⟨hf,_⟩ := target_page_six_frame I'
  have hdet := nu_target_sphere_detected BHS.eInfty (L'.target M') ht hf v hvf hvn
  obtain ⟨t,hlt,hltv⟩ := nu_target_sphere_four_split BHS (L'.target M') ht v hdet
  have htn : L'.target M'≠0 := by
    intro hz
    apply SF.t_not_h0_multiple
    refine ⟨0,?_⟩
    rw [hl,hz]
    simp only [Sphere.Internal.product,map_zero]
  exact ⟨t,a,target_first_label_nonzero_detection BHS.eInfty (L'.target M') ht htn t hlt,hltv.symm⟩

private theorem nu_target_h0_af13_image_boundary_two
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I' : AdamsComputationTheorems D' L' G)
    : ∀ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M' (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M' 0) a ∈ boundaries H SphereSpectrum 2 (14,139) := by
  have differential_target_later_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)} {r : ℤ} {p : ℤ×ℤ} {t : ℤ} {q : ℤ×ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
      (hr0 : E.r₀ ≤ r) (hrt : r < t)
      (h : KIP126.SpectralSequence.HasDifferential E r p q x y) : KIP126.SpectralSequence.RepresentsOnPage E t q y 0 := by
    exact KIP126.SpectralSequence.FinitePageCalculus.differential_target_later_zero hr0 hrt h
  classical
  have expand {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
      (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (a : A) :
      a=∑ i : Fin N, if (e a) i=0 then 0 else e.symm (Finsupp.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext i
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · generalize (e a) i=b
      fin_cases b <;> simp
    · intro j hj hji
      by_cases hc : (e a) j=0
      · simp [hc]
      · simp [hc,hji]
    · simp
  have negself (x : KIP126.LinE2.E2) : -x=x := by
    exact RelationCertificates.pq_neg_eq_self x
  let E := sequence D' .sphere
  have rel0 : (generator ⟨0,by decide⟩)*(generator ⟨24,by decide⟩)=0 := by
    exact RelationCertificates.h0_obstruction_rel0
  have rel1 : (generator ⟨0,by decide⟩)*(generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩)=(generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^5)*(generator ⟨391,by decide⟩)=0 := by
    exact RelationCertificates.h0_obstruction_rel2
  have rel3 : (generator ⟨0,by decide⟩^6)*(generator ⟨375,by decide⟩)=0 := by
    exact RelationCertificates.h0_obstruction_rel3
  obtain ⟨e13_138,he13_138⟩ := I'.basis ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 209) rfl)
  change E2 H SphereSpectrum 13 138 ≃ₗ[ℤ] (Fin 5 →₀ F2) at e13_138
  change ∀i : Fin 5, e13_138.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 13 138 i.val at he13_138
  obtain ⟨e14_139,he14_139⟩ := I'.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl)
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 14 139 i.val at he14_139
  have hcsv := I'.monomials ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 209) rfl) rfl
  choose z hz he using hcsv
  change Fin 5 → E2At 13 138 at z
  change ∀ i : Fin 5, I'.interpretation.sphere 13 138 (z i) = I'.interpretation.basis .sphere 13 138 i.val at he
  have mon0 : projection (monomialOfString "24,1,190,1") = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_mon0
  have zv0 : (z (0 : Fin 5)).val = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := by
    rw [hz]
    exact mon0
  have mon1 : projection (monomialOfString "3,1,335,1") = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_mon1
  have zv1 : (z (1 : Fin 5)).val = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := by
    rw [hz]
    exact mon1
  have mon2 : projection (monomialOfString "0,1,425,1") = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_mon2
  have zv2 : (z (2 : Fin 5)).val = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := by
    rw [hz]
    exact mon2
  have mon3 : projection (monomialOfString "0,4,391,1") = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_mon3
  have zv3 : (z (3 : Fin 5)).val = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := by
    rw [hz]
    exact mon3
  have mon4 : projection (monomialOfString "0,5,375,1") = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_mon4
  have zv4 : (z (4 : Fin 5)).val = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := by
    rw [hz]
    exact mon4
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_monT
  have targetCSV := I'.monomials ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl) rfl
  have labelT : I'.interpretation.sphere 14 139 T = I'.interpretation.basis .sphere 14 139 1 := by
    obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
    have hyT : T=y := by
      apply Subtype.ext
      rw [hy]
      change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
      rw [monT]
      exact (mul_assoc _ _ _).symm
    rw [hyT]
    exact heq
  let f : E2 H SphereSpectrum 13 138 →+ E2 H SphereSpectrum 14 139 :=
    { toFun := fun a => Sphere.Internal.product H M' (s:=1) (t:=1) (s':=13) (t':=138)
        (Sphere.Internal.hi H M' 0) a
      map_add' := by
        intro a b
        simp only [Sphere.Internal.product,map_add]
      map_zero' := by
        simp only [Sphere.Internal.product,map_zero] }
  have hf (a : E2 H SphereSpectrum 13 138) : f a = Sphere.Internal.product H M'
      (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M' 0) a := rfl
  have hprod (i : Fin 5) : f (I'.interpretation.basis .sphere 13 138 i.val) =
      I'.interpretation.sphere 14 139 (mulAt (dataH0) (z i)) := by
    rw [←he i,hf,←I'.distinguishedClasses.h0]
    exact (I'.products ⟨1,1,13,138⟩ (by simp [Raw.products]) (dataH0) (z i)).symm
  obtain ⟨y2,hy2,hey2⟩ := targetCSV (2 : Fin 3)
  have monTarget2 : projection (monomialOfString "0,2,425,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := by
    exact RelationCertificates.h0_obstruction_monTarget2
  have mul0 : mulAt dataH0 (z (0 : Fin 5))=0 := by
    apply Subtype.ext
    change generator ⟨0,by decide⟩*(z (0 : Fin 5)).val=0
    rw [zv0,←mul_assoc,rel0,zero_mul]
  have mul1 : mulAt dataH0 (z (1 : Fin 5))=y2 := by
    apply Subtype.ext
    change generator ⟨0,by decide⟩*(z (1 : Fin 5)).val=y2.val
    rw [zv1,hy2]
    change _=projection (monomialOfString "0,2,425,1")
    rw [monTarget2]
    simpa only [mul_assoc] using rel1
  have mul2 : mulAt dataH0 (z (2 : Fin 5))=y2 := by
    apply Subtype.ext
    change generator ⟨0,by decide⟩*(z (2 : Fin 5)).val=y2.val
    rw [zv2,hy2]
    change _=projection (monomialOfString "0,2,425,1")
    rw [monTarget2]
    ring
  have mul3 : mulAt dataH0 (z (3 : Fin 5))=0 := by
    apply Subtype.ext
    change generator ⟨0,by decide⟩*(z (3 : Fin 5)).val=0
    rw [zv3]
    calc
      _=generator ⟨0,by decide⟩^5*generator ⟨391,by decide⟩ := by ring
      _=0 := rel2
  have mul4 : mulAt dataH0 (z (4 : Fin 5))=0 := by
    apply Subtype.ext
    change generator ⟨0,by decide⟩*(z (4 : Fin 5)).val=0
    rw [zv4]
    calc
      _=generator ⟨0,by decide⟩^6*generator ⟨375,by decide⟩ := by ring
      _=0 := rel3
  have h341 : HasDifferential E 2 (12,138) (14,139)
      (I'.interpretation.basis .sphere 12 138 1) (I'.interpretation.basis .sphere 14 139 2) := by
    have hrow := I'.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 341) rfl)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,138) (14,139) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have hz2 : RepresentsOnPage E 3 (14,139) (I'.interpretation.basis .sphere 14 139 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h341
  have hb2 : I'.interpretation.basis .sphere 14 139 2 ∈ boundaries H SphereSpectrum 2 (14,139) := by
    let P := E.ssData (14,139)
    obtain ⟨_,z,hz,hzero⟩ := hz2
    change P.pageπ 1 z=0 at hzero
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B 1) (P.Z 1) (P.B_le_Z 1)) z).mp hzero
    change ∃ b, (PageRepresentatives.boundaryMap H SphereSpectrum (1 : WithTop ℕ) (14,139)).hom b=_
    refine ⟨b,?_⟩
    change (Subobject.ofLE (P.B 1) (P.Z 0) _ ≫ P.pageπ 0) b=_
    rw [←hz,←hb]
    change _=(Subobject.ofLE (P.Z 1) (P.Z 0) _ ≫ P.pageπ 0)
      ((Subobject.ofLE (P.B 1) (P.Z 1) (P.B_le_Z 1)) b)
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  intro a
  change f a ∈ boundaries H SphereSpectrum 2 (14,139)
  rw [expand e13_138 a,map_sum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hc : (e13_138 a) i=0
  · simp only [hc,if_true,map_zero]
    exact Submodule.zero_mem _
  · simp only [hc,if_false]
    rw [he13_138,hprod]
    fin_cases i
    · change I'.interpretation.sphere 14 139 (mulAt dataH0 (z (0:Fin 5)))∈boundaries H SphereSpectrum 2 (14,139)
      rw [mul0,map_zero]; exact Submodule.zero_mem _
    · change I'.interpretation.sphere 14 139 (mulAt dataH0 (z (1:Fin 5)))∈boundaries H SphereSpectrum 2 (14,139)
      rw [mul1,hey2]; exact hb2
    · change I'.interpretation.sphere 14 139 (mulAt dataH0 (z (2:Fin 5)))∈boundaries H SphereSpectrum 2 (14,139)
      rw [mul2,hey2]; exact hb2
    · change I'.interpretation.sphere 14 139 (mulAt dataH0 (z (3:Fin 5)))∈boundaries H SphereSpectrum 2 (14,139)
      rw [mul3,map_zero]; exact Submodule.zero_mem _
    · change I'.interpretation.sphere 14 139 (mulAt dataH0 (z (4:Fin 5)))∈boundaries H SphereSpectrum 2 (14,139)
      rw [mul4,map_zero]; exact Submodule.zero_mem _

private theorem nu_target_h2_af13_product_zero
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I' : AdamsComputationTheorems D' L' G)
    : ∀ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M' (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M' 2) a = 0 := by
  classical
  have expand {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
      (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (a : A) :
      a=∑ i : Fin N, if (e a) i=0 then 0 else e.symm (Finsupp.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext i
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · generalize (e a) i=b
      fin_cases b <;> simp
    · intro j hj hji
      by_cases hc : (e a) j=0
      · simp [hc]
      · simp [hc,hji]
    · simp
  have negself (x : KIP126.LinE2.E2) : -x=x := by
    exact RelationCertificates.pq_neg_eq_self x
  let E := sequence D' .sphere
  have rel0 : (generator ⟨2,by decide⟩)*(generator ⟨407,by decide⟩)=0 := by
    exact RelationCertificates.h2_obstruction_rel0
  have rel1 : (generator ⟨2,by decide⟩)*(generator ⟨79,by decide⟩)=(generator ⟨0,by decide⟩)*(generator ⟨89,by decide⟩) := by
    exact RelationCertificates.h2_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^3)*(generator ⟨89,by decide⟩)=0 := by
    exact RelationCertificates.h2_obstruction_rel2
  obtain ⟨e13_135,he13_135⟩ := I'.basis ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 206) rfl)
  change E2 H SphereSpectrum 13 135 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_135
  change ∀i : Fin 3, e13_135.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 13 135 i.val at he13_135
  obtain ⟨e14_139,he14_139⟩ := I'.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl)
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 14 139 i.val at he14_139
  have hcsv := I'.monomials ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 206) rfl) rfl
  choose z hz he using hcsv
  change Fin 3 → E2At 13 135 at z
  change ∀ i : Fin 3, I'.interpretation.sphere 13 135 (z i) = I'.interpretation.basis .sphere 13 135 i.val at he
  have mon0 : projection (monomialOfString "407,1") = (generator ⟨407,by decide⟩) := by
    exact RelationCertificates.h2_obstruction_mon0
  have zv0 : (z (0 : Fin 3)).val = (generator ⟨407,by decide⟩) := by
    rw [hz]
    exact mon0
  have mon1 : projection (monomialOfString "1,2,351,1") = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := by
    exact RelationCertificates.h2_obstruction_mon1
  have zv1 : (z (1 : Fin 3)).val = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := by
    rw [hz]
    exact mon1
  have mon2 : projection (monomialOfString "0,2,69,1,79,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := by
    exact RelationCertificates.h2_obstruction_mon2
  have zv2 : (z (2 : Fin 3)).val = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := by
    rw [hz]
    exact mon2
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := by
    exact RelationCertificates.h2_obstruction_monT
  have targetCSV := I'.monomials ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl) rfl
  have labelT : I'.interpretation.sphere 14 139 T = I'.interpretation.basis .sphere 14 139 1 := by
    obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
    have hyT : T=y := by
      apply Subtype.ext
      rw [hy]
      change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
      rw [monT]
      exact (mul_assoc _ _ _).symm
    rw [hyT]
    exact heq
  let f : E2 H SphereSpectrum 13 135 →+ E2 H SphereSpectrum 14 139 :=
    { toFun := fun a => Sphere.Internal.product H M' (s:=1) (t:=4) (s':=13) (t':=135)
        (Sphere.Internal.hi H M' 2) a
      map_add' := by
        intro a b
        simp only [Sphere.Internal.product,map_add]
      map_zero' := by
        simp only [Sphere.Internal.product,map_zero] }
  have hf (a : E2 H SphereSpectrum 13 135) : f a = Sphere.Internal.product H M'
      (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M' 2) a := rfl
  have hprod (i : Fin 3) : f (I'.interpretation.basis .sphere 13 135 i.val) =
      I'.interpretation.sphere 14 139 (mulAt (atom .h2) (z i)) := by
    rw [←he i,hf,←I'.distinguishedClasses.h2]
    exact (I'.products ⟨1,4,13,135⟩ (by simp [Raw.products]) (atom .h2) (z i)).symm
  have mul0 : mulAt (atom .h2) (z (0 : Fin 3))=0 := by
    apply Subtype.ext
    change generator ⟨2,by decide⟩*(z (0 : Fin 3)).val=0
    rw [zv0]
    exact rel0
  have mul1 : mulAt (atom .h2) (z (1 : Fin 3))=0 := by
    apply Subtype.ext
    change generator ⟨2,by decide⟩*(z (1 : Fin 3)).val=0
    rw [zv1]
    have h12 : generator ⟨1,by decide⟩*generator ⟨2,by decide⟩=0 := h1_mul_h2_eq_zero
    calc
      _=(generator ⟨1,by decide⟩*generator ⟨2,by decide⟩)*
        (generator ⟨1,by decide⟩*generator ⟨351,by decide⟩) := by ring
      _=0 := by rw [h12,zero_mul]
  have mul2 : mulAt (atom .h2) (z (2 : Fin 3))=0 := by
    apply Subtype.ext
    change generator ⟨2,by decide⟩*(z (2 : Fin 3)).val=0
    rw [zv2]
    calc
      _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
        (generator ⟨2,by decide⟩*generator ⟨79,by decide⟩) := by ring
      _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
        (generator ⟨0,by decide⟩*generator ⟨89,by decide⟩) := by rw [rel1]
      _=generator ⟨69,by decide⟩*(generator ⟨0,by decide⟩^3*generator ⟨89,by decide⟩) := by ring
      _=0 := by rw [rel2,mul_zero]
  intro a
  change f a=0
  rw [expand e13_135 a,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hc : (e13_135 a) i=0
  · simp only [hc,if_true,map_zero]
  · simp only [hc,if_false]
    rw [he13_135,hprod]
    fin_cases i
    · change I'.interpretation.sphere 14 139 (mulAt (atom .h2) (z (0:Fin 3)))=0
      rw [mul0,map_zero]
    · change I'.interpretation.sphere 14 139 (mulAt (atom .h2) (z (1:Fin 3)))=0
      rw [mul1,map_zero]
    · change I'.interpretation.sphere 14 139 (mulAt (atom .h2) (z (2:Fin 3)))=0
      rw [mul2,map_zero]

private theorem nu_target_full_of_nonzero
    (I' : AdamsComputationTheorems D' L' G) (BHS : SyntheticComparisonTheorems D') (SF : Derived.SphereFacts I'.interpretation)
    (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
    (nu : BiHom 3 4 (S_0_0 : Syn))
    (hnu : D'.sphereFirstQuotient 1 4 (quotientClass 1 nu)=Sphere.Internal.hi H M' 2)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hh0 : D'.sphereFirstQuotient 1 1 (quotientClass 1 h0)=Sphere.Internal.hi H M' 0)
    (hlambda_h0 : lambdaMultiply 1 h0=syntheticTwo)
    (hext : NuExtension9 D' (I'.interpretation.sphere 8 130 X) (I'.interpretation.sphere 11 136 Y) nu)
    (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
    (hy0 : Detects (D'.quotientConvergence 9 (by decide)) (11,136,132)
      (D'.quotientLabel 9 11 136 4 (I'.interpretation.sphere 11 136 Y)) y0)
    (hweaknonzero : lambdaMultiply 2 (sphereAction h0 y0)≠0) :
    TargetNuDivisible D' (L'.target M') nu := by
  have boundary_of_zero_representative
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
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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
  have family_page_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D'.family f r i ≫ familyPageMap D'.family g r i = familyPageMap D'.family (f ≫ g) r i := by
    rw [family_map_data,family_map_data,family_map_data,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map
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
  have sphere_quotient_label_to_nu (q k : ℕ) (s t : ℤ)
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
          ConcreteCategory.congr_hom (family_page_comp (SyntheticCategory.biShift_zero.hom.app _ ≫ D'.nu.unitIso.hom) D'.nu.unitIso.inv 2 (s,t,t-k)) nx
        _ = targetNuLabel D' .sphere s t k x := by
          simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
          dsimp only [targetNuLabel]
          congr 1
    have hlabel : familyPageMap D'.family f 2 (s,t,t-k) (D'.quotientLabel q s t k x)=
        finiteTargetLabel D' .sphere q s t k x := by
      calc
        _ = familyPageMap D'.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D'.nu.unitIso.inv q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) :=
          ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D'.nu.unitIso.inv q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)
        _ = familyPageMap D'.family (D'.nu.unitIso.inv ≫ XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q)
            2 (s,t,t-k) (D'.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
        _ = familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
            (familyPageMap D'.family D'.nu.unitIso.inv 2 (s,t,t-k) (D'.sphereE2 s t k x)) :=
          (ConcreteCategory.congr_hom (family_page_comp D'.nu.unitIso.inv (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D'.sphereE2 s t k x)).symm
        _ = finiteTargetLabel D' .sphere q s t k x := congrArg
          (fun y => familyPageMap D'.family (XModLambdaN.incl (D'.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
    exact hlabel
  have finite_sphere_infinity_cycle_label_exists
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (e : ((D'.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty) :
      ∃ x : E2 H SphereSpectrum s t,
        x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
        HasInfinityRepresentative (D'.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
          (D'.quotientLabel q s t k x) e := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let f := XModLambdaN.map D'.nu.unitIso.hom q
    let g := XModLambdaN.map D'.nu.unitIso.inv q
    have hgf : g≫f=𝟙 _ := by
      dsimp only [f,g]
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have heq : (D'.family.functor.map f).eInftyMap (s,t,t-k)
        ((D'.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
      change ((D'.family.functor.map g).eInftyMap (s,t,t-k) ≫
        (D'.family.functor.map f).eInftyMap (s,t,t-k)) e=e
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
      rfl
    obtain ⟨c,hc⟩ := Quotient.exists_rep (P ((D'.family.functor.map g).eInftyMap (s,t,t-k) e))
    have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hc.symm
    have hl : familyPageMap D'.family f 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k c.val)=D'.quotientLabel q s t k c.val := by
      rw [←sphere_quotient_label_to_nu q k s t c.val]
      calc
        _ = familyPageMap D'.family (g≫f) 2 (s,t,t-k) (D'.quotientLabel q s t k c.val) :=
          ConcreteCategory.congr_hom (family_page_comp g f 2 (s,t,t-k)) _
        _ = D'.quotientLabel q s t k c.val := by
          rw [hgf,family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
            (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have h := family_infinity_representative_map f (s,t,t-k) _ _ hn
    rw [hl,heq] at h
    refine ⟨c.val,?_,h⟩
    convert c.property using 1; congr 1; omega
  have finite_sphere_filtration_has_cycle_label
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
      (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : Syn) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) s a) :
      ∃ x : E2 H SphereSpectrum s t,
        x ∈ cycles H SphereSpectrum ((q:ℤ)-k) (s,t) ∧
        Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) q)
    have ham : a ∈ (ModuleCat.subobjectModule
        (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (t-s,t-k)))
        (F.F s (t-s,t-k)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let gr := F.toAssociatedGraded s (t-s,t-k) a'
    let e := ((D'.quotientConvergence q hq).identification (s,t,t-k)).inv gr
    have he : ((D'.quotientConvergence q hq).identification (s,t,t-k)).hom e=gr :=
      ConcreteCategory.congr_hom ((D'.quotientConvergence q hq).identification (s,t,t-k)).inv_hom_id gr
    obtain ⟨x,hc,hx⟩ := finite_sphere_infinity_cycle_label_exists BHS q k hq hkq s t e
    exact ⟨x,hc,e,hx,a',ha',he⟩
  have sphere_quotient_label_from_nu (q k : ℕ) (s t : ℤ)
      (x : E2 H SphereSpectrum s t) :
      familyPageMap D'.family (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) = D'.quotientLabel q s t k x := by
    rw [←sphere_quotient_label_to_nu q k s t x]
    have hcomp := ConcreteCategory.congr_hom (family_page_comp (XModLambdaN.map D'.nu.unitIso.inv q) (XModLambdaN.map D'.nu.unitIso.hom q) 2 (s,t,t-k))
      (D'.quotientLabel q s t k x)
    have hgf : XModLambdaN.map D'.nu.unitIso.inv q ≫ XModLambdaN.map D'.nu.unitIso.hom q = 𝟙 _ := by
      rw [←D'.quotientFunctoriality.map_comp,Iso.inv_hom_id,D'.quotientFunctoriality.map_id]
    have hid : familyPageMap D'.family (𝟙 (XModLambdaN (S_0_0 : Syn) q)) 2 (s,t,t-k) = 𝟙 _ := by
      rw [family_map_data,CategoryTheory.Functor.map_id]
      exact SSDataMorphism.pageMap_id
        (D'.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-k) (↑(2-2:ℤ).toNat)
    exact hcomp.trans (by rw [hgf]; erw [hid]; rfl)
  have finite_sphere_zero_of_classical_quotient
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
  have finite_sphere_boundary_detects_zero
      (BHS : EInftyComparison D') (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (hx : x∈boundaries H SphereSpectrum (1+k) (s,t)) :
      Detects (D'.quotientConvergence q hq) (s,t,t-k) (D'.quotientLabel q s t k x) 0 := by
    let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
      (by constructor <;> omega)
    let z : cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t) :=
      ⟨x,boundaries_le_cycles H SphereSpectrum (s,t) (1+k) _ hx⟩
    have hz : NestedQuotient.projection _ (boundaries H SphereSpectrum (1+t-(t-k)) (s,t)) z=0 := by
      apply (NestedQuotient.projection_eq_zero z).mpr
      convert hx using 1; congr 1; omega
    have hn : HasInfinityRepresentative (D'.family.nuQuotient D'.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D' .sphere q s t k x) 0 := by
      apply (BHS.labels.1 .sphere q hq (s,t) k hk z 0).mpr
      change P 0 = NestedQuotient.projection _ _ z
      simpa only [map_zero] using hz.symm
    have h := family_infinity_representative_map (XModLambdaN.map D'.nu.unitIso.hom q)
      (s,t,t-k) _ _ hn
    rw [sphere_quotient_label_from_nu q k s t x,map_zero] at h
    exact ⟨0,h,0,by simp only [map_zero],by simp only [map_zero]⟩
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
  let shiftSwap (a b : ℤ × ℤ) (A : Syn) :
      (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
      (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
    (biShiftAddIso a b (a+b) rfl).app A ≪≫
      ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm
  have lambda_one_shift (coh : BiShiftCoherence Syn) (a : ℤ×ℤ) (A : Syn) :
      lambdaPow 1 ((SyntheticCategory.biShift a).obj A)=
        (shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
    rw [lambdaPow_one coh,lambdaPow_one coh]
    simpa only [shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc] using coh.lambda_comm a A
  let sphere_unit (D' : AdamsComparison H M' Syn) : BiHom 0 0 (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.hom.app _
  let sphere_unit_label (D' : AdamsComparison H M' Syn) : E2 H SphereSpectrum 0 0 :=
    D'.sphereFirstQuotient 0 0 (quotientClass 1 (sphere_unit D'))
  have nu_target_finite_error_twice_zero
      (BHS : EInftyComparison D') (A : AdamsAlgebraStructures D') (ab : AlgebraDetectionCompatibility D' A)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      (hd : Detects D'.sphereConvergence (1,1,1)
        (D'.sphereE2 1 1 0 (Sphere.Internal.hi H M' 0)) h0)
      (hgap : cycles H SphereSpectrum 3 (12,137) ≤ boundaries H SphereSpectrum 7 (12,137))
      (hprod : ∀ x : E2 H SphereSpectrum 13 138,
        Sphere.Internal.product H M' (s:=1) (t:=1) (s':=13) (t':=138)
          (Sphere.Internal.hi H M' 0) x ∈ boundaries H SphereSpectrum 2 (14,139))
      (a : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 a) :
      lambdaMultiply 1 (sphereAction h0 a)=0 := by
    have hc : Subsingleton (CycleQuotient H SphereSpectrum 3 7 (12,137)) := by
      apply subsingleton_of_forall_eq 0
      intro z
      induction z using Quotient.inductionOn with
      | h z => exact (NestedQuotient.projection_eq_zero z).mpr (hgap z.property)
    have hg : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 13 a := by
      apply (D'.quotientConvergence 9 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
        12 13 125 131 (by decide)
      intro j hj hj'
      have : j=12 := by omega
      subst j
      exact finite_sphere_zero_of_classical_quotient BHS 9 (by decide) 12 137 131 (by norm_num) hc
    obtain ⟨x,_,hx⟩ := finite_sphere_filtration_has_cycle_label BHS 9 7 (by decide) (by decide) 13 138 a (hg.mp ha)
    have hdprod := ab.finite_action 9 (by decide) 1 1 13 138 0 7
      (Sphere.Internal.hi H M' 0) x h0 a hd hx
    let z : E2 H SphereSpectrum 14 139 :=
      Sphere.Internal.product H M' (s:=1) (t:=1) (s':=13) (t':=138) (Sphere.Internal.hi H M' 0) x
    have hb : z∈boundaries H SphereSpectrum 8 (14,139) :=
      boundaries_monotone H SphereSpectrum (14,139) (by decide : (2:ℤ)≤8) (hprod x)
    have hz := finite_sphere_boundary_detects_zero BHS 9 7 (by decide) (by decide) 14 139 z hb
    have he : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 15 (sphereAction h0 a) := by
      simpa only [sub_zero, homotopyRegrade, Int.reduceAdd, Int.reduceSub, SyntheticObject.obj] using detects_sub_filtration (D'.quotientConvergence 9 (by decide))
        (14,139,132) hdprod hz
    have hf := lambda_filtration_preserved 1 15 (sphereAction h0 a) he
    exact sphere_quotient_high_filtration_zero BHS 9 (by decide) 125 131 15 (by decide)
      (lambdaMultiply 1 (sphereAction h0 a)) hf
  have lambda_one_one_133 (D' : AdamsComparison H M' Syn)
      {X : Syn} (c : BiHom 125 133 X) :
      lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
    have ha := shift_assoc_inv D'.shiftCoherence (125,133) (0,-1) (0,-1)
      (125,132) (0,-2) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Nat.cast_ofNat, Int.reduceSub]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (125,133) (0,-1)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 133)))]
    erw [← Category.assoc, ha]
    erw [lambdaPow_add D'.shiftCoherence 1 1 2 (by decide) (Smn 125 133)]
    simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
      Iso.trans_inv, eqToIso.inv, eqToHom_refl,
      Category.id_comp, Category.assoc]
    rfl
  have h0_action_right_one (D' : AdamsComparison H M' Syn)
      {X : Syn} (etaAux : BiHom 0 1 (S_0_0 : Syn))
      (c : BiHom 125 131 X) :
      sphereAction etaAux (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction etaAux c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (0,1) (125,131) (0,-1)
      (125,132) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (0,1) (125,131)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift (125,131)).map etaAux))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,131) (0,-1)).inv.naturality etaAux)]
    rfl
  have lambda_sphere_unit (D' : AdamsComparison H M' Syn) :
      lambdaMultiply 1 (sphere_unit D') = SyntheticCategory.lam.app (S_0_0 : Syn) := by
    have hu := D'.shiftCoherence.left_unit (0,-1) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold lambdaMultiply sphere_unit
    simp only [eqToHom_refl,Category.id_comp]
    erw [←lambdaPow_naturality 1 (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn))]
    erw [←hu,Iso.inv_hom_id_app_assoc]
    exact lambdaPow_one D'.shiftCoherence _
  have sphere_lambda_action (D' : AdamsComparison H M' Syn) {A : Syn}
      (a : BiHom 125 132 A) :
      sphereAction (lambdaMultiply 1 (sphere_unit D')) a = lambdaMultiply 1 a := by
    rw [lambda_sphere_unit D']
    have hc := D'.shiftCoherence.lambda_comm (125,132) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
      eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp]
    erw [lambdaPow_one D'.shiftCoherence, hc]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc]
    rfl
  have sphere_unit_action_136 (D' : AdamsComparison H M' Syn) {A : Syn}
      (a : BiHom 125 136 A) : sphereAction (sphere_unit D') a = a := by
    have hu := D'.shiftCoherence.left_unit (125,136) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold sphereAction sphere_unit
    erw [←hu,Iso.inv_hom_id_app_assoc]
  have sphere_unit_label_product_136
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 11 136) :
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D') y = y := by
    letI := A.syntheticSymmetric
    let b := (D'.sphereFirstQuotient 11 136).symm y
    have hb : D'.sphereFirstQuotient 11 136 b = y := (D'.sphereFirstQuotient 11 136).apply_symm_apply y
    have h := ab.first_quotient 0 0 11 136 (quotientClass 1 (sphere_unit D')) b
    change D'.sphereFirstQuotient 11 136
      (KIP126.Literature.AdamsSynthetic.algebraProduct (A.quotients.algebra 1 (by decide))
        (quotientClass 1 (sphere_unit D')) b) = _ at h
    rw [qb.sphere_action 1 (by decide) 0 0 125 136,sphere_unit_action_136 D'] at h
    change D'.sphereFirstQuotient 11 136 b =
      Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D')
        (D'.sphereFirstQuotient 11 136 b) at h
    rw [hb] at h
    exact h.symm
  have lambda_one_finite_detected_136
      (A : AdamsAlgebraStructures D') (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (y : E2 H SphereSpectrum 11 136)
      (a : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
      (ha : Detects (D'.quotientConvergence 9 (by decide)) (11,136,132)
        (D'.quotientLabel 9 11 136 4 y) a) :
      Detects (D'.quotientConvergence 9 (by decide)) (11,136,131)
        (D'.quotientLabel 9 11 136 5 y) (lambdaMultiply 1 a) := by
    have hu := D'.comparisonCompatible.homotopy_lambda 0 0 1 (sphere_unit D')
    have hh := ab.finite_action 9 (by decide) 0 0 11 136 1 4
      (sphere_unit_label D') y (lambdaMultiply 1 (sphere_unit D')) a hu ha
    change Detects (D'.quotientConvergence 9 (by decide)) (11,136,131)
      (D'.quotientLabel 9 11 136 5
        (Sphere.Internal.product H M' (s:=0) (t:=0) (s':=11) (t':=136) (sphere_unit_label D') y))
      (sphereAction (lambdaMultiply 1 (sphere_unit D')) a) at hh
    rw [sphere_unit_label_product_136 A qb ab y,sphere_lambda_action D'] at hh
    exact hh
  have nu_target_y_relation
      (BHS : EInftyComparison D') (A : AdamsAlgebraStructures D')
      (qb : QuotientAlgebraCompatibility D' A) (ab : AlgebraDetectionCompatibility D' A)
      (h0 : BiHom 0 1 (S_0_0 : Syn)) (ν : BiHom 3 4 (S_0_0 : Syn))
      (hd : Detects D'.sphereConvergence (1,1,1)
        (D'.sphereE2 1 1 0 (Sphere.Internal.hi H M' 0)) h0)
      (hgap : cycles H SphereSpectrum 3 (12,137) ≤ boundaries H SphereSpectrum 7 (12,137))
      (hprod : ∀ x : E2 H SphereSpectrum 13 138,
        Sphere.Internal.product H M' (s:=1) (t:=1) (s':=13) (t':=138)
          (Sphere.Internal.hi H M' 0) x ∈ boundaries H SphereSpectrum 2 (14,139))
      (Y : E2 H SphereSpectrum 11 136)
      (y0 : BiHom 125 132 (XModLambdaN (S_0_0 : Syn) 9))
      (hy0 : Detects (D'.quotientConvergence 9 (by decide)) (11,136,132)
        (D'.quotientLabel 9 11 136 4 Y) y0)
      (x : BiHom 122 126 (XModLambdaN (S_0_0 : Syn) 9))
      (y : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9))
      (hy : FiniteDetected D' 9 (by decide) 11 136 5 Y y)
      (hxy : sphereAction ν x=lambdaMultiply 1 y) :
      sphereAction h0 (sphereAction ν x)=lambdaMultiply 2 (sphereAction h0 y0) := by
    have hly := lambda_one_finite_detected_136 A qb ab Y y0 hy0
    let ly : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9) := lambdaMultiply 1 y0
    let e : BiHom 125 131 (XModLambdaN (S_0_0 : Syn) 9) := y-ly
    have hef : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 12 e :=
      by simpa only [e,ly,Int.reduceAdd] using
        detects_sub_filtration (D'.quotientConvergence 9 (by decide)) (11,136,131) hy.1 hly
    have hez := nu_target_finite_error_twice_zero BHS A ab h0 hd hgap hprod e hef
    have heq : lambdaMultiply 1 (sphereAction h0 y)=
        lambdaMultiply 1 (sphereAction h0 ly) := by
      apply sub_eq_zero.mp
      simpa only [e,sphereAction,lambdaMultiply,Preadditive.comp_sub,Functor.map_sub,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one] using hez
    rw [hxy,h0_action_right_one D',heq]
    have hright : sphereAction h0 ly=lambdaMultiply 1 (sphereAction h0 y0) := by
      change sphereAction h0 (lambdaMultiply 1 y0)=lambdaMultiply 1 (sphereAction h0 y0)
      -- The same coherence calculation at weight 132.
      have ha := shift_assoc_inv D'.shiftCoherence (0,1) (125,132) (0,-1)
        (125,133) (125,131) (125,132) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
      simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
      unfold sphereAction lambdaMultiply
      simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
      erw [← reassoc_of% (lambdaPow_naturality 1
        ((SyntheticCategory.biShift_comp (0,1) (125,132)).inv.app (S_0_0 : Syn)))]
      erw [← reassoc_of% (lambdaPow_naturality 1
        ((SyntheticCategory.biShift (125,132)).map h0))]
      erw [reassoc_of% ha]
      erw [← reassoc_of% ((SyntheticCategory.biShift_comp (125,132) (0,-1)).inv.naturality h0)]
      rfl
    rw [hright,lambda_one_one_133 D']
  have lambda_injective_three_five (D' : AdamsComparison H M' Syn)
      : LambdaInjectiveAt 3 5 (S_0_0 : Syn) := by
    let m : ℤ := 3
    let wt : ℤ := 5
    letI := D'.shiftAdditive (0,-1)
    letI := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).faithful
    let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := Syn) m wt)
    let T := XModLambdaN.cofiberTriangle (S_0_0 : Syn) 1
    let e₀ : U ≅ Smn (Syn := Syn) m (wt-1) :=
      (SyntheticCategory.biShift_comp (m,wt) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1)
    let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := Syn) (m+1) (wt-1) :=
      (shiftFunctor Syn (1 : ℤ)).mapIso e₀ ≪≫
        (SyntheticCategory.biShift_compat (Syn := Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (m,wt-1) (1,0)).app S_0_0 ≪≫
        eqToIso (by congr 1)
    have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
      intro q
      haveI : Subsingleton (PageRepresentatives.Ambient H SphereSpectrum (wt-m-2,wt-1)) :=
        sphereAdamsInternal_filtration_zero_subsingleton H 2 4 (by decide)
      have hz : ∀ a : BiHom (m+1) (wt-1) (XModLambdaN (S_0_0 : Syn) 1), a = 0 := by
        intro a
        have hp : wt - 1 - (wt-m-2) = m+1 := by omega
        have hsub : Subsingleton (BiHom (wt-1-(wt-m-2)) (wt-1)
            (XModLambdaN (S_0_0 : Syn) 1)) :=
          (D'.sphereFirstQuotient (wt-m-2) (wt-1)).injective.subsingleton
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
      rw [lambdaPow_one D'.shiftCoherence]
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
  have h0_lambda_left_nu (D' : AdamsComparison H M' Syn)
      (etaShuffle : BiHom 0 1 (S_0_0 : Syn))
      (a : BiHom 3 4 (S_0_0 : Syn)) :
      sphereAction (lambdaMultiply 1 etaShuffle) a = lambdaMultiply 1 (sphereAction etaShuffle a) := by
    let S := (S_0_0 : Syn)
    have h₁ := shift_assoc_inv D'.shiftCoherence (0,1) (3,4) (0,-1)
      (3,5) (3,3) (3,4) (by decide) (by decide) (by decide) (by decide) S
    have h₂ := shift_assoc_inv D'.shiftCoherence (0,1) (0,-1) (3,4)
      (0,0) (3,3) (3,4) (by decide) (by decide) (by decide) (by decide) S
    simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
      eqToHom_refl,Category.id_comp] at h₁ h₂
    have hp :
      (SyntheticCategory.biShift_comp (3,5) (0,-1)).inv.app S ≫
        lambdaPow 1 (Smn 3 5) ≫
        (SyntheticCategory.biShift_comp (0,1) (3,4)).inv.app S =
      (SyntheticCategory.biShift_comp (0,0) (3,4)).inv.app S ≫
        (SyntheticCategory.biShift (3,4)).map
          ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app S) ≫
        (SyntheticCategory.biShift (3,4)).map (lambdaPow 1 (Smn 0 1)) := by
      rw [←lambdaPow_naturality]
      change (SyntheticCategory.biShift_comp (3,5) (0,-1)).inv.app S ≫
        (SyntheticCategory.biShift (0,-1)).map ((SyntheticCategory.biShift_comp (0,1) (3,4)).inv.app S) ≫
        lambdaPow 1 ((SyntheticCategory.biShift (3,4)).obj (Smn 0 1)) = _
      rw [lambda_one_shift D'.shiftCoherence (3,4) (Smn 0 1)]
      dsimp only [shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
      simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,eqToIso.hom,eqToIso.inv,eqToHom_refl,
        Category.comp_id,Category.id_comp]
      simp only [Category.assoc]
      erw [←Category.assoc ((SyntheticCategory.biShift_comp (3,5) (0,-1)).inv.app S)]
      erw [h₁]
      simp only [Category.assoc,Smn,S,Int.natCast_one,Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc,Smn,S,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
        (congrArg (fun z => z ≫ (SyntheticCategory.biShift (3,4)).map (lambdaPow 1 (Smn 0 1))) h₂.symm)
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
    simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat,Nat.cast_one,Int.natCast_one] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (3,4)).map etaShuffle ≫ a) hp).symm
  have nu_lambda_right_h0 (D' : AdamsComparison H M' Syn)
      (etaAux : BiHom 3 4 (S_0_0 : Syn))
      (c : BiHom 0 1 (S_0_0 : Syn)) :
      sphereAction etaAux (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction etaAux c) := by
    have ha := shift_assoc_inv D'.shiftCoherence (3,4) (0,1) (0,-1)
      (3,5) (0,0) (3,4) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
    simp only [biShiftAddIso, Iso.trans_inv, eqToIso.inv, eqToHom_refl, Category.id_comp] at ha
    unfold sphereAction lambdaMultiply
    simp only [eqToHom_refl, Category.id_comp, Int.reduceAdd]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift_comp (3,4) (0,1)).inv.app (S_0_0 : Syn)))]
    erw [← reassoc_of% (lambdaPow_naturality 1
      ((SyntheticCategory.biShift (0,1)).map etaAux))]
    erw [reassoc_of% ha]
    erw [← reassoc_of% ((SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.naturality etaAux)]
    rfl
  have h0_nu_commute (D' : AdamsComparison H M' Syn)
      (h0 : BiHom 0 1 (S_0_0 : Syn)) (ν : BiHom 3 4 (S_0_0 : Syn))
      (hh0 : lambdaMultiply 1 h0=syntheticTwo) :
      sphereAction h0 ν=sphereAction ν h0 := by
    apply lambda_injective_three_five D'
    have hm (z : BiHom 3 5 (S_0_0 : Syn)) : lambdaAction 3 5 _ z=lambdaMultiply 1 z := by
      unfold lambdaAction lambdaMultiply
      rw [lambdaPow_one D'.shiftCoherence]
      rfl
    rw [hm,hm,←h0_lambda_left_nu D',←nu_lambda_right_h0 D',hh0]
    change sphereAction (syntheticTwo : BiHom 0 0 (S_0_0 : Syn)) ν =
      sphereAction ν (syntheticTwo : BiHom 0 0 (S_0_0 : Syn))
    letI := D'.shiftAdditive (3,4)
    have hl := D'.shiftCoherence.left_unit (3,4) (S_0_0 : Syn)
    have hr := D'.shiftCoherence.right_unit (3,4) (S_0_0 : Syn)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hl hr
    unfold sphereAction syntheticTwo
    simp only [Functor.map_add,Preadditive.comp_add,
      Preadditive.add_comp,Category.comp_id,two_smul]
    rw [←hl]
    erw [SyntheticCategory.biShift_zero.hom.naturality ν]
    erw [←hr]
    change
      ((SyntheticCategory.biShift_comp (0,0) (3,4)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (0,0) (3,4)).hom.app (S_0_0 : Syn) ≫ ν) +
      ((SyntheticCategory.biShift_comp (0,0) (3,4)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (0,0) (3,4)).hom.app (S_0_0 : Syn) ≫ ν) =
      ((SyntheticCategory.biShift_comp (3,4) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn) ≫ ν) +
      ((SyntheticCategory.biShift_comp (3,4) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (3,4) (0,0)).hom.app (S_0_0 : Syn) ≫ ν)
    simp only [Iso.inv_hom_id_app_assoc]
  have h0_nu_actions_commute (D' : AdamsComparison H M' Syn) {X : Syn}
      (h0 : BiHom 0 1 (S_0_0 : Syn)) (ν : BiHom 3 4 (S_0_0 : Syn))
      (hh0 : lambdaMultiply 1 h0=syntheticTwo) (x : BiHom 122 126 X) :
      sphereAction h0 (sphereAction ν x)=sphereAction ν (sphereAction h0 x) := by
    have hleft : sphereAction (sphereAction h0 ν) x=sphereAction h0 (sphereAction ν x) := by
      have ha := shift_assoc_inv D'.shiftCoherence (0,1) (3,4) (122,126)
        (3,5) (125,130) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
      simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
        eqToHom_refl,Category.id_comp] at ha
      unfold sphereAction
      simp only [Functor.map_comp,Category.assoc]
      erw [reassoc_of% ((SyntheticCategory.biShift_comp (3,4) (122,126)).inv.naturality h0)]
      erw [← reassoc_of% ha]
      rfl
    have hright : sphereAction (sphereAction ν h0) x=sphereAction ν (sphereAction h0 x) := by
      have ha := shift_assoc_inv D'.shiftCoherence (3,4) (0,1) (122,126)
        (3,5) (122,127) (125,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
      simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
        eqToHom_refl,Category.id_comp] at ha
      unfold sphereAction
      simp only [Functor.map_comp,Category.assoc]
      erw [reassoc_of% ((SyntheticCategory.biShift_comp (0,1) (122,126)).inv.naturality ν)]
      erw [← reassoc_of% ha]
      rfl
    rw [←hleft,←hright,h0_nu_commute D' h0 ν hh0]
  have nu_nine_h0x_gap (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D')
      (a : BiHom 122 127 (XModLambdaN (S_0_0 : Syn) 9)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 a := by
    apply (D'.quotientConvergence 9 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      9 11 122 127 (by decide)
    intro j hj hj'
    have hc : Subsingleton (E2 H SphereSpectrum j (122+j)) := by
      have hjs : j=9 ∨ j=10 := by omega
      rcases hjs with rfl|rfl
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,9,131,[]⟩ (by
          exact List.mem_of_getElem? (l := Raw.degrees) (i := 170) rfl)
        change E2 H SphereSpectrum 9 131 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
      · obtain ⟨e,_⟩ := I'.basis ⟨.sphere,10,132,[]⟩ (by
          exact List.mem_of_getElem? (l := Raw.degrees) (i := 179) rfl)
        change E2 H SphereSpectrum 10 132 ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        exact e.injective.subsingleton
    haveI := hc
    apply finite_sphere_zero_of_classical_quotient BHS 9 (by decide) j (122+j) 127
      (by constructor <;> omega)
    haveI : Subsingleton (cycles H SphereSpectrum ((9:ℤ)-(122+j)+127) (j,122+j)) := inferInstance
    refine ⟨?_⟩
    rintro ⟨x⟩ ⟨y⟩
    exact congrArg (NestedQuotient.projection _ _) (Subsingleton.elim x y)
  have detected_filtration {O : SyntheticObject} (i : Tridegree)
      {x : (D'.family.obj (O.obj D'.nu D'.hopfAndDetector)).Page 2 i}
      {a : BiHom (i.2.1-i.1) i.2.2 (O.obj D'.nu D'.hopfAndDetector)}
      (ha : Detects (D'.convergence O) i x a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) i.1 a := by
    obtain ⟨_,_,a',ha',_⟩ := ha
    have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (O.obj D'.nu D'.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)).arrow a' ∈
      ModuleCat.subobjectModule _ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (O.obj D'.nu D'.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)) := ⟨a',rfl⟩
    rw [ha'] at hm
    simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
  have nu_target_h0x_filtration
      (I' : AdamsComputationTheorems D' L' G) (BHS : EInftyComparison D') (A : AdamsAlgebraStructures D') (ab : AlgebraDetectionCompatibility D' A)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      (hd : Detects D'.sphereConvergence (1,1,1)
        (D'.sphereE2 1 1 0 (Sphere.Internal.hi H M' 0)) h0)
      (x : BiHom 122 126 (XModLambdaN (S_0_0 : Syn) 9))
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 8 x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 11 (sphereAction h0 x) := by
    have hf0 := detected_filtration (O:=.sphere) (1,1,1) hd
    exact (nu_nine_h0x_gap I' BHS _).mp
      (ab.action_filtration (.quotient 9 .sphere) 0 1 122 126 1 8 h0 x hf0 hx)
  have target_lambda_zero_0_1 (D' : AdamsComparison H M' Syn) {X : Syn} (a : BiHom 0 1 X) :
      lambdaMultiply 0 a=a := by
    have hc := D'.shiftCoherence.right_unit (0,1) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : Syn) := by
      change (biShiftAddIso (0,1) (0,0) (0,1) (by ext <;> simp)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hh0d := D'.comparisonCompatible.homotopy_lambda 1 1 0 h0
  rw [hh0,target_lambda_zero_0_1 D'] at hh0d
  have hgap : cycles H SphereSpectrum 3 (12,137) ≤ boundaries H SphereSpectrum 7 (12,137) := by
    intro x hx
    obtain ⟨xr,hxr⟩ := (isCycle_iff_represents H SphereSpectrum 4 (by decide) (12,137) x).mp ⟨by decide,hx⟩
    haveI : Subsingleton ((adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C:=C))).Page 4 (12,137)) :=
      SF.e4_stem125_af12
    have hz : xr=0 := Subsingleton.elim _ _
    rw [hz] at hxr
    exact boundaries_monotone H SphereSpectrum (12,137) (by decide : (3:ℤ)≤7)
      (boundary_of_zero_representative (r:=4) (p:=(12,137)) (x:=x) hxr)
  obtain ⟨x,y,hx,hy,hxy⟩ := hext
  have he := nu_target_y_relation BHS.eInfty A qb ab h0 nu hh0d hgap
    (nu_target_h0_af13_image_boundary_two I') (I'.interpretation.sphere 11 136 Y) y0 hy0 x y hy hxy
  have hxF : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 8 x :=
    detected_filtration (O:=.quotient 9 .sphere) (8,130,126) hx.1
  have hF := nu_target_h0x_filtration I' BHS.eInfty A ab h0 hh0d x hxF
  have hn : sphereAction nu (sphereAction h0 x)≠0 := by
    rw [←h0_nu_actions_commute D' h0 nu hlambda_h0 x,he]
    exact hweaknonzero
  exact nu_target_of_finite_nonzero I' BHS SF A ab nu hnu (nu_target_h2_af13_product_zero I') _ hF hn

end NuTargetProof



end
end KIP126.Main.SectionSeven
