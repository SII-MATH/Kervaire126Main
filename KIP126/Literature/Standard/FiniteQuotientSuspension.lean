module

import all KIP126.Literature.Standard.FiniteQuotientPositive
import all KIP126.Literature.Standard.FiniteQuotientTriangle
import all KIP126.Literature.Standard.FiniteQuotientGhosts

/-! Strict ordinary suspension naturality of the actual selected quotient
maps on finite sources. The comparison is only required to preserve the
actual quotient inclusion; no equality of suspension comparisons is assumed.
-/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard Internal.GhostResearch
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section Generic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C:=Syn)]

/-- The exact Hom obstruction to strict suspension naturality vanishes
on the stated same source. The actual CommShift comparison is used only as
an isomorphism of the source of the residual map, never identified with a
different chosen comparison. The argument works for every natural q. -/
private theorem finite_quotient_suspension_naturality_of_vanishing
    (q : ℕ) [(SyntheticCategory.biShift (Syn:=Syn) (0,-(q:ℤ))).CommShift ℤ]
    {A B : Syn}
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (B⟦(1:ℤ)⟧) q ≅ (XModLambdaN B q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl A q))
    (heB : XModLambdaN.incl (B⟦(1:ℤ)⟧) q≫eB.hom=
      (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl B q))
    (hvan : ∀ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶
      XModLambdaN B q, z=0)
    (f : A ⟶ B) :
    XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map f) q≫eB.hom=
      eA.hom≫(shiftFunctor Syn (1:ℤ)).map (XModLambdaN.map f q) := by
  let S := shiftFunctor Syn (1:ℤ)
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(q:ℤ))
  let a := XModLambdaN.map (S.map f) q≫eB.hom
  let b := eA.hom≫S.map (XModLambdaN.map f q)
  have hincl : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫a=
      XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫b := by
    calc
      _ = (S.map f≫XModLambdaN.incl (B⟦(1:ℤ)⟧) q)≫eB.hom := by
        simpa only [a,Category.assoc] using congrArg (fun k => k≫eB.hom)
          (XModLambdaN.incl_naturality (S.map f) q).symm
      _ = S.map f≫S.map (XModLambdaN.incl B q) := by rw [Category.assoc,heB]
      _ = S.map (f≫XModLambdaN.incl B q) := (S.map_comp _ _).symm
      _ = S.map (XModLambdaN.incl A q≫XModLambdaN.map f q) := by
        rw [XModLambdaN.incl_naturality]
      _ = S.map (XModLambdaN.incl A q)≫S.map (XModLambdaN.map f q) := S.map_comp _ _
      _ = _ := by rw [←heA]; simp only [b,Category.assoc]
  have hdefect : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫(a-b)=0 := by
    rw [Preadditive.comp_sub,hincl,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished (A⟦(1:ℤ)⟧) q) (a-b) hdefect
  let χ : F.obj (A⟦(1:ℤ)⟧) ≅ (F.obj A)⟦(1:ℤ)⟧ := (F.commShiftIso (1:ℤ)).app A
  let e := S.mapIso χ
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let w : (F.obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN B q := ff.preimage (e.inv≫z)
  have hw : S.map w=e.inv≫z := ff.map_preimage _
  have hz0 : z=0 := (cancel_epi e.inv).mp (by rw [←hw,hvan w,S.map_zero]; simp)
  apply sub_eq_zero.mp
  change a-b=0
  rw [hz,hz0,comp_zero]

end Generic

private theorem suspension_finite_source_to_unshifted_quotient_vanishing
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p : ℤ×ℤ) (q : ℕ) (hq : 0<q) (hrel : p.2+(q:ℤ)≤p.1+1)
    (z : ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧ ⟶
      XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q) : z=0 := by
  rcases hX with hs | hc
  · obtain ⟨n,⟨e⟩⟩ := hs.2
    let eNu := model.nu.functor.mapIso e ≪≫ ghost_shifts_nu_sphere_iso n
    let eD : ((SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧ ≅
        Smn (Syn:=SyntheticSpectrum) (n+p.1+1) (n+p.2) :=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
        ((SyntheticCategory.biShift p).mapIso eNu ≪≫
          (biShiftAddIso (n,n) p (n+p.1,n+p.2) (by ext <;> simp)).app S_0_0) ≪≫
        positive_sphere_suspension_iso (n+p.1) (n+p.2)
    exact negative_hom_finite_sphere_iso Y q hq (n+p.1+1) (n+p.2) (by omega) eD z
  · obtain ⟨n,⟨e⟩⟩ := hc.2
    let eNu := model.nu.functor.mapIso e ≪≫
      ghost_shifts_nu_int_iso (ClassicalObject.nuCofiber.obj model.auxiliary) n
    let eD : (SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ≅
        (SyntheticCategory.biShift (n+p.1,n+p.2)).obj
          (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) :=
      (SyntheticCategory.biShift p).mapIso eNu ≪≫
        (biShiftAddIso (n,n) p (n+p.1,n+p.2) (by ext <;> simp)).app _
    let eDS := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eD
    have hz : eDS.inv ≫ z=0 :=
      negative_hom_shifted_nu_cofiber_finite Y q hq (n+p.1) (n+p.2) (by omega) _
    exact (cancel_epi eDS.inv).mp (by simpa only [comp_zero] using hz)

private theorem suspension_finite_source_to_quotient_vanishing
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (δ ε : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (hrel : δ.2-δ.1-(ε.2-ε.1)≤1)
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))))⟦(1:ℤ)⟧ ⟶
      XModLambdaN ((SyntheticCategory.biShift ε).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q) : z=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) ε
  letI : F.Additive := model.exactness.shiftAdditive ε
  letI : F.CommShift ℤ := model.exactness.shiftCommShift ε
  letI : F.IsTriangulated := model.exactness.shiftExact ε
  let p : ℤ×ℤ := (δ.1-ε.1,δ.2-ε.2-(q:ℤ))
  let D := ((SyntheticCategory.biShift p).obj
    (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧
  obtain ⟨eQ,_heQ⟩ := finite_quotient_shift_comparison model.quotients.coherence ε q
    (model.nu.functor.obj (Y.obj model.auxiliary))
  let eComp : F.obj ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) ≅
      (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) :=
    (biShiftAddIso p ε (δ+(0,-(q:ℤ))) (by
      apply Prod.ext
      · dsimp only [p,Prod.fst_add]
        omega
      · dsimp only [p,Prod.snd_add]
        omega)).app _ ≪≫
      (SyntheticCategory.biShift_comp δ (0,-(q:ℤ))).symm.app _
  let eS : F.obj D ≅
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
        ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (X.obj model.auxiliary))))⟦(1:ℤ)⟧ :=
    (F.commShiftIso (1:ℤ)).app _ ≪≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eComp
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) ε
  let a : D ⟶ XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q :=
    ff.preimage (eS.hom ≫ z ≫ eQ.hom)
  have ha : a=0 :=
    suspension_finite_source_to_unshifted_quotient_vanishing X Y hX p q hq (by
      dsimp only [p]
      omega) a
  have hz : eS.hom ≫ z ≫ eQ.hom=0 := by
    have hm := ff.map_preimage (eS.hom ≫ z ≫ eQ.hom)
    change F.map a = eS.hom ≫ z ≫ eQ.hom at hm
    rw [ha,Functor.map_zero] at hm
    exact hm.symm
  exact (cancel_mono eQ.hom).mp ((cancel_epi eS.hom).mp (by
    simpa only [Category.assoc,zero_comp,comp_zero] using hz))

/-- The actual coordinate criterion permits arbitrary source and target
isomorphisms. The same residual map is transported, then strictly killed. -/
private theorem suspension_finite_source_to_quotient_vanishing_of_coordinates
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-(r.2-r.1)≤1)
    {A B : SyntheticSpectrum}
    (aCoord : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (bCoord : B ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN B q) :
    z=0 := by
  let eS := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    ((SyntheticCategory.biShift (0,-(q:ℤ))).mapIso aCoord)
  let eT := (model.quotients.functoriality.functor q).mapIso bCoord
  have hz : eS.inv≫z≫eT.hom=0 :=
    suspension_finite_source_to_quotient_vanishing X Y hX p r q hq hrel _
  exact (cancel_mono eT.hom).mp ((cancel_epi eS.inv).mp
    (by simpa only [Category.assoc,zero_comp,comp_zero] using hz))

/-- Ordinary shifts are recorded explicitly and folded into the displayed
topological coordinates. The stated inequality includes both actual shifts. -/
private theorem suspension_finite_source_to_quotient_vanishing_of_shifted_coordinates
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (a b : ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-a-(r.2-r.1-b)≤1)
    {A B : SyntheticSpectrum}
    (aCoord : A ≅ ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦a⟧)
    (bCoord : B ≅ ((SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦b⟧)
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ XModLambdaN B q) :
    z=0 := by
  let eA : A ≅ (SyntheticCategory.biShift (p.1+a,p.2)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) :=
    aCoord ≪≫ (SyntheticCategory.biShift_compat a).symm.app _ ≪≫
      (biShiftAddIso p (a,0) (p.1+a,p.2) (by ext <;> simp)).app _
  let eB : B ≅ (SyntheticCategory.biShift (r.1+b,r.2)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) :=
    bCoord ≪≫ (SyntheticCategory.biShift_compat b).symm.app _ ≪≫
      (biShiftAddIso r (b,0) (r.1+b,r.2) (by ext <;> simp)).app _
  exact suspension_finite_source_to_quotient_vanishing_of_coordinates X Y hX
    (p.1+a,p.2) (r.1+b,r.2) q hq (by dsimp only; omega) eA eB z

/-- Strict suspension naturality for the actual selected quotient maps,
with the complete literal finite-source criterion and arbitrary actual
coordinate isomorphisms. Both suspension comparisons remain arbitrary
among the inclusion-compatible comparisons in the statement. -/
private theorem finite_quotient_suspension_naturality_finite_source
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-(r.2-r.1)≤1)
    {A B : SyntheticSpectrum}
    (aCoord : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (bCoord : B ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (B⟦(1:ℤ)⟧) q ≅ (XModLambdaN B q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (A⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (heB : XModLambdaN.incl (B⟦(1:ℤ)⟧) q≫eB.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl B q))
    (f : A ⟶ B) :
    XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q≫eB.hom=
      eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) := by
  letI := model.exactness.shiftCommShift (0,-(q:ℤ))
  exact finite_quotient_suspension_naturality_of_vanishing q eA eB heA heB
    (fun z => suspension_finite_source_to_quotient_vanishing_of_coordinates
      X Y hX p r q hq hrel aCoord bCoord z) f

end
end KIP126.Literature.Standard
