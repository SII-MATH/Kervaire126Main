module
public import KIP126.Literature.Standard
public import KIP126.Literature.Triangles
import all KIP126.Literature.Standard.FiniteQuotientConstruction
import all KIP126.Literature.Standard.FiniteQuotientSuspension
import all KIP126.Literature.Standard.FiniteQuotientRotations
import all KIP126.Literature.Standard.FiniteQuotientMiddle

/-! Actual normalized finite quotient rows. Classical syntax is used only
to obtain actual nu-object coordinates; every row map remains selected. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
open Internal Internal.GhostResearch
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option Elab.async false

private theorem normalized_literal_finite_nu_coordinates
    (X : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X) :
    ∃ (X0 : ClassicalObject) (n : ℤ), (X0=.sphere ∨ X0=.nuCofiber) ∧
      Nonempty (model.nu.functor.obj (X.obj model.auxiliary) ≅
        (SyntheticCategory.biShift (n,n)).obj
          (model.nu.functor.obj (X0.obj model.auxiliary))) := by
  rcases hX with hs | hc
  · obtain ⟨n,⟨e⟩⟩ := hs.2
    refine ⟨.sphere,n,Or.inl rfl,⟨?_⟩⟩
    exact model.nu.functor.mapIso e ≪≫ ghost_shifts_nu_int_iso SphereSpectrum n
  · obtain ⟨n,⟨e⟩⟩ := hc.2
    refine ⟨.nuCofiber,n,Or.inr rfl,⟨?_⟩⟩
    exact model.nu.functor.mapIso e ≪≫
      ghost_shifts_nu_int_iso (ClassicalObject.nuCofiber.obj model.auxiliary) n

/-- Record the precise Chow displacement while folding literal classical
shifts and an ordinary synthetic shift into actual finite coordinates. -/
private theorem normalized_literal_finite_source_coordinates
    (X : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (a : ℤ×ℤ) (n : ℤ) {A : SyntheticSpectrum}
    (eA : A ≅ ((SyntheticCategory.biShift a).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦n⟧) :
    ∃ (X0 : ClassicalObject) (p : ℤ×ℤ), (X0=.sphere ∨ X0=.nuCofiber) ∧
      Nonempty (A ≅ (SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (X0.obj model.auxiliary))) ∧
      p.2-p.1=a.2-a.1-n := by
  obtain ⟨X0,k,hX0,⟨e⟩⟩ := normalized_literal_finite_nu_coordinates X hX
  let p : ℤ×ℤ := (k+a.1+n,k+a.2)
  refine ⟨X0,p,hX0,⟨?_⟩,by dsimp [p]; omega⟩
  let e0 := (SyntheticCategory.biShift a).mapIso e ≪≫
    (biShiftAddIso (k,k) a (k+a.1,k+a.2) (by ext <;> simp)).app _
  exact eA ≪≫ (shiftFunctor SyntheticSpectrum n).mapIso e0 ≪≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) n).symm.app _ ≪≫
    (biShiftAddIso (k+a.1,k+a.2) (n,0) p (by ext <;> simp [p])).app _

/-- Move an ordinary shift into the actual classical nu-coordinate. -/
private def normalized_ordinary_shift_coordinate (X : ClassicalObject) (w n : ℤ) :
    ((SyntheticCategory.biShift (0,w)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦n⟧ ≅
      (SyntheticCategory.biShift (0,w-n)).obj
        (model.nu.functor.obj ((ClassicalObject.shift n X).obj model.auxiliary)) :=
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let lhs : ((SyntheticCategory.biShift (0,w)).obj V)⟦n⟧ ≅
      (SyntheticCategory.biShift (n,w)).obj V :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) n).symm.app _ ≪≫
      (biShiftAddIso (0,w) (n,0) (n,w) (by ext <;> simp)).app V
  let rhs : (SyntheticCategory.biShift (0,w-n)).obj
        (model.nu.functor.obj ((ClassicalObject.shift n X).obj model.auxiliary)) ≅
      (SyntheticCategory.biShift (n,w)).obj V :=
    (SyntheticCategory.biShift (0,w-n)).mapIso
        (ghost_shifts_nu_int_iso (X.obj model.auxiliary) n) ≪≫
      (biShiftAddIso (n,n) (0,w-n) (n,w) (by ext <;> simp)).app V
  lhs ≪≫ rhs.symm

private theorem normalized_quotient_row_finite_middle
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (hY : ghost_cells_literal_finite_source_case T.Y) (q : ℕ) (hq : 0<q) :
    let N := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum := by
  let N := KIP126.Literature.normalizedTriangle model T he
  let M := N.rotate
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  have hM : M ∈ distTriang SyntheticSpectrum := rot_of_distTriang N hT
  let eY0 : M.obj₁ ≅ ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary)))⟦(0:ℤ)⟧ :=
    SyntheticCategory.biShift_zero.symm.app _ ≪≫
      (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _
  obtain ⟨X0,p,hX0,⟨eA⟩,hp⟩ := normalized_literal_finite_source_coordinates
    T.Y hY (0,0) 0 eY0
  have hp0 : p.2-p.1=0 := by simpa only [sub_self,sub_zero] using hp
  let eB : M.obj₂ ≅ (SyntheticCategory.biShift (0,-eg)).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary)) := Iso.refl _
  let eC : M.obj₃ ≅ (SyntheticCategory.biShift (0,ef-1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary)) :=
    normalized_ordinary_shift_coordinate T.X ef 1
  have hAB : p.2-p.1-(-eg-0)≤1 := by
    rw [hp0]
    dsimp only [eg]
    omega
  have hAC : p.2-p.1-((ef-1)-0)≤1 := by
    rw [hp0]
    dsimp only [ef]
    omega
  obtain ⟨esusp,hesusp,hrow⟩ := actual_finite_first_quotient_row_of_coordinates
    M hM X0 T.Z (.shift 1 T.X) hX0 p (0,-eg) (0,ef-1) eA eB eC q hq hAB hAC
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  change Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (XModLambdaN.map (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)) q≫
      esusp.hom) ∈ distTriang SyntheticSpectrum at hrow
  have hneg : XModLambdaN.map (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)) q=
      -XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q := by
    change Q.map (-_) = -Q.map _
    exact Functor.map_neg Q
  rw [hneg,Preadditive.neg_comp] at hrow
  exact ⟨esusp,hesusp,hrow⟩

private theorem normalized_quotient_row_finite_first
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (hX : ghost_cells_literal_finite_source_case T.X) (q : ℕ) (hq : 0<q) :
    let N := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum := by
  let N := KIP126.Literature.normalizedTriangle model T he
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eX0 : N.obj₁ ≅ ((SyntheticCategory.biShift (0,ef)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))⟦(0:ℤ)⟧ :=
    (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _
  obtain ⟨X0,p,hX0,⟨eA⟩,hp⟩ := normalized_literal_finite_source_coordinates
    T.X hX (0,ef) 0 eX0
  have hp0 : p.2-p.1=ef := by simpa only [sub_zero] using hp
  let eB : N.obj₂ ≅ (SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  let eC : N.obj₃ ≅ (SyntheticCategory.biShift (0,-eg)).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary)) := Iso.refl _
  have hAB : p.2-p.1-(0-0)≤1 := by
    rw [hp0]
    dsimp only [ef]
    omega
  have hAC : p.2-p.1-(-eg-0)≤1 := by
    rw [hp0]
    dsimp only [ef,eg]
    omega
  obtain ⟨eSuspA,heSuspA,hrow⟩ := actual_finite_first_quotient_row_of_coordinates
    N hT X0 T.Y T.Z hX0 p (0,0) (0,-eg) eA eB eC q hq hAB hAC
  have hX0lit : ghost_cells_literal_finite_source_case X0 :=
    ghost_cells_descriptor_none_literal_actual X0 (by rcases hX0 with rfl | rfl <;> rfl)
  exact quotient_row_rotation_finite_source_coordinates X0 T.Y hX0lit p (0,0) q hq hAB
    N eA eB eSuspA heSuspA hrow

private theorem normalized_mapped_row_from_inverse_rotation
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map N.invRotate.mor₂ q)
      (XModLambdaN.map N.invRotate.mor₃ q)
      (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        N.invRotate.mor₁) q≫eA.hom)) ∈ distTriang SyntheticSpectrum) :
    Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q≫eA.hom) ∈ distTriang SyntheticSpectrum := by
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  let c : (N.obj₃⟦(-1:ℤ)⟧)⟦(1:ℤ)⟧ ≅ N.obj₃ :=
    (shiftEquiv SyntheticSpectrum (1:ℤ)).counitIso.app N.obj₃
  let eC : XModLambdaN ((N.obj₃⟦(-1:ℤ)⟧)⟦(1:ℤ)⟧) q ≅ XModLambdaN N.obj₃ q :=
    Q.mapIso c
  let R := Triangle.mk (XModLambdaN.map N.invRotate.mor₂ q)
    (XModLambdaN.map N.invRotate.mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      N.invRotate.mor₁) q≫eA.hom))
  let U := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
    (XModLambdaN.map N.mor₃ q≫eA.hom)
  have hsecond : XModLambdaN.map N.invRotate.mor₃ q≫eC.hom=
      XModLambdaN.map N.mor₂ q := by
    change Q.map (N.mor₂≫c.inv)≫Q.map c.hom=Q.map N.mor₂
    rw [←Functor.map_comp,Category.assoc,c.inv_hom_id,Category.comp_id]
  have hthird : -(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      N.invRotate.mor₁) q)=eC.hom≫XModLambdaN.map N.mor₃ q := by
    have hh : -((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.invRotate.mor₁)=
        c.hom≫N.mor₃ := by
      simpa [invRotCompRot,Triangle.rotate,c] using
        (((invRotCompRot (C:=SyntheticSpectrum)).app N).hom.comm₃)
    change -(Q.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.invRotate.mor₁))=
      Q.map c.hom≫Q.map N.mor₃
    rw [←Functor.map_neg,hh,Functor.map_comp]
  let E : R ≅ U := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eC
    (by change Q.map N.mor₁≫𝟙 _=𝟙 _≫Q.map N.mor₁; simp)
    (by
      change XModLambdaN.map N.invRotate.mor₃ q≫eC.hom=𝟙 _≫XModLambdaN.map N.mor₂ q
      rw [Category.id_comp]
      exact hsecond)
    (by
      change (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        N.invRotate.mor₁) q≫eA.hom))≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (𝟙 _)=
          eC.hom≫(XModLambdaN.map N.mor₃ q≫eA.hom)
      rw [CategoryTheory.Functor.map_id,Category.comp_id,←Preadditive.neg_comp,
        hthird,Category.assoc])
  exact isomorphic_distinguished R hR U E.symm

private theorem normalized_raw_suspension_distinguished
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum) :
    Triangle.mk ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₂)
      (-((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₃)) ∈
        distTriang SyntheticSpectrum := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let R := N⟦(1:ℤ)⟧
  let U := Triangle.mk (S.map N.mor₁) (S.map N.mor₂) (-(S.map N.mor₃))
  let E : U ≅ R := Triangle.isoMk _ _ (Iso.refl _) (-(Iso.refl _)) (Iso.refl _)
    (by simp [U,R,S,Triangle.shiftFunctor])
    (by simp [U,R,S,Triangle.shiftFunctor])
    (by simp [U,R,S,Triangle.shiftFunctor])
  exact isomorphic_distinguished R (Triangle.shift_distinguished N hN 1) U E

private theorem normalized_mapped_row_finite_third_coordinates
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (X Y Z : ClassicalObject) (hZ : ghost_cells_literal_finite_source_case Z)
    (p r s : ℤ×ℤ) (n : ℤ)
    (eA : N.obj₁ ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (eB : N.obj₂ ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (eC : N.obj₃ ≅ ((SyntheticCategory.biShift s).obj
      (model.nu.functor.obj (Z.obj model.auxiliary)))⟦n⟧)
    (hCA : s.2-s.1-n-(p.2-p.1)≤0) (hCB : s.2-s.1-n-(r.2-r.1)≤0)
    (q : ℕ) (hq : 0<q) :
    ∃ esusp : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
        (XModLambdaN.map N.mor₃ q≫esusp.hom) ∈ distTriang SyntheticSpectrum := by
  let M := N.invRotate
  have hM : M ∈ distTriang SyntheticSpectrum := inv_rot_of_distTriang N hN
  let eMC : M.obj₁ ≅ ((SyntheticCategory.biShift s).obj
      (model.nu.functor.obj (Z.obj model.auxiliary)))⟦n-1⟧ :=
    (shiftFunctor SyntheticSpectrum (-1:ℤ)).mapIso eC ≪≫
      ((shiftFunctorAdd' SyntheticSpectrum n (-1) (n-1) (by omega)).app _).symm
  obtain ⟨Z0,t,hZ0,⟨eFirst⟩,ht⟩ :=
    normalized_literal_finite_source_coordinates Z hZ s (n-1) eMC
  have hMA : t.2-t.1-(p.2-p.1)≤1 := by omega
  have hMB : t.2-t.1-(r.2-r.1)≤1 := by omega
  obtain ⟨eFirstSusp,hFirstSusp,hFirstRow⟩ := actual_finite_first_quotient_row_of_coordinates
    M hM Z0 X Y hZ0 t p r eFirst eA eB q hq hMA hMB
  have hZ0lit : ghost_cells_literal_finite_source_case Z0 :=
    ghost_cells_descriptor_none_literal_actual Z0 (by rcases hZ0 with rfl | rfl <;> rfl)
  obtain ⟨eSuspA,heSuspA,hRotRow⟩ := quotient_row_rotation_finite_source_coordinates
    Z0 X hZ0lit t p q hq hMA M eFirst eA eFirstSusp hFirstSusp hFirstRow
  exact ⟨eSuspA,heSuspA,normalized_mapped_row_from_inverse_rotation N q eSuspA hRotRow⟩

private theorem normalized_quotient_row_finite_third
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (hZ : ghost_cells_literal_finite_source_case T.Z) (q : ℕ) (hq : 0<q) :
    let N := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum := by
  let N := KIP126.Literature.normalizedTriangle model T he
  let ef := normalizedExponent model.classicalTower T.f
  let eg := normalizedExponent model.classicalTower T.g
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let aCoord : N.obj₁ ≅ (SyntheticCategory.biShift (0,(ef:ℤ))).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)) := Iso.refl _
  let bCoord : N.obj₂ ≅ (SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary)) :=
    SyntheticCategory.biShift_zero.symm.app _
  let cCoord : N.obj₃ ≅ (SyntheticCategory.biShift (0,-(eg:ℤ))).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary)) := Iso.refl _
  obtain ⟨eA,heA,hR0⟩ := normalized_mapped_row_finite_third_coordinates
    N hT T.X T.Y T.Z hZ (0,(ef:ℤ)) (0,0) (0,-(eg:ℤ)) 0 aCoord bCoord
    (cCoord ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _)
    (by dsimp only; omega) (by dsimp only; omega) q hq
  let V := Triangle.mk (S.map N.mor₁) (S.map N.mor₂) (-(S.map N.mor₃))
  have hV : V ∈ distTriang SyntheticSpectrum := normalized_raw_suspension_distinguished N hT
  let vaCoord : V.obj₁ ≅ (SyntheticCategory.biShift (1,(ef:ℤ))).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)) :=
    S.mapIso aCoord ≪≫ (SyntheticCategory.biShift_compat 1).symm.app _ ≪≫
      (biShiftAddIso (0,(ef:ℤ)) (1,0) (1,(ef:ℤ)) (by ext <;> simp)).app _
  let vbCoord : V.obj₂ ≅ (SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.Y.obj model.auxiliary)) :=
    (SyntheticCategory.biShift_compat 1).symm.app _
  let vcCoord : V.obj₃ ≅ ((SyntheticCategory.biShift (0,-(eg:ℤ))).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary)))⟦(1:ℤ)⟧ := S.mapIso cCoord
  obtain ⟨eSA,heSA,hR1⟩ := normalized_mapped_row_finite_third_coordinates
    V hV T.X T.Y T.Z hZ (1,(ef:ℤ)) (1,0) (0,-(eg:ℤ)) 1 vaCoord vbCoord vcCoord
    (by dsimp only; omega) (by dsimp only; omega) q hq
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  change Triangle.mk (XModLambdaN.map (S.map N.mor₁) q)
    (XModLambdaN.map (S.map N.mor₂) q)
    (XModLambdaN.map (-(S.map N.mor₃)) q≫eSA.hom) ∈ distTriang SyntheticSpectrum at hR1
  have hneg : XModLambdaN.map (-(S.map N.mor₃)) q=
      -XModLambdaN.map (S.map N.mor₃) q := by
    change Q.map (-_) = -Q.map _
    exact Functor.map_neg Q
  rw [hneg,Preadditive.neg_comp] at hR1
  obtain ⟨eC,heC⟩ := finite_quotient_suspension_comparison q N.obj₃
  obtain ⟨eB,heB,hf⟩ := finite_c_middle_suspension_comparison_of_coordinates
    T.X T.Y T.Z hZ ef eg aCoord cCoord N.mor₁ N.mor₂ N.mor₃ hT q hq
    eA heA eC heC eSA heSA hR0 hR1
  exact ⟨eB,heB,finite_c_public_row_of_middle_comparison N q eA eB hR0 hf⟩

/-- The actual normalized finite-quotient horizontal row, with the same
selected maps and its literal signed boundary. -/
public theorem normalized_finite_quotient_horizontal_row
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0<q) :
    let N := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
          esusp.hom)) ∈ distTriang SyntheticSpectrum := by
  rcases ghost_cells_some_finite_source T he with hX | hY | hZ
  · exact normalized_quotient_row_finite_first T he hT hX q hq
  · exact normalized_quotient_row_finite_middle T he hT hY q hq
  · exact normalized_quotient_row_finite_third T he hT hZ q hq

/-- The same constructed suspension comparison admits an actual cofiber
isomorphism preserving both structure arrows, including the literal sign. -/
private theorem normalized_finite_quotient_horizontal_cone_iso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : KIP126.Literature.NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0<q) :
    let N := KIP126.Literature.normalizedTriangle model T he
    ∃ esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      ∃ e : HasFunctorialCofiber.cofib (XModLambdaN.map N.mor₂ q) ≅
          XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q,
        HasFunctorialCofiber.cofibι (XModLambdaN.map N.mor₂ q)≫e.hom=
          XModLambdaN.map N.mor₃ q ∧
        e.hom≫(-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
          esusp.hom))=HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q) := by
  obtain ⟨esusp,hinc,hR⟩ := normalized_finite_quotient_horizontal_row T he hT q hq
  exact ⟨esusp,hinc,(fixed_row_iff_exact_cone_diagram
    (KIP126.Literature.normalizedTriangle model T he) q esusp).mp hR⟩

end
end KIP126.Literature.Standard
