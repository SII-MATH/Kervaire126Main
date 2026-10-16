module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Square
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingDelta

/-! AimPaper Theorem 6.1, lines 1644–1650: apply the proved filtered
three-edge square argument to the actual quotient/boundary naturality square.
The same right-edge representative has the prescribed finite label and the
prescribed absolute boundary. Shifted detection is transported back along the
actual ESS shift comparison. The input edge relations and crossing conversions
remain separate proof responsibilities. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private theorem detects_of_shift (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a))) :
    Detects (model.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl a) := by
  obtain ⟨eS,heS,b,hb,hgb⟩ := frame_of_source_detects
    (model.convergence (.shift δ A)) (p+δ) s _ (shiftHomotopyClass δ p a) ha
  let S := (essShift δ).filtered A p
  let I := towerInfinityIso (model.convergence A) (model.convergence (.shift δ A)) S s
  let e := I.inv eS
  let ar := (S.level s).inv b
  have har : ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow ar = a := by
    apply S.ambient.toLinearEquiv.injective
    have h := ConcreteCategory.congr_hom (S.level_arrow s) ar
    have hlevel : (S.level s).hom ar=b := (S.level s).toLinearEquiv.apply_symm_apply b
    simp only [ModuleCat.comp_apply] at h
    rw [hlevel] at h
    exact h.symm.trans (hb.trans ((essShift δ).ambient_eq A p a).symm)
  have hgar : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s p ar =
      (infinityGradedIso (model.convergence A) p s).hom e := by
    have h := ConcreteCategory.congr_hom (S.projection_inv_comm s) b
    simp only [ModuleCat.comp_apply] at h
    rw [hgb] at h
    rw [←h]
    change (S.gradedIso s).inv
        ((towerGradedIso (model.convergence (.shift δ A)) (p+δ) s).hom eS) =
      (towerGradedIso (model.convergence A) p s).hom
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A)) S s).inv eS)
    simp only [towerInfinityIso,Iso.trans_inv,Iso.symm_inv,←ModuleCat.comp_apply,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2) x e := by
    apply ((essShift δ).representative_iff A 2 (by decide) p s x e).mpr
    have hI : I.hom e=eS := I.toLinearEquiv.apply_symm_apply eS
    change HasInfinityRepresentative _ 2 _ _ (I.hom e)
    rw [hI]
    exact heS
  have hdet := source_frame_detects (model.convergence A) p s e x he ar hgar
  rw [har] at hdet
  exact hdet

private theorem absolute_boundary_detects_unshifted (B : SyntheticObject)
    (q : ℕ) (m w v : ℤ)
    (a : BiHom m w ((SyntheticObject.quotient q B).obj model.nu model.auxiliary))
    (x : (model.family.obj (B.obj model.nu model.auxiliary)).E₂ (v,m-1+v,w+q))
    (hdet : Detects (model.convergence (.shift (1,-(q:ℤ)) B)) (v,m+v,w)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-(q:ℤ))).page B 2 (by decide) (m-1,w+q) v).hom x))
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q))) :
    Detects (model.convergence B) (v,m-1+v,w+q) x
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv m w q (B.obj model.nu model.auxiliary)
          (a ≫ XModLambdaN.proj _ q))) := by
  let β := biSuspensionHomEquiv m w q (B.obj model.nu model.auxiliary)
    (a ≫ XModLambdaN.proj _ q)
  have he : a ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q =
      homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w (q:ℤ))
        (shiftHomotopyClass (1,-(q:ℤ)) (m-1,w+q) β) := by
    have h := congrArg (fun z => z ≫ (biSuspensionIso q (B.obj model.nu model.auxiliary)).inv)
      (bi_susp_symm_eq m w q (B.obj model.nu model.auxiliary) β)
    simpa [β,absoluteBoundary,shiftHomotopyClass,susp_invariance,Iso.homCongr] using h
  have hp : (v,((m-1,w+q)+(1,-(q:ℤ))).1+v,((m-1,w+q)+(1,-(q:ℤ))).2) =
      (v,m+v,w) := by ext <;> dsimp <;> omega
  have H := detects_transport hp.symm _ _ hdet
  apply detects_of_shift B (1,-(q:ℤ)) (m-1,w+q) v x β
  convert H using 1
  · have cancel {i j : Tridegree} (h : i=j)
        (z : (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).E₂ i) :
        regradeE2 h.symm (regradeE2 h z)=z := by subst j; rfl
    exact (cancel hp _).symm
  · rw [he]
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]

private theorem absolute_boundary_square_detects (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) (p : ℤ × ℤ) (s m r l : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient q A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).sequence.ssData
      (s+m,p.1+(s+m),p.2)).eInfty)
    (z : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (w : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (hleft : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r x z)
    (htop : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.quotient q B) (XModLambdaN.map g q)) p s m x y)
    (hbottom : TowerExtensionEquation
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l z w)
    (hsourceCrossing :
      TowerNoCrossing (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r ∨
      TowerNoCrossing (model.convergentMap (.quotient q A) (.quotient q B)
        (XModLambdaN.map g q)) p s m)
    (hbottomCrossing : TowerNoCrossing
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l)
    (y0 : (model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).E₂
      (s+m,p.1+(s+m),p.2))
    (hy : HasInfinityRepresentative _ 2 (s+m,p.1+(s+m),p.2) y0 y)
    (w0 : (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).E₂
      (s+r+l,p.1+(s+r+l),p.2))
    (hw : HasInfinityRepresentative _ 2 (s+r+l,p.1+(s+r+l),p.2) w0 w) :
    ∃ aRight : BiHom p.1 p.2 ((SyntheticObject.quotient q B).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient q B)) (s+m,p.1+(s+m),p.2) y0
        (homotopyRegrade (by dsimp; omega) rfl aRight) ∧
      Detects (model.convergence (.shift (1,-(q:ℤ)) B)) (s+r+l,p.1+(s+r+l),p.2) w0
        (homotopyRegrade (by dsimp; omega) rfl
          (aRight ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q)) := by
  obtain ⟨ar,br,cr,dr,har,hbr,hcr,hdr,hab,hac,hcd,hbd⟩ := square_frames
    (model.convergentMap (.quotient q A) (.quotient q B) (XModLambdaN.map g q))
    (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
      (absoluteBoundary (A.obj model.nu model.auxiliary) q))
    (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
      ((SyntheticCategory.biShift (1,-(q:ℤ))).map g))
    (absoluteBoundary_natural g q) p s m r l x y z w htop hleft hbottom
    (hsourceCrossing.elim Or.inr Or.inl) hbottomCrossing
  have hright := source_frame_detects (model.convergence (.quotient q B)) p (s+m) y y0 hy br hbr
  have hrightBoundary := source_frame_detects (model.convergence (.shift (1,-(q:ℤ)) B))
    p (s+r+l) w w0 hw dr hdr
  rw [←hbd] at hrightBoundary
  exact ⟨_,hright,hrightBoundary⟩

private theorem absolute_boundary_square_detects_unshifted (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) (p : ℤ × ℤ) (s m r l : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient q A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).sequence.ssData
      (s+m,p.1+(s+m),p.2)).eInfty)
    (z : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (w : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (hleft : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r x z)
    (htop : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.quotient q B) (XModLambdaN.map g q)) p s m x y)
    (hbottom : TowerExtensionEquation
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l z w)
    (hsourceCrossing :
      TowerNoCrossing (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r ∨
      TowerNoCrossing (model.convergentMap (.quotient q A) (.quotient q B)
        (XModLambdaN.map g q)) p s m)
    (hbottomCrossing : TowerNoCrossing
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l)
    (y0 : (model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).E₂
      (s+m,p.1+(s+m),p.2))
    (hy : HasInfinityRepresentative _ 2 (s+m,p.1+(s+m),p.2) y0 y)
    (w0 : (model.family.obj (B.obj model.nu model.auxiliary)).E₂
      (s+r+l,p.1-1+(s+r+l),p.2+q))
    (hw : HasInfinityRepresentative _ 2 (s+r+l,p.1+(s+r+l),p.2)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-(q:ℤ))).page B 2 (by decide)
          (p.1-1,p.2+q) (s+r+l)).hom w0)) w) :
    ∃ aRight : BiHom p.1 p.2 ((SyntheticObject.quotient q B).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient q B)) (s+m,p.1+(s+m),p.2) y0
        (homotopyRegrade (by dsimp; omega) rfl aRight) ∧
      Detects (model.convergence B) (s+r+l,p.1-1+(s+r+l),p.2+q) w0
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv p.1 p.2 q (B.obj model.nu model.auxiliary)
            (aRight ≫ XModLambdaN.proj _ q))) := by
  obtain ⟨aRight,haRight,hboundary⟩ := absolute_boundary_square_detects A B g q p s m r l
    x y z w hleft htop hbottom hsourceCrossing hbottomCrossing y0 hy _ hw
  exact ⟨aRight,haRight,absolute_boundary_detects_unshifted B q p.1 p.2
    (s+r+l) aRight w0 hboundary⟩

private theorem absolute_boundary_square_high_filtration (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) (p : ℤ × ℤ) (s m r l : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient q A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).sequence.ssData
      (s+m,p.1+(s+m),p.2)).eInfty)
    (z : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s+r,p.1+(s+r),p.2)).eInfty)
    (w : ((model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).sequence.ssData
      (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (hleft : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r x z)
    (htop : TowerExtensionEquation
      (model.convergentMap (.quotient q A) (.quotient q B) (XModLambdaN.map g q)) p s m x y)
    (hbottom : TowerExtensionEquation
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l z w)
    (hsourceCrossing :
      TowerNoCrossing (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
        (absoluteBoundary (A.obj model.nu model.auxiliary) q)) p s r ∨
      TowerNoCrossing (model.convergentMap (.quotient q A) (.quotient q B)
        (XModLambdaN.map g q)) p s m)
    (hbottomCrossing : TowerNoCrossing
      (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
        ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)) p (s+r) l)
    (y0 : (model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).E₂
      (s+m,p.1+(s+m),p.2))
    (hy : HasInfinityRepresentative _ 2 (s+m,p.1+(s+m),p.2) y0 y)
    : ∃ aRight : BiHom p.1 p.2 ((SyntheticObject.quotient q B).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient q B)) (s+m,p.1+(s+m),p.2) y0
        (homotopyRegrade (by dsimp; omega) rfl aRight) ∧
      FiltrationAtLeast model.syntheticTower (s+r+l)
        (biSuspensionHomEquiv p.1 p.2 q (B.obj model.nu model.auxiliary)
          (aRight ≫ XModLambdaN.proj _ q)) := by
  obtain ⟨ar,br,cr,dr,har,hbr,hcr,hdr,hab,hac,hcd,hbd⟩ := square_frames
    (model.convergentMap (.quotient q A) (.quotient q B) (XModLambdaN.map g q))
    (model.convergentMap (.quotient q A) (.shift (1,-(q:ℤ)) A)
      (absoluteBoundary (A.obj model.nu model.auxiliary) q))
    (model.convergentMap (.shift (1,-(q:ℤ)) A) (.shift (1,-(q:ℤ)) B)
      ((SyntheticCategory.biShift (1,-(q:ℤ))).map g))
    (absoluteBoundary_natural g q) p s m r l x y z w htop hleft hbottom
    (hsourceCrossing.elim Or.inr Or.inl) hbottomCrossing
  let aRight := ((model.syntheticTower.filtration
    ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).F (s+m) p).arrow br
  have hright := source_frame_detects (model.convergence (.quotient q B)) p (s+m) y y0 hy br hbr
  have hfil : FiltrationAtLeast model.syntheticTower (s+r+l)
      (aRight ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q) := by
    have hh : aRight ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q ∈
        ModuleCat.subobjectModule _ ((model.syntheticTower.filtration
          ((SyntheticObject.shift (1,-(q:ℤ)) B).obj model.nu model.auxiliary)).F (s+r+l) p) :=
      ⟨dr,hbd.symm⟩
    rcases p with ⟨p1,p2⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast,
      SyntheticObject.obj,syntheticHomotopy] using hh
  let β := biSuspensionHomEquiv p.1 p.2 q (B.obj model.nu model.auxiliary)
    (aRight ≫ XModLambdaN.proj _ q)
  have he : aRight ≫ absoluteBoundary (B.obj model.nu model.auxiliary) q =
      homotopyRegrade (sub_add_cancel p.1 1) (add_neg_cancel_right p.2 (q:ℤ))
        (shiftHomotopyClass (1,-(q:ℤ)) (p.1-1,p.2+q) β) := by
    have h := congrArg (fun z => z ≫ (biSuspensionIso q (B.obj model.nu model.auxiliary)).inv)
      (bi_susp_symm_eq p.1 p.2 q (B.obj model.nu model.auxiliary) β)
    simpa [β,absoluteBoundary,shiftHomotopyClass,susp_invariance,Iso.homCongr] using h
  rw [he] at hfil
  have hshift := (regrade_filtration_iff _ _ _ _).mp hfil
  have hβ := (shift_filtration_iff B (1,-(q:ℤ)) (p.1-1,p.2+q) (s+r+l) β).mp hshift
  exact ⟨aRight,hright,hβ⟩

end
end KIP126.ProofTools.Internal.Leibniz
