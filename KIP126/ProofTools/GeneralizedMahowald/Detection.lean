module
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.StretchingRepresentatives
/-! First-quotient detection from the retained Mahowald proof, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem first_label_detects_unshifted
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : a ≫ (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a := by
  have first_label_detects
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : Ambient model X (s,t))
      (a : BiHom (t-s) t (XModLambdaN (nuZero model X) q))
      (ha : a ≫ (model.quotients.tower (nuZero model X)).rho 1 q hq = firstLabel model X s t x) :
      Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x))
        (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) := by
    let Z := model.nu.functor.obj (X.obj model.auxiliary)
    let f : nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
    have h0 : (s,t,t+0-(0:ℕ))=(s,t,t) := by simp
    let x0 : (model.family.obj (nuZero model X)).E₂ (s,t,t) :=
      (congrArg (fun i => ((model.family.obj (nuZero model X)).E₂ i : Type)) h0).mp
        (model.comparison.nuE2 X 0 s t 0 x)
    let xq0 (n : ℕ) := familyPageMap model.family (XModLambdaN.incl (nuZero model X) n) 2 (s,t,t) x0
    let xq (n : ℕ) := familyPageMap model.family (XModLambdaN.incl Z n) 2 (s,t,t)
      (familyPageMap model.family f 2 (s,t,t) x0)
    have map_label (n : ℕ) :
        familyPageMap model.family (XModLambdaN.map f n) 2 (s,t,t) (xq0 n) = xq n := by
      dsimp only [xq0,xq]
      rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality]
      rw [←family_page_comp,ModuleCat.comp_apply]
    have rho_label :
        familyPageMap model.family ((model.quotients.tower Z).rho 1 q hq) 2 (s,t,t) (xq q) = xq 1 := by
      dsimp only [xq]
      rw [←ModuleCat.comp_apply,family_page_comp,(model.quotients.tower Z).rho_quotient]
    have hxR := (KIP126.Literature.Standard.bhs_finite_lift X q hq s t x).mpr ⟨a,ha⟩
    have hx : x ∈ KIP126.Literature.cycles model X q (s,t) := by
      have h := ((isCycle_iff_reaches model X (q+1) (by omega) (s,t) x).mpr hxR).2
      simpa only [add_sub_cancel_right] using h
    have transport_infinity {A : SyntheticAdamsSS.{0}} {i j : Tridegree}
        (h : i=j) (x : A.E₂ i)
        (hx : ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e) :
        ∃ e : (A.sequence.ssData j).eInfty,
          HasInfinityRepresentative A 2 j
            ((congrArg (fun k => (A.E₂ k : Type)) h).mp x) e := by
      subst j
      exact hx
    have map_cast {A B : SyntheticSpectrum} (g : A ⟶ B) {i j : Tridegree} (h : i=j)
        (x : (model.family.obj A).E₂ i) :
        (congrArg (fun k => ((model.family.obj B).E₂ k : Type)) h).mp
          (familyPageMap model.family g 2 i x) =
        familyPageMap model.family g 2 j
          ((congrArg (fun k => ((model.family.obj A).E₂ k : Type)) h).mp x) := by
      subst j
      rfl
    have hex : ∃ e0 : ((model.family.obj (XModLambdaN (nuZero model X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (model.family.obj (XModLambdaN (nuZero model X) q)) 2 (s,t,t) (xq0 q) e0 := by
      have hh := transport_infinity h0 (finiteNuLabel model X q 0 s t 0 x)
        (shifted_finite_source_exists X q hq 0 s t x hx)
      have hl : (congrArg (fun k => ((model.family.obj (XModLambdaN (nuZero model X) q)).E₂ k : Type)) h0).mp
          (finiteNuLabel model X q 0 s t 0 x) = xq0 q :=
        map_cast (XModLambdaN.incl (nuZero model X) q) h0 (model.comparison.nuE2 X 0 s t 0 x)
      exact (congrArg (fun z => ∃ e0 : ((model.family.obj (XModLambdaN (nuZero model X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (model.family.obj (XModLambdaN (nuZero model X) q)) 2 (s,t,t) z e0) hl).mp hh
    obtain ⟨e0,he0⟩ := hex
    have he := family_infinity_representative_map (XModLambdaN.map f q) (s,t,t) _ e0 he0
    have he' : HasInfinityRepresentative (model.family.obj (XModLambdaN Z q)) 2 (s,t,t) (xq q)
        ((model.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0) :=
      (congrArg (fun z => HasInfinityRepresentative (model.family.obj (XModLambdaN Z q)) 2 (s,t,t) z
        ((model.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0)) (map_label q)).mp he
    have hb0 : Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) (xq0 1) (firstLabel model X s t x) := by
      have transport_detects {A : SyntheticObject} {i j : Tridegree} (h : i=j)
          (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
          (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
          (ha : Detects (model.convergence A) i x a) :
          Detects (model.convergence A) j
            ((congrArg (fun k => ((model.family.obj (A.obj model.nu model.auxiliary)).E₂ k : Type)) h).mp x)
            ((congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2 (A.obj model.nu model.auxiliary)) h).mp a) := by
        subst j
        exact ha
      have h1 : (s,t,t+0)=(s,t,t) := by simp
      have h01 : (s,t,t+0-(0:ℕ))=(s,t,t+0) := by simp only [Nat.cast_zero,sub_zero]
      let x1 : (model.family.obj (nuZero model X)).E₂ (s,t,t+0) :=
        (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h01).mp
          (model.comparison.nuE2 X 0 s t 0 x)
      let a1 : BiHom (t-s) (t+0) (XModLambdaN (nuZero model X) 1) :=
        (model.firstQuotient X 0 s t).symm x
      have hr : Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t+0)
          (familyPageMap model.family (XModLambdaN.incl (nuZero model X) 1) 2 (s,t,t+0) x1) a1 :=
        model.comparisonCompatible.first_quotient X 0 s t x
      have hh := transport_detects h1 _ _ hr
      have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx1 : (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h1).mp x1 = x0 := by
        exact cast_comp
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h01)
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h1)
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h0)
          (model.comparison.nuE2 X 0 s t 0 x)
      have hlabel : (congrArg (fun k => ((model.family.obj (XModLambdaN (nuZero model X) 1)).E₂ k : Type)) h1).mp
          (familyPageMap model.family (XModLambdaN.incl (nuZero model X) 1) 2 (s,t,t+0) x1) = xq0 1 :=
        (map_cast _ h1 x1).trans (congrArg (familyPageMap model.family (XModLambdaN.incl (nuZero model X) 1)
          2 (s,t,t)) hx1)
      have halabel : (congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2
          (XModLambdaN (nuZero model X) 1)) h1).mp a1 = firstLabel model X s t x := by
        rfl
      exact (congrArg₂ (fun z a => Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) z a) hlabel halabel).mp hh
    have hb := detects_map (.quotient 1 (.shift (0,0) (.nu X))) (.quotient 1 (.nu X))
      (XModLambdaN.map f 1) (s,t,t) _ _ hb0
    have hb' : Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) (xq 1)
        (firstLabel model X s t x ≫ XModLambdaN.map f 1) :=
      (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) z
        (firstLabel model X s t x ≫ XModLambdaN.map f 1)) (map_label 1)).mp hb
    have hactual :
        (a ≫ XModLambdaN.map f q) ≫ (model.quotients.tower Z).rho 1 q hq =
          firstLabel model X s t x ≫ XModLambdaN.map f 1 := by
      rw [Category.assoc,←(model.quotients.natural f).rho_naturality,
        ←Category.assoc,ha]
    have hinj : Function.Injective ((model.family.functor.map ((model.quotients.tower Z).rho 1 q hq)).eInftyMap
        (s,t,t)).hom :=
      rho_infty_injective X 1 q (by decide) hq s t t (by omega)
    have hdet := detects_reflect (.quotient q (.nu X)) (.quotient 1 (.nu X))
      ((model.quotients.tower Z).rho 1 q hq) (s,t,t) hinj (xq q) _ he'
      (a ≫ XModLambdaN.map f q) (finite_bottom_filtration X q hq s t _)
      ((congrArg₂ (fun z b => Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) z b)
        rho_label hactual).mpr hb')
    have htarget : regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x) = xq q := by
      have h2 : (s,t,t-(0:ℕ))=(s,t,t) := by simp
      have h02 : (s,t,t+0-(0:ℕ))=(s,t,t-(0:ℕ)) := by simp only [add_zero]
      let x2 : (model.family.obj (nuZero model X)).E₂ (s,t,t-(0:ℕ)) :=
        (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h02).mp
          (model.comparison.nuE2 X 0 s t 0 x)
      have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx2 : (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h2).mp x2 = x0 :=
        cast_comp
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h02)
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h2)
          (congrArg (fun k => ((model.family.obj (nuZero model X)).E₂ k : Type)) h0)
          (model.comparison.nuE2 X 0 s t 0 x)
      have regrade_cast {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j) (x : A.E₂ i) :
          regradeE2 h x = (congrArg (fun k => (A.E₂ k : Type)) h).mp x := by
        subst j
        rfl
      rw [regrade_cast]
      exact (map_cast (XModLambdaN.incl Z q) h2 _).trans (congrArg
        (familyPageMap model.family (XModLambdaN.incl Z q) 2 (s,t,t))
        ((map_cast f h2 x2).trans (congrArg (familyPageMap model.family f 2 (s,t,t)) hx2)))
    exact (congrArg (fun z => Detects (model.convergence (.quotient q (.nu X))) (s,t,t) z
      (a ≫ XModLambdaN.map f q)) htarget).mpr hdet

  let Z := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app _
  have hfg : f ≫ g = 𝟙 _ := Iso.hom_inv_id_app _ _
  have hgf : g ≫ f = 𝟙 _ := Iso.inv_hom_id_app _ _
  have hfirst : (a ≫ XModLambdaN.map g q) ≫ (model.quotients.tower (nuZero model X)).rho 1 q hq =
      firstLabel model X s t x := by
    rw [Category.assoc,←(model.quotients.natural g).rho_naturality,
      ←Category.assoc,ha,Category.assoc,←model.quotients.functoriality.map_comp,hfg,
      model.quotients.functoriality.map_id,Category.comp_id]
  have h := first_label_detects X q hq s t x (a ≫ XModLambdaN.map g q) hfirst
  have hback : (a ≫ XModLambdaN.map g q) ≫ XModLambdaN.map f q = a := by
    rw [Category.assoc,←model.quotients.functoriality.map_comp,hgf,
      model.quotients.functoriality.map_id,Category.comp_id]
  exact (congrArg (fun a => Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
    (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a) hback).mp h

end
end KIP126.ProofTools.Internal.Mahowald
