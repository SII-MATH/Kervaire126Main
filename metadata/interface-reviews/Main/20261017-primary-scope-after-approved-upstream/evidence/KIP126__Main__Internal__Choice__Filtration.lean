module

public import KIP126.Main.Conditions

/-! Additive square and detection transport from Selected/ChoiceInvariance:631–683
at bbac1fc05843 (MIT). These are proofs on the same fixed upstream tower. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem theta_square_difference
    (θ θ' : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (h2 : θ'+θ'=0) :
    sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct (θ-θ') (θ-θ') := by
  classical
  letI := model.exactness.shiftAdditive (62,64)
  let d := θ-θ'
  have ht : θ=θ'+d := by dsimp only [d]; abel
  have hc : sphereProduct d θ'=sphereProduct θ' d := by
    have h := model.sphereProductCommutative 62 64 62 64 d θ'
    norm_num [homotopyRegrade] at h
    exact h
  have hz : sphereProduct θ' d+sphereProduct d θ'=0 := by
    rw [hc]
    dsimp only [sphereProduct]
    rw [←Preadditive.comp_add,←Preadditive.add_comp,←Functor.map_add,h2,Functor.map_zero,
      zero_comp,comp_zero]
  have hs : sphereProduct (θ'+d) (θ'+d)=sphereProduct θ' θ'+sphereProduct d d := by
    have he : sphereProduct (θ'+d) (θ'+d)=
        sphereProduct θ' θ'+sphereProduct θ' d+(sphereProduct d θ'+sphereProduct d d) := by
      simp only [sphereProduct,Functor.map_add,Preadditive.add_comp,Preadditive.comp_add]
      abel
    rw [he]
    calc
      _ = sphereProduct θ' θ'+(sphereProduct θ' d+sphereProduct d θ')+sphereProduct d d := by abel
      _ = _ := by rw [hz,add_zero]
  change sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct d d
  rw [ht,hs,add_sub_cancel_left]


private theorem detects_of_difference_in_next_filtration
    {H' : SyntheticSpectrum} {unit : S_0_0 ⟶ H'}
    {F : SyntheticAdamsFamily SyntheticSpectrum} {X : SyntheticSpectrum}
    {T : SyntheticTowerPresentation unit F}
    (c : SyntheticTowerConvergence T X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : FiltrationAtLeast T (i.1+1) (b-a)) :
    Detects c i x b := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let P := T.filtration X
  let p := (i.2.1-i.1,i.2.2)
  have hmem : b-a∈(ModuleCat.subobjectModule (syntheticHomotopy X p)) (P.F (i.1+1) p) := by
    simpa only [P,p,FiltrationAtLeast,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hb
  obtain ⟨z,hz⟩ := hmem
  let j := Subobject.ofLE (P.F (i.1+1) p) (P.F i.1 p) (P.mono i.1 p)
  refine ⟨e,he,a'+j z,?_,?_⟩
  · rw [map_add]
    have hj : (P.F i.1 p).arrow (j z)=(P.F (i.1+1) p).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.mono i.1 p)) z
    rw [hj,ha',hz]
    abel
  · rw [map_add]
    have hj : P.toAssociatedGraded i.1 p (j z)=0 :=
      ConcreteCategory.congr_hom (cokernel.condition j) z
    rw [hj,add_zero]
    exact hga
private theorem filtration_step_of_infinity_zero
    {H' : SyntheticSpectrum} {unit : S_0_0 ⟶ H'}
    {F : SyntheticAdamsFamily SyntheticSpectrum} {X : SyntheticSpectrum}
    {T : SyntheticTowerPresentation unit F} (c : SyntheticTowerConvergence T X)
    (s m w : ℤ) (hzero : IsZero ((F.obj X).sequence.ssData (s,m+s,w)).eInfty)
    (a : BiHom m w X) (ha : FiltrationAtLeast T s a) :
    FiltrationAtLeast T (s+1) a := by
  let P := T.filtration X
  have hz : IsZero (P.associatedGraded s (m,w)) := by
    simpa only [add_sub_cancel_right] using
      (c.identification (s,m+s,w)).isZero_iff.mp hzero
  have hmem : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) (P.F s (m,w)) := by
    simpa only [P, FiltrationAtLeast, SyntheticTowerPresentation.filtration,
      OrderIso.apply_symm_apply] using ha
  obtain ⟨a',ha'⟩ := hmem
  have hgrade : P.toAssociatedGraded s (m,w) a' = 0 :=
    (ModuleCat.subsingleton_of_isZero hz).elim _ _
  have hnext := (P.toAssociatedGraded_eq_zero_iff s (m,w) a').mp hgrade
  rw [ha'] at hnext
  simpa only [P, FiltrationAtLeast, SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply] using hnext

private theorem subquotient_subsingleton_of_le {R A : Type*} [Ring R]
    [AddCommGroup A] [Module R A] (Z B : Submodule R A) (h : Z ≤ B) :
    Subsingleton (KIP126.Literature.E2Subquotient Z B) := by
  have allzero : ∀ x : KIP126.Literature.E2Subquotient Z B, x = 0 := by
    intro x
    obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h a.property)
  exact ⟨fun x y => (allzero x).trans (allzero y).symm⟩

private theorem permanentQuotient_zero_of_page_zero
    (X : ClassicalObject) (r b : ℤ) (p : ℤ × ℤ) (hr : 2 ≤ r) (hb : r-1 ≤ b)
    (hpage : Subsingleton ((model.classical.obj (X.obj model.auxiliary)).Page r p)) :
    Subsingleton (KIP126.Literature.PermanentQuotient model X b p) := by
  let E := (model.classical.obj (X.obj model.auxiliary)).ssData p
  let n : WithTop ℕ := ↑(r-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat
  have hn : (↑(r-1-1).toNat : WithTop ℕ) = n := by
    dsimp only [n]
    rw [model.classical.firstPage]
    congr 2
    omega
  have hcycles : KIP126.Literature.permanentCycles model X p ≤
      KIP126.Literature.boundaries model X (r-1) p := by
    rintro x ⟨z,hz⟩
    let zf := (Subobject.ofLE (E.Z ⊤) (E.Z n) (E.Z_anti le_top)) z
    have hzero : E.pageπ n zf = 0 := hpage.elim _ _
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (E.B n) (E.Z n) (E.B_le_Z n)) zf).mp hzero
    change ∃ y, KIP126.Literature.boundaryLabel model X (↑(r-1-1).toNat) p y = x
    rw [hn]
    refine ⟨y, ?_⟩
    have hfactor : Subobject.ofLE (E.B n) (E.Z n) (E.B_le_Z n) ≫
        KIP126.Literature.cycleLabel model X n p =
        KIP126.Literature.boundaryLabel model X n p := by
      simp only [KIP126.Literature.cycleLabel,KIP126.Literature.boundaryLabel,E,
        ←Category.assoc,Subobject.ofLE_comp_ofLE]
    rw [←hfactor,ModuleCat.comp_apply,hy]
    have htop : Subobject.ofLE (E.Z ⊤) (E.Z n) (E.Z_anti le_top) ≫
        KIP126.Literature.cycleLabel model X n p =
        KIP126.Literature.cycleLabel model X ⊤ p := by
      simp only [KIP126.Literature.cycleLabel,E,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact (congrArg (fun f => f z) htop).trans hz
  have hle : KIP126.Literature.permanentCycles model X p ≤
      KIP126.Literature.boundaries model X b p :=
    hcycles.trans (KIP126.Literature.boundaries_monotone model X p hb)
  exact subquotient_subsingleton_of_le _ _ hle

end
end KIP126.Main.Internal.Choice
end
