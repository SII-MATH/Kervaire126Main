module
public import KIP126.AdamsSynthetic.Standard.ClassicalSupport
import all KIP126.Main.Internal.Selected.Exhaustion
import all KIP126.Main.Internal.Selected.InfinityFrames
import all KIP126.Main.Internal.Selected.ProductDetection

/-! The stable-boundary and filtration consequences of the finite stem-124
calculations. Pinned Selected/ThetaData:742–841,1693–1750,1953–2020. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Kervaire.Route KIP126.Literature
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem classical_infinity_generated_of_normalized (p : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p)
    (hx : InfinityGenerated Normalized.sphere p (Normalized.label p x)) :
    InfinityGenerated model.classical.sphere p x := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E'.Page 2 p)
      (hx : InfinityGenerated E p ((eqToHom (congrArg (fun A => A.Page 2 p) h.symm)) x)) :
      InfinityGenerated E' p x := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ Normalized.sphere_eq x hx

private theorem correction_infinity_generated :
    InfinityGenerated model.classical.sphere (13,137) KIP126.Computation.Standard.correction := by
  apply classical_infinity_generated_of_normalized
  have h := stem124_af13_exhaustion
  rw [← Normalized.label_basis, KIP126.Computation.Table.basis_correction] at h
  exact h

private theorem u_infinity_generated :
    InfinityGenerated model.classical.sphere (10,134) KIP126.Computation.Standard.U := by
  apply classical_infinity_generated_of_normalized
  have h := stem124_af10_exhaustion
  rw [← Normalized.label_basis, KIP126.Computation.Table.basis_U] at h
  exact h

private theorem no_outgoing_stem125_low (s : ℤ) (hs : s≤4) (r : ℤ) (hr : 2≤r)
    (x : Normalized.sphere.Page r (s,s+125)) : Normalized.sphere.d r (s,s+125) x=0 := by
  have hz : Subsingleton (Normalized.sphere.Page 2 (s,s+125)) := by
    by_cases hn : s<0
    · rw [Normalized.sphere_eq]
      exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere 2 s (s+125) hn
    · rw [Normalized.sphere_eq]
      have h := KIP126.Computation.Standard.e2_stem125_low s.toNat (by omega)
      simpa only [Int.toNat_of_nonneg (by omega : 0≤s)] using h
  have hz' := page_subsingleton_of_le 2 r s (s+125) (by decide) hr hz
  rw [hz'.elim x 0,map_zero]

private theorem classical_low_infinity_zero (s : ℤ) (hs : s<10) :
    Subsingleton ((model.classical.sphere.ssData (s,s+124)).eInfty) := by
  let E := Normalized.sphere
  change Subsingleton ((E.ssData (s,s+124)).eInfty)
  have collapse (r : ℤ) (hp : Subsingleton (E.Page r (s,s+124))) :
      Subsingleton ((E.ssData (s,s+124)).eInfty) := by
    let A := E.ssData (s,s+124)
    haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
    refine ⟨fun x y => ?_⟩
    obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance x
    obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
    exact A.infinity_projection_eq_of_page_projection_eq ↑(r-E.r₀).toNat x y (hp.elim _ _)
  by_cases hn : s<0
  · apply collapse 2
    change Subsingleton (Normalized.sphere.Page 2 (s,s+124))
    rw [Normalized.sphere_eq]
    exact KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere 2 s (s+124) hn
  have hs0 : 0≤s := by omega
  by_cases hsmall : s≤5
  · have hd : (⟨.sphere,s.toNat,(s+124).toNat,[]⟩ : KIP126.Computation.Table.Raw.Degree) ∈ KIP126.Computation.Table.Raw.degrees := by
      interval_cases s <;> simp [KIP126.Computation.Table.Raw.degrees]
    obtain ⟨e,_⟩ := Normalized.basis_correct _ hd
    change Normalized.Page .sphere s.toNat (s+124).toNat ≃ₗ[ℤ] (Fin 0 →₀ ZMod 2) at e
    have he : Subsingleton (Normalized.Page .sphere s.toNat (s+124).toNat) := e.injective.subsingleton
    apply collapse 2
    simpa only [Normalized.Page,Int.toNat_of_nonneg hs0,
      Int.toNat_of_nonneg (by omega : 0≤s+124)] using he
  have hf := stem124_finite_pages
  interval_cases s
  · exact collapse 6 hf.1
  · exact collapse 6 hf.2.1
  · exact collapse 3 hf.2.2.1
  · exact collapse 4 hf.2.2.2

private theorem infinity_zero_boundary_mem (p : ℤ×ℤ) (b : ℤ)
    (hB : (model.classical.sphere.ssData p).B ⊤=(model.classical.sphere.ssData p).B ↑(b-1).toNat)
    (z : (Subobject.underlying.obj ((model.classical.sphere.ssData p).Z ⊤) : ModuleCat ℤ))
    (hz : (model.classical.sphere.ssData p).pageπ ⊤ z=0) :
    cycleLabel model .sphere ⊤ p z ∈ boundaries model .sphere b p := by
  let A := model.classical.sphere.ssData p
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (A.B ⊤) (A.Z ⊤) (A.B_le_Z ⊤)) z).mp hz
  refine ⟨(Subobject.ofLE _ _ hB.le) y,?_⟩
  rw [←hy]
  change (Subobject.ofLE _ _ hB.le ≫ boundaryLabel model .sphere ↑(b-1).toNat p) y =
    (Subobject.ofLE _ _ (A.B_le_Z ⊤) ≫ cycleLabel model .sphere ⊤ p) y
  congr 1
  dsimp only [boundaryLabel,cycleLabel,A,ClassicalAdamsFamily.sphere,ClassicalObject.obj]
  simp only [←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem permanent_quotient_zero_of_stable_boundaries (p : ℤ×ℤ) (b : ℤ)
    (hz : Subsingleton ((model.classical.sphere.ssData p).eInfty))
    (hB : (model.classical.sphere.ssData p).B ⊤=(model.classical.sphere.ssData p).B ↑(b-1).toNat) :
    Subsingleton (PermanentQuotient model .sphere b p) := by
  have hall (a : PermanentQuotient model .sphere b p) : a=0 := by
    obtain ⟨x,rfl⟩ := Quotient.exists_rep a
    obtain ⟨z,hz'⟩ := x.property
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    rw [←hz']
    exact infinity_zero_boundary_mem p b hB z (hz.elim _ _)
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem theta_quotient_frame (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : model.classical.sphere.Page 2 (s,t)) (hx : InfinityGenerated model.classical.sphere (s,t) x) :
    ∃ x' : permanentCycles model .sphere (s,t), x'.val=x ∧
      ∀ q : PermanentQuotient model .sphere (1+(k:ℤ)) (s,t), q=0 ∨ q=subquotientClass _ _ x' := by
  let E := Normalized.sphere
  let A := E.ssData (s,t)
  have hB : A.B ⊤=A.B (k:WithTop ℕ) := by
    have hin (r : ℤ) (hr : (k:ℤ)+2≤r) : E.d r ((s,t)-E.diffDeg r)=0 := by
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low (s-r) (by omega) r (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change A.B ⊤=A.B ↑((k:ℤ)+2-2).toNat at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  have hz' : cycleLabel model .sphere ⊤ (s,t) z=x := by
    have norm (P : SSData (ModuleCat ℤ)) (n : WithTop ℕ) (hn : n=0) :
        Subobject.ofLE (P.Z ⊤) (P.Z n) (P.Z_anti le_top) ≫ P.pageπ n =
          Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0 ≫
            eqToHom (congrArg P.page hn.symm) := by
      subst n
      simp only [eqToHom_refl,Category.comp_id]
    have hn := norm (model.classical.sphere.ssData (s,t)) (↑(2-model.classical.sphere.r₀).toNat)
      (by rw [model.classical.firstPage]; rfl)
    exact (congrArg (fun f => f z) hn).symm.trans hz
  let x' : permanentCycles model .sphere (s,t) := ⟨x,⟨z,hz'⟩⟩
  refine ⟨x',rfl,?_⟩
  intro q
  obtain ⟨y,rfl⟩ := Quotient.exists_rep q
  obtain ⟨z',hz''⟩ := y.property
  have zero_mem (v : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat ℤ)) (hv : A.pageπ ⊤ v=0) :
      cycleLabel model .sphere ⊤ (s,t) v∈boundaries model .sphere (1+(k:ℤ)) (s,t) := by
    apply infinity_zero_boundary_mem (s,t) (1+(k:ℤ)) _ v hv
    have hb := hB
    change (Normalized.sphere.ssData (s,t)).B ⊤=(Normalized.sphere.ssData (s,t)).B ↑k at hb
    rw [Normalized.sphere_eq] at hb
    simpa only [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast] using hb
  rcases hall (A.pageπ ⊤ z') with h0|h1
  · left
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    rw [←hz'']
    exact zero_mem z' h0
  · right
    apply sub_eq_zero.mp
    change subquotientClass _ _ y-subquotientClass _ _ x'=0
    rw [←map_sub]
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change y.val-x'.val∈_
    have hzX : cycleLabel model .sphere ⊤ (s,t) z=x'.val := hz'
    rw [←hz'',←hzX,←map_sub]
    let z0 : (Subobject.underlying.obj (((model.classical.obj (ClassicalObject.sphere.obj model.auxiliary)).ssData (s,t)).Z ⊤) : ModuleCat ℤ) := z
    exact zero_mem (z'-z0) (by rw [map_sub,h1]; exact sub_self _)

private theorem theta_sphere_frame (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : model.classical.sphere.Page 2 (s,t)) (hx : InfinityGenerated model.classical.sphere (s,t) x) :
    ∀ e : (model.family.sphere.sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative model.family.sphere 2 (s,t,t-k)
        (model.comparison.sphereE2 s t k x) e := by
  apply sphere_frame_of_permanent_quotient
  rw [show 1+t-(t-(k:ℤ))=1+(k:ℤ) by omega]
  exact theta_quotient_frame s t k hst hsk x hx

private theorem stem124_weight128_filtration_ten (a : BiHom 124 128 (S_0_0 : SyntheticSpectrum)) :
    FiltrationAtLeast model.syntheticTower 10 a := by
  have ha0 : FiltrationAtLeast model.syntheticTower 0 a := by
    refine ⟨a ≫ (model.syntheticTower.tower (S_0_0 : SyntheticSpectrum)).zeroIso.inv,?_⟩
    change (a ≫ (model.syntheticTower.tower _).zeroIso.inv) ≫ (model.syntheticTower.tower _).projection 0=a
    simp only [AbstractAdamsTower.projection,Int.toNat_zero,(model.syntheticTower.tower _).map_self]
    erw [Category.assoc,Category.id_comp,Iso.inv_hom_id,Category.comp_id]
  apply (filtration_iff_of_infinity_zero (model.convergence .sphere) 0 10 124 128 (by decide) ?_ a).mp ha0
  intro s hs hs10
  by_cases hw : 128≤124+s
  · apply sphere_infinity_zero_of_permanent_quotient_zero s (124+s) 128 hw
    have hz : Subsingleton ((model.classical.sphere.ssData (s,124+s)).eInfty) := by
      simpa only [add_comm] using classical_low_infinity_zero s hs10
    apply permanent_quotient_zero_of_stable_boundaries (s,124+s) (1+(124+s)-128) hz
    let E := Normalized.sphere
    have hin (r : ℤ) (hr : s-2≤r) : E.d r ((s,124+s)-E.diffDeg r)=0 := by
      have hi : (s,124+s)-E.diffDeg r=(s-r,(s-r)+125) := by
        change (s,124+s)-(r,r-1)=_
        ext <;> dsimp
        omega
      rw [hi]
      ext z
      exact no_outgoing_stem125_low (s-r) (by omega) r (by omega) z
    have hB := boundaries_top_eq_of_d_eq_zero E (s-2) (by change (2:ℤ)≤s-2; omega) (s,124+s) hin
    change (E.ssData (s,124+s)).B ⊤=(E.ssData (s,124+s)).B ↑(s-2-2).toNat at hB
    dsimp only [E] at hB
    rw [Normalized.sphere_eq] at hB
    simpa only [show s-2-2=1+(124+s)-128-1 by omega] using hB
  · haveI : Subsingleton (nuEInftyModel model .sphere (s,124+s) 128) := by
      simp only [nuEInftyModel,hw,ite_false]
      infer_instance
    haveI : Subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty) :=
      (KIP126.Literature.Standard.eInfinity_nu .sphere (s,124+s) 128).injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton (((model.family.nu model.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty)
    let f := (model.family.map model.nu.unitIso.hom).eInftyMap (s,124+s,128)
    let g := (model.family.map model.nu.unitIso.inv).eInftyMap (s,124+s,128)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←SyntheticAdamsFamily.map_comp,Iso.inv_hom_id,
        SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,comp_zero])

private theorem theta_three_cases (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    Theta5SquareNonzeroDetectionAt theta ∨
      DetectsNonzero (model.convergence .sphere) (13,137,128)
        (model.comparison.sphereE2 13 137 9 KIP126.Computation.Standard.correction) (sphereProduct theta theta) ∨
      ∃ a : BiHom 124 138 (S_0_0 : SyntheticSpectrum), lambdaMultiply 10 a=sphereProduct theta theta := by
  have h10 := theta_sphere_frame 10 134 6 (by decide) (by decide) _ u_infinity_generated
  have h13 := theta_sphere_frame 13 137 9 (by decide) (by decide) _ correction_infinity_generated
  rcases theta_detection_step (10,134,128) _ h10 (sphereProduct theta theta)
    (stem124_weight128_filtration_ten _) with hdet|ha11
  · exact Or.inl hdet
  exact Or.inr (stem124_weight128_filtration11_branches h13 _ ha11)

end
end KIP126.Main.Internal.Selected
