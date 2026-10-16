module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem cumulative_boundary_permanent (X : ClassicalObject) (b : ℤ)
    (p : Bidegree) (y : Ambient model X p)
    (hy : y ∈ boundaries model X b p) : ClassicalPermanentCycle model X p y := by
  obtain ⟨z,hz⟩ := hy
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData p
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  let j := Subobject.ofLE (P.B (↑(b-1).toNat)) (P.Z ⊤)
    ((P.B_mono le_top).trans (P.B_le_Z ⊤))
  refine ⟨j z,?_⟩
  change (j ≫ Subobject.ofLE (P.Z ⊤) (P.Z n₀) (P.Z_anti le_top) ≫ P.pageπ n₀) z=y
  rw [normalizeInitialProjection P n₀ ⊤ hn₀ le_top]
  change ((j ≫ Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti bot_le)) ≫ P.pageπ 0 ≫ _) z=y
  rw [show j ≫ Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti bot_le) =
    Subobject.ofLE (P.B (↑(b-1).toNat)) (P.Z 0) _ by simp only [j,Subobject.ofLE_comp_ofLE]]
  exact hz

private theorem cumulative_boundary_hit (X : ClassicalObject)
    (r : ℕ) (hr : 2 ≤ r) (p : Bidegree) (y : Ambient model X p)
    (hy : y ∈ boundaries model X r p)
    (hprev : y ∉ boundaries model X (r-1) p) :
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r p y := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData p
  let n : ℕ := ((r:ℤ)-E.r₀).toNat
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have hn' : ((r:ℤ)-1).toNat=n+1 := by dsimp [n,E]; rw [model.classical.firstPage]; omega
  change y ∈ LinearMap.range (boundaryLabel model X (↑((r:ℤ)-1).toNat) p).hom at hy
  rw [hn'] at hy
  obtain ⟨z,hz⟩ := hy
  let j := Subobject.ofLE (P.B ↑(n+1)) (P.Z ↑n)
    ((P.B_le_Z _).trans (P.Z_anti (by exact_mod_cast Nat.le_succ n)))
  let yr : E.Page r p := P.pageπ ↑n (j z)
  have hyr : RepresentsOnPage E r p y yr := by
    refine ⟨by omega,j z,?_,rfl⟩
    change (j ≫ Subobject.ofLE (P.Z ↑n) (P.Z n₀) _ ≫ P.pageπ n₀) z=y
    rw [normalizeInitialProjection P n₀ ↑n hn₀ (by rw [hn₀]; exact bot_le)]
    change ((j ≫ Subobject.ofLE (P.Z ↑n) (P.Z 0) _) ≫ P.pageπ 0 ≫ _) z=y
    rw [show j ≫ Subobject.ofLE (P.Z ↑n) (P.Z 0) _ =
      Subobject.ofLE (P.B ↑(n+1)) (P.Z 0) _ by simp only [j,Subobject.ofLE_comp_ofLE]]
    exact hz
  have hyrne : yr ≠ 0 := by
    intro hyrzero
    exact hprev (represents_zero_mem_boundary model X r p y (by simpa only [E,hyrzero] using hyr))
  let q := p-E.diffDeg r
  have hqp : q+E.diffDeg r=p := by dsimp [q]; abel
  have himage : yr ∈ LinearMap.range (E.d r q ≫ eqToHom (congrArg (E.Page r) hqp)).hom := by
    have h := congrArg (ModuleCat.subobjectModule (E.Page r (q+E.diffDeg r)))
      (E.B_succ r q (by dsimp [E]; rw [model.classical.firstPage]; omega))
    simp only [subobjectModule_image] at h
    have transport (p' : Bidegree) (hp : p'=p)
        (d : E.Page r q ⟶ E.Page r p')
        (hd : LinearMap.range d.hom = LinearMap.range
          (Subobject.ofLE ((E.ssData p').B ↑(n+1)) ((E.ssData p').Z ↑n)
            (((E.ssData p').B_le_Z _).trans ((E.ssData p').Z_anti
              (by exact_mod_cast Nat.le_succ n))) ≫
            (E.ssData p').pageπ ↑n).hom) :
        yr ∈ LinearMap.range (d ≫ eqToHom (congrArg (E.Page r) hp)).hom := by
      subst p'
      simp only [eqToHom_refl,Category.comp_id,hd]
      exact ⟨z,rfl⟩
    exact transport _ hqp (E.d r q) h
  obtain ⟨a,ha⟩ := himage
  exact ⟨q,hqp,a,yr,hyr,hyrne,ha⟩

private theorem lambdaMultiply_zero_of_le {A : SyntheticSpectrum} (m w : ℤ)
    (i j : ℕ) (hij : i ≤ j) (a : BiHom m w A)
    (ha : lambdaMultiply i a=0) : lambdaMultiply j a=0 := by
  simp only [lambdaMultiply,comp_eq_zero_iff_of_epi] at ha ⊢
  rw [lambdaPow_add model.quotients.coherence (j-i) i j (Nat.sub_add_cancel hij) _,
    Category.assoc,Category.assoc,ha,comp_zero,comp_zero]

private theorem cumulative_boundary_torsion_lift (X : ClassicalObject)
    (k : ℕ) (s t : ℤ) (y : Ambient model X (s,t))
    (hy : y ∈ boundaries model X (k+1) (s,t)) :
    ∃ a : BiHom (t-s) t (nuZero model X),
      quotientClass 1 a=firstLabel model X s t y ∧ lambdaMultiply k a=0 := by
  induction k with
  | zero =>
    have hyzero : y=0 := by
      simpa only [Nat.cast_zero,zero_add,boundaries_one,Submodule.mem_bot] using hy
    subst y
    refine ⟨0,?_,?_⟩
    · have cast_zero (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w=w')
          (he : BiHom m w A = BiHom m w' A) : he.mp 0=0 := by subst w'; rfl
      simp only [quotientClass,zero_comp,firstLabel,map_zero]
      rw [cast_zero _ _ _ _ (Int.add_zero t)]
    · simp only [lambdaMultiply,comp_zero]
  | succ k ih =>
    by_cases hprev : y ∈ boundaries model X (k+1) (s,t)
    · obtain ⟨a,ha,hak⟩ := ih hprev
      exact ⟨a,ha,lambdaMultiply_zero_of_le (t-s) t k (k+1) (by omega) a hak⟩
    · have hy' : y ∈ boundaries model X (k+2) (s,t) := by
        simpa only [Nat.cast_succ,add_assoc,Int.reduceAdd] using hy
      have hhit := cumulative_boundary_hit X (k+2) (by omega) (s,t) y hy'
        (by simpa only [show ((k+2:ℕ):ℤ)-1=(k:ℤ)+1 by omega] using hprev)
      obtain ⟨a,ha,hak⟩ := KIP126.Literature.Standard.selected_realization_boundary_lift X s t
        (k+2) (by omega) y (cumulative_boundary_permanent X _ (s,t) y hy') hhit
      have hk : (k+2:ℕ)-1=k+1 := by omega
      rw [hk] at hak
      exact ⟨a,ha,hak⟩

private theorem cumulative_boundary_torsion_lift_unshifted (X : ClassicalObject)
    (k : ℕ) (s t : ℤ) (y : Ambient model X (s,t))
    (hy : y ∈ boundaries model X (k+1) (s,t)) :
    ∃ a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      lambdaMultiply k a=0 := by
  obtain ⟨a,ha,hak⟩ := cumulative_boundary_torsion_lift X k s t y hy
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let z : nuZero model X ⟶ A := SyntheticCategory.biShift_zero.hom.app A
  refine ⟨a ≫ z,?_,?_⟩
  · rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    exact congrArg (fun f => f ≫ XModLambdaN.map z 1) ha
  · simpa only [lambdaMultiply,Category.assoc,zero_comp] using congrArg (fun f => f ≫ z) hak

end
end KIP126.ProofTools.Internal.Mahowald
