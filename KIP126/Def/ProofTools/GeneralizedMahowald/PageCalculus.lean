module
public import KIP126.Def.ProofTools.Representatives
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs

/-! Page-calculus steps of the existing Mahowald proof, adapted from
bbac1fc05843 GeneralizedMahowald/Proofs.lean (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
set_option backward.isDefEq.respectTransparency false
private theorem normalizeInitialProjection
    (P : SSData (ModuleCat.{v} ℤ)) (n m : WithTop ℕ)
    (hn : n = 0) (hnm : n ≤ m) :
    Subobject.ofLE (P.Z m) (P.Z n) (P.Z_anti hnm) ≫ P.pageπ n =
      Subobject.ofLE (P.Z m) (P.Z 0) (P.Z_anti bot_le) ≫ P.pageπ 0 ≫
        eqToHom (congrArg P.page hn.symm) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]

theorem initialProjection_eq_cycleLabel (X : ClassicalObject) (r : ℤ)
    (hr : 2 ≤ r) (p : ℤ × ℤ) :
    let E := D.classical.obj (X.obj D.auxiliary)
    let P := E.ssData p
    let n : WithTop ℕ := ↑(2-E.r₀).toNat
    let m : WithTop ℕ := ↑(r-E.r₀).toNat
    Subobject.ofLE (P.Z m) (P.Z n)
      (P.Z_anti (by
        change (↑(2-E.r₀).toNat : WithTop ℕ) ≤ ↑(r-E.r₀).toNat
        exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega))) ≫
      P.pageπ n = KIP126.Literature.cycleLabel D X m p := by
  dsimp only
  exact normalizeInitialProjection _ _ _ (by rw [D.classical.firstPage]; rfl)
    (by exact_mod_cast (show (2-(D.classical.obj (X.obj D.auxiliary)).r₀).toNat ≤
      (r-(D.classical.obj (X.obj D.auxiliary)).r₀).toNat by omega))


theorem boundaries_le_cycles (X : ClassicalObject) (p : Bidegree) (b c : ℤ) :
    KIP126.Literature.boundaries D X b p ≤ KIP126.Literature.cycles D X c p := by
  rintro x ⟨z,rfl⟩
  let P := (D.classical.obj (X.obj D.auxiliary)).ssData p
  let i : P.B (↑(b-1).toNat) ≤ P.Z (↑(c-1).toNat) :=
    (P.B_mono le_top).trans ((P.B_le_Z ⊤).trans (P.Z_anti le_top))
  refine ⟨Subobject.ofLE _ _ i z, ?_⟩
  change (Subobject.ofLE _ _ i ≫ KIP126.Literature.cycleLabel D X (↑(c-1).toNat) p) z = _
  simp only [KIP126.Literature.cycleLabel, KIP126.Literature.boundaryLabel, P,
    ←Category.assoc, Subobject.ofLE_comp_ofLE]

theorem boundaries_one (X : ClassicalObject) (p : Bidegree) :
    KIP126.Literature.boundaries D X 1 p = ⊥ := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    change KIP126.Literature.boundaryLabel D X 0 p z = 0
    have hz : KIP126.Literature.boundaryLabel D X 0 p = 0 := by
      dsimp only [KIP126.Literature.boundaryLabel]
      rw [←Category.assoc]
      have h := cokernel.condition (Subobject.ofLE
        (((D.classical.obj (X.obj D.auxiliary)).ssData p).B 0)
        (((D.classical.obj (X.obj D.auxiliary)).ssData p).Z 0)
        (((D.classical.obj (X.obj D.auxiliary)).ssData p).B_le_Z 0))
      change _ ≫ _ = 0
      dsimp only [SSData.pageπ]
      rw [h, zero_comp]
    rw [hz]
    rfl
  · exact bot_le

theorem represents_zero_mem_boundary (X : ClassicalObject) (r : ℤ) (p : Bidegree)
    (y : Ambient D X p)
    (hy : RepresentsOnPage (D.classical.obj (X.obj D.auxiliary)) r p y 0) :
    y ∈ KIP126.Literature.boundaries D X (r-1) p := by
  let E := D.classical.obj (X.obj D.auxiliary)
  let P := E.ssData p
  let k : WithTop ℕ := ↑(r-E.r₀).toNat
  obtain ⟨hr,z,hz,hz0⟩ := hy
  rw [initialProjection_eq_cycleLabel D X r hr p] at hz
  obtain ⟨b,hb⟩ := (P.pageπ_eq_zero_iff k z).mp hz0
  change ∃ b, KIP126.Literature.boundaryLabel D X (↑(r-1-1).toNat) p b = y
  have hk : (↑(r-1-1).toNat : WithTop ℕ) = k := by
    dsimp only [k,E]
    rw [D.classical.firstPage]
    congr 2; omega
  rw [hk]
  refine ⟨b, ?_⟩
  have hlabel : Subobject.ofLE (P.B k) (P.Z k) (P.B_le_Z k) ≫
      KIP126.Literature.cycleLabel D X k p = KIP126.Literature.boundaryLabel D X k p := by
    dsimp only [KIP126.Literature.cycleLabel, KIP126.Literature.boundaryLabel, P, E]
    simp only [←Category.assoc, Subobject.ofLE_comp_ofLE]
  rw [←hlabel, ModuleCat.comp_apply, hb]
  exact hz

theorem differential_targets_sub_mem_boundary (X : ClassicalObject)
    (r : ℤ) (p q : Bidegree) (x : Ambient D X p) (y z : Ambient D X q)
    (hy : HasDifferential (D.classical.obj (X.obj D.auxiliary)) r p q x y)
    (hz : HasDifferential (D.classical.obj (X.obj D.auxiliary)) r p q x z) :
    y-z ∈ KIP126.Literature.boundaries D X (r-1) q := by
  obtain ⟨hdeg,a,b,ha,hb,hab⟩ := hy
  obtain ⟨hdeg',a',b',ha',hb',hab'⟩ := hz
  have haa := represents_unique ha ha'
  subst a'
  have hbb : b=b' := hab.symm.trans hab'
  apply represents_zero_mem_boundary D X r q (y-z)
  simpa only [hbb,sub_self] using represents_sub hb hb'

theorem boundary_target_zero (X : ClassicalObject) (r b : ℤ)
    (p q : Bidegree) (hr : 2 ≤ r) (hbr : b ≤ r-1)
    (x : Ambient D X p) (z : Ambient D X q)
    (hz : z ∈ KIP126.Literature.boundaries D X b q)
    (hdz : HasDifferential (D.classical.obj (X.obj D.auxiliary)) r p q x z) :
    HasDifferential (D.classical.obj (X.obj D.auxiliary)) r p q x 0 := by
  apply (differentialAt_of_congruent D X ⟨hr,hdz⟩ ⟨by omega, ?_⟩).2
  simpa only [zero_sub] using
    (KIP126.Literature.boundaries D X (r-1) q).neg_mem
      (KIP126.Literature.boundaries_monotone D X q hbr hz)

end
end KIP126.ProofTools.Internal.Mahowald
