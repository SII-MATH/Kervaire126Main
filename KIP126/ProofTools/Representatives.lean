module

public import KIP126.ProofTools.Language

/-! Page-label transport from the proved auxiliary steps of AimPaper's
GeneralizedLeibniz/Proofs.lean at bbac1fc05843 (MIT; see the retained source LICENSE). -/

@[expose] section
namespace KIP126.ProofTools
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
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

private theorem initialProjection_eq_cycleLabel (X : ClassicalObject) (r : ℤ)
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

public theorem isCycle_iff_reaches (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (x : Ambient D X p) :
    IsCycle D X (r-1) p x ↔ ReachesPage (D.classical.obj (X.obj D.auxiliary)) r p x := by
  let E := D.classical.obj (X.obj D.auxiliary)
  let P := E.ssData p
  let m : WithTop ℕ := ↑(r-E.r₀).toNat
  have hm : (↑(r-1-1).toNat : WithTop ℕ) = m := by
    dsimp only [m, E]
    rw [D.classical.firstPage]
    congr 2; omega
  constructor
  · rintro ⟨_, hx⟩
    change ∃ z, KIP126.Literature.cycleLabel D X (↑(r-1-1).toNat) p z = x at hx
    rw [hm] at hx
    obtain ⟨z,hz⟩ := hx
    refine ⟨P.pageπ m z, hr, z, ?_, rfl⟩
    change (Subobject.ofLE (P.Z m) (P.Z _) _ ≫ P.pageπ _) z = x
    rw [initialProjection_eq_cycleLabel D X r hr p]
    exact hz
  · rintro ⟨y, _, z, hz, _⟩
    refine ⟨by omega, ?_⟩
    change ∃ z, KIP126.Literature.cycleLabel D X (↑(r-1-1).toNat) p z = x
    rw [hm]
    refine ⟨z, ?_⟩
    rw [initialProjection_eq_cycleLabel D X r hr p] at hz
    exact hz

public theorem representsOnPage_of_congruent (X : ClassicalObject) {R : ℤ}
    (hR : 2 ≤ R) {p : ℤ × ℤ} {x y : Ambient D X p}
    {xr : (D.classical.obj (X.obj D.auxiliary)).Page R p}
    (hx : RepresentsOnPage (D.classical.obj (X.obj D.auxiliary)) R p x xr)
    (hy : Congruent D X (R - 1) p y x) :
    RepresentsOnPage (D.classical.obj (X.obj D.auxiliary)) R p y xr := by
  let E := D.classical.obj (X.obj D.auxiliary)
  let P := E.ssData p
  let k : WithTop ℕ := ↑(R - E.r₀).toNat
  obtain ⟨_, z, hzx, hzr⟩ := hx
  have hb : y - x ∈ KIP126.Literature.boundaries D X (R - 1) p := hy.2
  change ∃ b, KIP126.Literature.boundaryLabel D X (↑(R - 1 - 1).toNat) p b = y - x at hb
  have hk : (↑(R-1-1).toNat : WithTop ℕ) = k := by
    dsimp only [k,E]
    rw [D.classical.firstPage]
    congr 2; omega
  rw [hk] at hb
  obtain ⟨b, hb⟩ := hb
  let j := Subobject.ofLE (P.B k) (P.Z k) (P.B_le_Z k)
  have hlabel : j ≫ KIP126.Literature.cycleLabel D X k p =
      KIP126.Literature.boundaryLabel D X k p := by
    dsimp only [j, KIP126.Literature.cycleLabel, KIP126.Literature.boundaryLabel, P, E]
    simp only [← Category.assoc, Subobject.ofLE_comp_ofLE]
  have hboundary : (P.pageπ k) (j b) = 0 := by
    have hj : j ≫ P.pageπ k = 0 := cokernel.condition _
    exact congrArg (fun f => f b) hj
  refine ⟨hR, z + j b, ?_, ?_⟩
  · have hz0 : KIP126.Literature.cycleLabel D X k p z = x := by
      rw [initialProjection_eq_cycleLabel D X R hR p] at hzx
      exact hzx
    have hzb : KIP126.Literature.cycleLabel D X k p (j b) = y - x := by
      change (j ≫ KIP126.Literature.cycleLabel D X k p) b = _
      rw [hlabel]
      exact hb
    have hh : KIP126.Literature.cycleLabel D X k p (z + j b) = y := by
      rw [map_add, hz0, hzb]
      abel
    change (Subobject.ofLE (P.Z k) (P.Z _) _ ≫ P.pageπ _) (z+j b) = y
    rw [initialProjection_eq_cycleLabel D X R hR p]
    exact hh
  · change P.pageπ k (z + j b) = xr
    rw [map_add, hboundary, add_zero]
    exact hzr

public theorem differentialAt_of_congruent (X : ClassicalObject) {R : ℤ}
    {p q : ℤ × ℤ} {x : Ambient D X p} {y z : Ambient D X q}
    (hd : DifferentialAt D X R p q x y)
    (hz : Congruent D X (R - 1) q z y) :
    DifferentialAt D X R p q x z := by
  obtain ⟨hR, hdeg, xr, yr, hx, hy, hdiff⟩ := hd
  exact ⟨hR, hdeg, xr, yr, hx, representsOnPage_of_congruent D X hR hy hz, hdiff⟩

end
end KIP126.ProofTools
