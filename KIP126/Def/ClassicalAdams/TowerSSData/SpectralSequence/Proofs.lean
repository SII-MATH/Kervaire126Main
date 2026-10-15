module

public import KIP126.Def.ClassicalAdams.TowerSSData.NextBoundaries.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Unfold the admissible-page differential without unfolding its categorical instances. -/
theorem adamsTowerPreSS_d_eq (r : ℤ) (p : ℤ × ℤ) (hr : 2 ≤ r) :
    (adamsTowerPreSS unit X).d r p =
      adamsTowerInternalD unit X (r - 2).toNat p.1 p.2 ≫ eqToHom (by
        have hn : (((r - 2).toNat + 2 : ℕ) : ℤ) = r := by omega
        change (adamsTowerSSData unit X
          (p.1 + ((r - 2).toNat + 2 : ℕ))
          (p.2 + ((r - 2).toNat + 2 : ℕ) - 1)).page ↑(r - 2).toNat =
            (adamsTowerSSData unit X (p.1 + r) (p.2 + (r - 1))).page ↑(r - 2).toNat
        rw [hn]
        congr 2; omega) := by
  exact dif_pos hr

/-- Square-zero is unchanged by the coordinate equalities used in `PreSS`. -/
theorem adamsTowerInternalD_comp_reindex (n : ℕ) (s t a b : ℤ)
    (ha : s + (n + 2 : ℕ) = a) (hb : t + (n + 2 : ℕ) - 1 = b)
    (W : ModuleCat.{v} ℤ)
    (hW : (adamsTowerSSData unit X (a + (n + 2 : ℕ))
      (b + (n + 2 : ℕ) - 1)).page (n : WithTop ℕ) = W) :
    adamsTowerInternalD unit X n s t ≫
      eqToHom (show (adamsTowerSSData unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1)).page (n : WithTop ℕ) =
          (adamsTowerSSData unit X a b).page (n : WithTop ℕ) by rw [ha, hb]) ≫
      adamsTowerInternalD unit X n a b ≫ eqToHom hW = 0 := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.id_comp, ← Category.assoc]
  rw [adamsTowerInternalD_comp, zero_comp]

/-- The image calculation is unchanged by coordinate reindexing. -/
theorem adamsTowerInternalD_image_reindex (n : ℕ) (s t a b : ℤ)
    (ha : s + (n + 2 : ℕ) = a) (hb : t + (n + 2 : ℕ) - 1 = b) :
    imageSubobject (adamsTowerInternalD unit X n s t ≫
      eqToHom (show (adamsTowerSSData unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1)).page (n : WithTop ℕ) =
          (adamsTowerSSData unit X a b).page (n : WithTop ℕ) by rw [ha, hb])) =
      imageSubobject (Subobject.ofLE
        ((adamsTowerSSData unit X a b).B ((n + 1 : ℕ) : WithTop ℕ))
        ((adamsTowerSSData unit X a b).Z (n : WithTop ℕ))
        (le_trans ((adamsTowerSSData unit X a b).B_le_Z ((n + 1 : ℕ) : WithTop ℕ))
          ((adamsTowerSSData unit X a b).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (adamsTowerSSData unit X a b).pageπ (n : WithTop ℕ)) := by
  subst a
  subst b
  simpa only [eqToHom_refl, Category.comp_id] using adamsTowerInternalD_image unit X s t n

/-- Every integer-indexed internal page differential squares to zero. -/
theorem adamsTowerPreSS_d_comp_d (r : ℤ) (p : ℤ × ℤ) :
    (adamsTowerPreSS unit X).d r p ≫
      (adamsTowerPreSS unit X).d r (p + (adamsTowerPreSS unit X).diffDeg r) = 0 := by
  by_cases hr : 2 ≤ r
  · have hn : (((r - 2).toNat + 2 : ℕ) : ℤ) = r := by omega
    dsimp only [adamsTowerPreSS]
    rw [dif_pos hr, dif_pos hr, Category.assoc]
    exact adamsTowerInternalD_comp_reindex unit X (r - 2).toNat p.1 p.2
      (p + (r, r - 1)).1 (p + (r, r - 1)).2
      (by dsimp; omega) (by dsimp; omega) _ _
  · simp only [adamsTowerPreSS, dif_neg hr, zero_comp]

/-- The integer-indexed kernel law is the proved tower next-cycle law. -/
theorem adamsTowerPreSS_Z_succ (r : ℤ) (p : ℤ × ℤ) (hr : 2 ≤ r) :
    let n := (r - 2).toNat
    kernelSubobject ((adamsTowerPreSS unit X).d r p) =
      imageSubobject (Subobject.ofLE
        (((adamsTowerPreSS unit X).ssData p).Z ((n + 1 : ℕ) : WithTop ℕ))
        (((adamsTowerPreSS unit X).ssData p).Z (n : WithTop ℕ))
        (((adamsTowerPreSS unit X).ssData p).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        ((adamsTowerPreSS unit X).ssData p).pageπ (n : WithTop ℕ)) := by
  exact (congrArg (fun f => kernelSubobject f) (adamsTowerPreSS_d_eq unit X r p hr)).trans
    ((kernelSubobject_comp_mono _ _).trans
      (adamsTowerInternalD_kernel unit X p.1 p.2 (r - 2).toNat))

/-- The integer-indexed image law is the proved tower next-boundary law. -/
theorem adamsTowerPreSS_B_succ (r : ℤ) (p : ℤ × ℤ) (hr : 2 ≤ r) :
    let n := (r - 2).toNat
    let D := (adamsTowerPreSS unit X).ssData (p + (adamsTowerPreSS unit X).diffDeg r)
    imageSubobject ((adamsTowerPreSS unit X).d r p) =
      imageSubobject (Subobject.ofLE (D.B ((n + 1 : ℕ) : WithTop ℕ))
        (D.Z (n : WithTop ℕ))
        (le_trans (D.B_le_Z ((n + 1 : ℕ) : WithTop ℕ))
          (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫ D.pageπ (n : WithTop ℕ)) := by
  have hn : (((r - 2).toNat + 2 : ℕ) : ℤ) = r := by omega
  have him := adamsTowerInternalD_image_reindex unit X (r - 2).toNat p.1 p.2
    (p + (r, r - 1)).1 (p + (r, r - 1)).2
    (by dsimp; omega) (by dsimp; omega)
  simpa only [adamsTowerPreSS, dif_pos hr] using him

end
end KIP126.Classical.Adams
