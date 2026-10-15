module

public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Data
public import KIP126.Def.ClassicalAdams.TowerDifferential.Proofs

@[expose] public section

/-!
# Internal page maps induced by the actual tower differential

Every displayed differential is obtained from the existing `j(lift(k(x)))`
formula, transported through the representative-preserving quotient isomorphism.
There is no independent choice of differential in this construction.
-/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Stage `n` corresponds to the differential on classical page `n+2`. -/
def adamsTowerInternalD (n : ℕ) (s t : ℤ) :
    (adamsTowerSSData unit X s t).page (n : WithTop ℕ) ⟶
      (adamsTowerSSData unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1)).page (n : WithTop ℕ) :=
  (adamsTowerSSDataPageIso unit X s t n).hom ≫
    ModuleCat.ofHom (adamsDifferential unit X (n + 2) (by omega) s t) ≫
    (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1) n).inv

/-- The data-only internal sequence determined by the tower. The `Z_succ` and
`B_succ` proofs, needed for a `SpectralSequence`, are separate obligations. -/
def adamsTowerPreSS : PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  r₀ := 2
  ssData p := adamsTowerSSData unit X p.1 p.2
  diffDeg r := (r, r - 1)
  d r p := if hr : 2 ≤ r then
    adamsTowerInternalD unit X (r - 2).toNat p.1 p.2 ≫ eqToHom (by
      have hn : ((r - 2).toNat + 2 : ℕ) = r.toNat := by omega
      have hrn : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (by omega)
      simp only [hn, hrn, Prod.fst_add, Prod.snd_add]
      congr 2; omega)
    else 0

end
end KIP126.Classical.Adams
