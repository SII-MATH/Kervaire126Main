module

public import KIP126.Def.ClassicalAdams.TowerSSData.Differential.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The comparison commutes with the specified differential, not just page objects. -/
theorem adamsTowerInternalD_comparison (n : ℕ) (s t : ℤ) :
    adamsTowerInternalD unit X n s t ≫
      (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1) n).hom =
      (adamsTowerSSDataPageIso unit X s t n).hom ≫
        ModuleCat.ofHom (adamsDifferential unit X (n + 2) (by omega) s t) := by
  simp [adamsTowerInternalD]

/-- The transported tower differential still squares to zero. -/
theorem adamsTowerInternalD_comp (n : ℕ) (s t : ℤ) :
    adamsTowerInternalD unit X n s t ≫
      adamsTowerInternalD unit X n (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1) = 0 := by
  have hd : ModuleCat.ofHom (adamsDifferential unit X (n + 2) (by omega) s t) ≫
      ModuleCat.ofHom (adamsDifferential unit X (n + 2) (by omega)
        (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact adamsDifferential_comp unit X (n + 2) (by omega) s t x
  have hh := congrArg (fun f => (adamsTowerSSDataPageIso unit X s t n).hom ≫ f ≫
    (adamsTowerSSDataPageIso unit X
      (s + (n + 2 : ℕ) + (n + 2 : ℕ))
      (t + (n + 2 : ℕ) - 1 + (n + 2 : ℕ) - 1) n).inv) hd
  simpa only [adamsTowerInternalD, Category.assoc, Iso.inv_hom_id_assoc,
    Limits.comp_zero, Limits.zero_comp] using hh

end
end KIP126.Classical.Adams
