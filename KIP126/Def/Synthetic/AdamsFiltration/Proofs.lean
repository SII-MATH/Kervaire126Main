module

public import KIP126.Def.Synthetic.AdamsFiltration.Data

@[expose] public section
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Classical.Adams
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H) (X : Syn)

theorem towerFiltrationSubmodule_antitone (p : ℤ × ℤ) :
    Antitone (fun s => towerFiltrationSubmodule unit X s p) := by
  intro s t hst x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y ≫ adamsTowerMap unit X s.toNat t.toNat (by omega), ?_⟩
  change (y ≫ adamsTowerMap unit X s.toNat t.toNat _) ≫
    adamsTowerMap unit X 0 s.toNat _ = x
  rw [Category.assoc, adamsTowerMap_comp]
  exact hy
end KIP126.Synthetic.SpectralSequence
