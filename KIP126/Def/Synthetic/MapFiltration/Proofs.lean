module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Data
public import KIP126.Def.Synthetic.ExtensionSS.Data
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
set_option backward.isDefEq.respectTransparency false
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

/-- Tower naturality gives filtration preservation. This general
proof concerns actual maps and ranges; it is not a new operation or a local
Adams differential input. It requires no boundedness or convergence. -/
theorem homotopyMap_filtration_compatible {X Y : Syn} (g : X ⟶ Y) (s : ℤ) (p : ℤ × ℤ) :
    ∃ φ : Subobject.underlying.obj ((towerFiltration unit X).F s p) ⟶
        Subobject.underlying.obj ((towerFiltration unit Y).F s p),
      φ ≫ ((towerFiltration unit Y).F s p).arrow =
        ((towerFiltration unit X).F s p).arrow ≫ syntheticHomotopyMap g p := by
  let FX := towerFiltrationSubmodule unit X s p
  let FY := towerFiltrationSubmodule unit Y s p
  have hmap (a : FX) : ((syntheticHomotopyMap g p).hom.comp FX.subtype) a ∈ FY := by
    obtain ⟨z, hz⟩ := a.property
    refine ⟨z ≫ adamsTowerInduced unit g s.toNat, ?_⟩
    change (z ≫ adamsTowerInduced unit g s.toNat) ≫
      adamsTowerMap unit Y 0 s.toNat (Nat.zero_le _) = a.val ≫ g
    rw [Category.assoc, adamsTowerInduced_map, ← Category.assoc]
    change (towerHomotopyMap unit X s.toNat p z) ≫ g = _
    rw [hz]
  letI : Mono (ModuleCat.ofHom FX.subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  letI : Mono (ModuleCat.ofHom FY.subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  let φ := LinearMap.codRestrict FY ((syntheticHomotopyMap g p).hom.comp FX.subtype) hmap
  refine ⟨(Subobject.underlyingIso (ModuleCat.ofHom FX.subtype)).hom ≫
    ModuleCat.ofHom φ ≫ (Subobject.underlyingIso (ModuleCat.ofHom FY.subtype)).inv, ?_⟩
  change _ ≫ (Subobject.mk (ModuleCat.ofHom FY.subtype)).arrow =
    (Subobject.mk (ModuleCat.ofHom FX.subtype)).arrow ≫ _
  simp only [Category.assoc, Subobject.underlyingIso_arrow]
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (ModuleCat.ofHom FX.subtype), Category.assoc]
  congr 1
end KIP126.Synthetic.SpectralSequence
