module

public import KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The chosen cofiber map associated to a factorization, with identity on
the common target. No identity or composition law for cofiber choices is used. -/
noncomputable def cofiberFactorizationMap {A B D : C}
    (f : A ⟶ D) (g : B ⟶ D) (a : A ⟶ B) (h : a ≫ g = f) :
    HasFunctorialCofiber.cofib f ⟶ HasFunctorialCofiber.cofib g :=
  HasFunctorialCofiber.cofibMap f g a (𝟙 D) (h.trans (Category.comp_id f).symm)

end KIP126.StableHomotopy
