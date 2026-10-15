module

public import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs

@[expose] public section

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

/-- Concrete representatives for the categorical subobject of a submodule. -/
noncomputable def submoduleUnderlyingIso (Z : Submodule R M) :
    Subobject.underlying.obj ((ModuleCat.subobjectModule M).symm Z) ≅
      ModuleCat.of R Z :=
  Subobject.underlyingIso (ModuleCat.ofHom Z.subtype)

/-- The internal categorical quotient of two submodules agrees with the
ordinary module quotient, with explicitly chosen representative maps. -/
noncomputable def submoduleCokernelIso (B Z : Submodule R M) (h : B ≤ Z) :
    cokernel (Subobject.ofLE
      ((ModuleCat.subobjectModule M).symm B)
      ((ModuleCat.subobjectModule M).symm Z)
      ((ModuleCat.subobjectModule _).symm.monotone h)) ≅
        ModuleCat.of R (Z ⧸ B.comap Z.subtype) :=
  cokernel.mapIso _ (ModuleCat.ofHom (Submodule.inclusion h))
    (Subobject.underlyingIso (ModuleCat.ofHom B.subtype))
    (Subobject.underlyingIso (ModuleCat.ofHom Z.subtype))
    (submodule_ofLE_underlyingIso B Z h) ≪≫
  ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (Submodule.inclusion h)) ≪≫
  (Submodule.quotEquivOfEq _ _ (by
    exact Submodule.range_inclusion B Z h)).toModuleIso

end KIP126.SpectralSequence
