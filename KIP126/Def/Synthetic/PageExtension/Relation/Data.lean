module

public import KIP126.Def.SpectralSequence.Crossing.Predicates
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace KIP126.Synthetic.PageExtension
open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence
universe v
noncomputable section

/-- An element as a map from the free rank-one module in the same universe. -/
def elementMap {A : ModuleCat.{v} ℤ} (x : A) :
    ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ A :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ A x).comp ULift.moduleEquiv.toLinearMap)

/-- The complete target coset of the actual ESS boundary tower. Its B-level
already contains every shorter extension image. -/
def targetCoset (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (n : ℤ) (p : ℤ × ℤ) {T : ModuleCat.{v} ℤ}
    (y : T ⟶ (E.ssData (p + E.diffDeg n)).V) : Set (T ⟶ (E.ssData (p + E.diffDeg n)).V) :=
  { z | Subobject.Factors ((E.ssData (p + E.diffDeg n)).B
      (↑(n - E.r₀).toNat : WithTop ℕ)) (y - z) }

end
end KIP126.Synthetic.PageExtension
