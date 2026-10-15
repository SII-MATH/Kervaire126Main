module

public import KIP126.Def.Synthetic.EInfty.Shift.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn}

/-- Naturality of the selected E∞ weight comparison with the same F on both sides. -/
def EInftyWeightShift.Natural (S : EInftyWeightShift F) : Prop :=
  ∀ {A B : Syn} (g : A ⟶ B) (k : ℤ) (p : ℤ × ℤ) (w : ℤ)
    (x : ((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
      (p.1, p.2, w + k)).eInfty),
    S.iso B k p w (((F.functor.map ((SyntheticCategory.biShift (0, k)).map g)).eInftyMap
      (p.1, p.2, w + k)).hom x) =
    ((F.functor.map g).eInftyMap (p.1, p.2, w)).hom (S.iso A k p w x)

end KIP126.Synthetic.SpectralSequence
