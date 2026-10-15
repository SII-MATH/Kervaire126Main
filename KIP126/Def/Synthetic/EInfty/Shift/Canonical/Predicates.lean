module

public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

/-- The E∞ isomorphism is the quotient of the prescribed actual cycle map.
Every permanent-cycle representative has a displayed image, so the
condition cannot hold vacuously through a missing target representative.
This anchors every object and weight to the tower construction; it does not
assert naturality or choose a second family. -/
def CanonicalWeightShift (P : TowerPresentation unit F)
    (S : EInftyWeightShift F) : Prop :=
  ∀ (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ),
    let source := (F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
      (p.1, p.2, w + k)
    let target := (F.obj A).sequence.ssData (p.1, p.2, w)
    ∀ a : (Subobject.underlying.obj (source.Z ⊤) : ModuleCat.{v} ℤ),
      ∃ b : (Subobject.underlying.obj (target.Z ⊤) : ModuleCat.{v} ℤ),
        (target.Z ⊤).arrow b =
          canonicalWeightShiftAmbient unit P A k p w ((source.Z ⊤).arrow a) ∧
        S.iso A k p w (source.pageπ ⊤ a) = target.pageπ ⊤ b

end KIP126.Synthetic.SpectralSequence
