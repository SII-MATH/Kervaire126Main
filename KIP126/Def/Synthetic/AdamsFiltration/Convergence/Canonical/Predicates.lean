module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Canonical.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

/-- Canonical detection relative to the ONE supplied tower presentation.
The first condition binds the weight-shifted tower filtration to the actual
bigraded tower filtration. The second fixes the E∞ identification on actual
tower lifts and their cofiber images. Requiring this only for the model's P
avoids the false assertion that every re-labelled tower presentation has the
same detection map. No specified differential or survival is imposed. -/
def TowerConvergence.Canonical {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (P : TowerPresentation unit F) : Prop :=
  (∀ (s m w : ℤ) (a : BiHom m w X),
    a ∈ towerFiltrationSubmodule unit X s (m,w) ↔
      weightHomotopyMap m w X a ∈
        KIP126.Classical.Adams.TowerDetection.filtrationSubmodule unit
          ((SyntheticCategory.biShift (0,-w)).obj X) s m) ∧
  ∀ (i : Tridegree)
    (a : HomotopyGroup (i.2.1-i.1)
      (KIP126.Classical.Adams.adamsTowerAt unit
        ((SyntheticCategory.biShift (0,-i.2.2)).obj X) i.1))
    (z : FamilyInfiniteRepresentative F X i),
    familyInfiniteRepresentativeE1 unit P X i z =
      KIP126.Classical.Adams.adamsJ unit
        ((SyntheticCategory.biShift (0,-i.2.2)).obj X) i.1 i.2.1 a →
    ∀ b : (Subobject.underlying.obj
      ((towerFiltration unit X).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ),
    weightHomotopyMap (i.2.1-i.1) i.2.2 X
      (((towerFiltration unit X).F i.1 (i.2.1-i.1,i.2.2)).arrow b) =
      inducedMap (KIP126.Classical.Adams.adamsTowerMap unit
        ((SyntheticCategory.biShift (0,-i.2.2)).obj X) 0 i.1.toNat (Nat.zero_le _))
        (i.2.1-i.1) a →
    (c.identification i).hom (((F.obj X).sequence.ssData i).pageπ ⊤ z) =
      (towerFiltration unit X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b


end
end KIP126.Synthetic.SpectralSequence
