module

public import KIP126.Def.ClassicalAdams.Detection.Convergence.Canonical.Data

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
/-- Canonical convergence is fixed on the actual maps from tower stages.
The two displayed representatives belong to the SAME tower lift: E₁ uses
the real cofiber inclusion J, and the filtration class uses projection to
stage zero.  Thus an arbitrary automorphism of E∞ cannot be substituted.
The quantification includes zero classes and all integer filtrations. -/
def CanonicalIdentification (X : C)
    (e : ∀ p : ℤ × ℤ,
      ((adamsTowerInternalSpectralSequence unit X).ssData p).eInfty ≅
        (filtration unit X).associatedGraded p.1 (p.2-p.1)) : Prop :=
  ∀ (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (adamsTowerAt unit X p.1))
    (z : InfiniteRepresentative unit X p),
    infiniteRepresentativeE1 unit X p z = adamsJ unit X p.1 p.2 a →
    ∀ b : (Subobject.underlying.obj
      ((filtration unit X).F p.1 (p.2-p.1)) : ModuleCat ℤ),
    ((filtration unit X).F p.1 (p.2-p.1)).arrow b =
      inducedMap (adamsTowerMap unit X 0 p.1.toNat (Nat.zero_le _)) (p.2-p.1) a →
    (e p).hom (((adamsTowerInternalSpectralSequence unit X).ssData p).pageπ ⊤ z) =
      (filtration unit X).toAssociatedGraded p.1 (p.2-p.1) b

end
end KIP126.Classical.Adams.TowerDetection
