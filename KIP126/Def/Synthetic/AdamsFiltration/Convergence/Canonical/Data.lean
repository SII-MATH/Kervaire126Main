module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Data
public import KIP126.Def.Synthetic.AdamsSequence.TowerComparison.Data
public import KIP126.Def.ClassicalAdams.Detection.Convergence.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

/-- The specified bigraded suspension identifies the shifted domain sphere
with the ordinary m-sphere. The map is fixed by biShift_comp and biShift_compat. -/
def weightSourceIso (m w : ℤ) :
    (SyntheticCategory.biShift (0,-w)).obj (Smn m w (Syn := Syn)) ≅
      KIP126.StableHomotopy.Sphere (C := Syn) m :=
  (SyntheticCategory.biShift_comp (m,w) (0,-w)).app S_0_0 ≪≫
    eqToIso (congrArg (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj (S_0_0 : Syn))
      (by ext <;> simp)) ≪≫
    (SyntheticCategory.biShift_compat (Syn := Syn) m).app S_0_0

/-- Actual desuspension in weight, on maps rather than a selected bijection. -/
def weightHomotopyMap (m w : ℤ) (X : Syn) (a : BiHom m w X) :
    HomotopyGroup m ((SyntheticCategory.biShift (0,-w)).obj X) :=
  (weightSourceIso m w).inv ≫ (SyntheticCategory.biShift (0,-w)).map a

abbrev FamilyInfiniteRepresentative (F : SyntheticAdamsFamily Syn) (X : Syn)
    (i : Tridegree) :=
  (Subobject.underlying.obj (((F.obj X).sequence.ssData i).Z ⊤) : ModuleCat ℤ)

/-- Read a family representative in the SAME actual weight tower selected
by P. Both its E₂ and E∞ projections therefore use one common representative. -/
def familyInfiniteRepresentativeE1 {F : SyntheticAdamsFamily Syn}
    (P : TowerPresentation unit F) (X : Syn) (i : Tridegree)
    (z : FamilyInfiniteRepresentative F X i) :
    KIP126.Classical.Adams.adamsE1 unit
      ((SyntheticCategory.biShift (0,-i.2.2)).obj X) i.1 i.2.1 :=
  KIP126.Classical.Adams.TowerDetection.infiniteRepresentativeE1 unit
    ((SyntheticCategory.biShift (0,-i.2.2)).obj X) (i.1,i.2.1)
    ((P.forward X i.2.2).cycleMap (i.1,i.2.1) ⊤ z)



end
end KIP126.Synthetic.SpectralSequence
