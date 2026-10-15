module

public import KIP126.Def.Synthetic.AdamsSequence.TowerComparison.Data
public import KIP126.Def.Synthetic.EInfty.Shift.Data

@[expose] public section

/-! Actual weight reindexing maps below the E∞ quotient. No literature
statement, property witness or freely chosen E∞ isomorphism is used. -/
namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.SpectralSequence
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} (unit : S_0_0 ⟶ H)
  {F : SyntheticAdamsFamily Syn}

/-- Undo the object weight shift through the specified suspension-composition
isomorphism. This is the actual object underlying the two weight towers. -/
def weightShiftObjectIso (A : Syn) (k w : ℤ) :
    (SyntheticCategory.biShift (0, -(w + k))).obj
      ((SyntheticCategory.biShift (0, k)).obj A) ≅
    (SyntheticCategory.biShift (0, -w)).obj A :=
  (SyntheticCategory.biShift_comp (0, k) (0, -(w + k))).app A ≪≫
    eqToIso (congrArg (fun b => (SyntheticCategory.biShift b).obj A)
      (show (0, k) + (0, -(w + k)) = (0, -w) by
        apply Prod.ext <;> simp))

/-- The raw cycle map: move to the actual weight tower, apply the actual
Adams map of the object isomorphism, then return through the same tower
presentation. Preservation and descent are explicit later proof obligations. -/
def canonicalWeightShiftAmbient (P : TowerPresentation unit F)
    (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) :
    ((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
      (p.1, p.2, w + k)).V ⟶
    ((F.obj A).sequence.ssData (p.1, p.2, w)).V :=
  (P.forward ((SyntheticCategory.biShift (0, k)).obj A) (w + k)).φ p ≫
    ModuleCat.ofHom
      (adamsCycleInduced unit (weightShiftObjectIso A k w).hom 2 (by decide) p.1 p.2) ≫
    (P.inverse A w).φ p

end
end KIP126.Synthetic.SpectralSequence
