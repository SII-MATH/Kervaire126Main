module

public import KIP126.Def.Topology.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory CategoryTheory.Limits

universe u

/-- A genuine simultaneous attachment of homotopy-extension maps has
homotopy extension; the cell dimensions need not be uniform. -/
theorem hasHomotopyExtension_of_attachCells
    {α : Type*} {A B : α → TopCat.{u}} {g : ∀ i, A i ⟶ B i}
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u} g f)
    (hg : ∀ i, HasHomotopyExtension (g i)) : HasHomotopyExtension f := by
  apply (hasHomotopyExtension_iff_lifting f).mpr
  intro Z
  let W := MorphismProperty.ofHoms g
  have hp : W.rlp (pathEvaluationZero Z) := by
    intro S T i hi
    cases hi with
    | mk a => exact (hasHomotopyExtension_iff_lifting _).mp (hg a) Z
  have h : W.rlp.llp f := by
    simpa only [MorphismProperty.rlp_coproducts] using
      (MorphismProperty.coproducts.{u} W).pushouts_le_llp_rlp f c.pushouts_coproducts
  exact h (pathEvaluationZero Z) hp

end KIP126.Topology.HomotopyExtension
