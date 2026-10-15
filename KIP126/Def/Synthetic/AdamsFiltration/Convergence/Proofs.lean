module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Canonical.Data
public import KIP126.Def.Synthetic.AdamsSequence.TowerComparison.Data
public import KIP126.Def.ClassicalAdams.Detection.Convergence.Proofs
public import KIP126.Def.SpectralSequence.Basic.Proofs

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

/-- Every genuine tower lift has a common family representative, transported
through P.inverse. This is KJ=0, allowing a ZERO class, not convergence. -/
theorem exists_weightLiftRepresentative {F : SyntheticAdamsFamily Syn}
    (P : TowerPresentation unit F) (X : Syn) (i : Tridegree)
    (a : HomotopyGroup (i.2.1-i.1)
      (KIP126.Classical.Adams.adamsTowerAt unit
        ((SyntheticCategory.biShift (0,-i.2.2)).obj X) i.1)) :
    ∃ z : FamilyInfiniteRepresentative F X i,
      familyInfiniteRepresentativeE1 unit P X i z =
        KIP126.Classical.Adams.adamsJ unit
          ((SyntheticCategory.biShift (0,-i.2.2)).obj X) i.1 i.2.1 a := by
  obtain ⟨z, hz⟩ := KIP126.Classical.Adams.TowerDetection.exists_liftRepresentative unit
    ((SyntheticCategory.biShift (0, -i.2.2)).obj X) (i.1, i.2.1) a
  refine ⟨(P.inverse X i.2.2).cycleMap (i.1, i.2.1) ⊤ z, ?_⟩
  have h : (P.inverse X i.2.2).cycleMap (i.1, i.2.1) ⊤ ≫
      (P.forward X i.2.2).cycleMap (i.1, i.2.1) ⊤ = 𝟙 _ := by
    apply (cancel_mono (((weightTower unit X i.2.2).ssData (i.1, i.2.1)).Z ⊤).arrow).1
    simp only [Category.assoc, SSDataMorphism.cycleMap_arrow,
      SSDataMorphism.cycleMap_arrow_assoc, Category.id_comp]
    rw [P.right_inv, Category.comp_id]
  have he := congrArg (fun f => f.hom z) h
  change (P.forward X i.2.2).cycleMap (i.1, i.2.1) ⊤
    ((P.inverse X i.2.2).cycleMap (i.1, i.2.1) ⊤ z) = z at he
  unfold familyInfiniteRepresentativeE1
  rw [he]
  exact hz

end
end KIP126.Synthetic.SpectralSequence
