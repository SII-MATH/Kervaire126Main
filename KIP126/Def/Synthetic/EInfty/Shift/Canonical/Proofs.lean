module

public import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Predicates
public import KIP126.Def.Synthetic.EInfty.Shift.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Morphism.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs

@[expose] public section

/-! Internal construction obligations for weight reindexing. These are
properties of the actual tower maps, not statements supplied by BHS. -/



namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence
set_option backward.isDefEq.respectTransparency false
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

/-- Prove preservation of the cycle and boundary towers, descend the actual
weight-shift map and its inverse to E∞, and verify their inverse equations.
Full-category naturality is a separate external hypothesis in
`KIP126.Literature.Background.WeightShift`. -/
theorem canonicalWeightShift_exists (P : TowerPresentation unit F) :
    ∃ S : EInftyWeightShift F, CanonicalWeightShift P S := by
  classical
  have all (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ) :
      ∃ q : ((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
          (p.1, p.2, w + k)).eInfty ≅ ((F.obj A).sequence.ssData (p.1, p.2, w)).eInfty,
        ∀ a : (Subobject.underlying.obj (((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
          (p.1, p.2, w + k)).Z ⊤) : ModuleCat ℤ),
          ∃ b : (Subobject.underlying.obj (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤) : ModuleCat ℤ),
            (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤).arrow b =
              canonicalWeightShiftAmbient unit P A k p w
                ((((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData (p.1, p.2, w + k)).Z ⊤).arrow a) ∧
            q.hom ((((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
              (p.1, p.2, w + k)).pageπ ⊤ a)) =
              ((F.obj A).sequence.ssData (p.1, p.2, w)).pageπ ⊤ b := by
    let X := (SyntheticCategory.biShift (0, k)).obj A
    let U := (SyntheticCategory.biShift (0, -(w + k))).obj X
    let V := (SyntheticCategory.biShift (0, -w)).obj A
    let eF : ((F.obj X).sequence.ssData (p.1, p.2, w + k)).V ≅
        ((weightTower unit X (w + k)).ssData p).V :=
      { hom := (P.forward X (w + k)).φ p
        inv := (P.inverse X (w + k)).φ p
        hom_inv_id := P.left_inv X (w + k) p
        inv_hom_id := P.right_inv X (w + k) p }
    let eI : ((weightTower unit A w).ssData p).V ≅
        ((F.obj A).sequence.ssData (p.1, p.2, w)).V :=
      { hom := (P.inverse A w).φ p
        inv := (P.forward A w).φ p
        hom_inv_id := P.right_inv A w p
        inv_hom_id := P.left_inv A w p }
    let eT := LinearEquiv.ofBijective
      (KIP126.Classical.Adams.adamsCycleInduced unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
      (KIP126.Classical.Adams.adamsCycleInduced_bijective unit (weightShiftObjectIso A k w).hom 2 (Nat.le_succ 1) p.1 p.2)
    let e := (eF.toLinearEquiv.trans eT).trans eI.toLinearEquiv
    have htZ (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).Z ⊤) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).Z ⊤) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit V p.1 p.2 ⊤)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsCycleSubmodule unit U p.1 p.2 ⊤))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_cycleSubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 ⊤ x
    have htB (x : KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2) :
        eT x ∈ (ModuleCat.subobjectModule _) (((weightTower unit A w).ssData p).B ⊤) ↔
          x ∈ (ModuleCat.subobjectModule _) (((weightTower unit X (w + k)).ssData p).B ⊤) := by
      change eT x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit V p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit V p.1 p.2 ⊤)) ↔
        x ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (KIP126.Classical.Adams.adamsCycleAmbient unit U p.1 p.2)))
          ((ModuleCat.subobjectModule _).symm (KIP126.Classical.Adams.adamsBoundarySubmodule unit U p.1 p.2 ⊤))
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact KIP126.Classical.Adams.adamsCycleInduced_mem_boundarySubmodule_iff unit
        (weightShiftObjectIso A k w).hom p.1 p.2 ⊤ x
    have hZ x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_Z p ⊤) ((P.forward A w).preserves_Z p ⊤) (eT (eF.hom x))).trans
      ((htZ (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_Z p ⊤) ((P.inverse X (w + k)).preserves_Z p ⊤) x))
    have hB x := (subobject_mem_iff_of_inverse eI.toLinearEquiv _ _
      ((P.inverse A w).preserves_B p ⊤) ((P.forward A w).preserves_B p ⊤) (eT (eF.hom x))).trans
      ((htB (eF.hom x)).trans (subobject_mem_iff_of_inverse eF.toLinearEquiv _ _
        ((P.forward X (w + k)).preserves_B p ⊤) ((P.inverse X (w + k)).preserves_B p ⊤) x))
    obtain ⟨q, hq⟩ := subobject_quotient_iso_of_linearEquiv
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B ⊤)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).Z ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).Z ⊤)
      (((F.obj X).sequence.ssData (p.1, p.2, w + k)).B_le_Z ⊤)
      (((F.obj A).sequence.ssData (p.1, p.2, w)).B_le_Z ⊤) e hB hZ
    exact ⟨q, hq⟩
  refine ⟨{ iso := fun A k p w => (all A k p w).choose.toLinearEquiv }, ?_⟩
  intro A k p w
  dsimp only
  intro a
  exact (all A k p w).choose_spec a

end KIP126.Synthetic.SpectralSequence
