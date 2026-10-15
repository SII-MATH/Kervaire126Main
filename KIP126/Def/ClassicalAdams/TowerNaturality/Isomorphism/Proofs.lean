module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data

@[expose] public section

/-! Isomorphisms of actual Adams towers. The triangle argument is the same
one used in KIPBase/Synthetic/GeometricAdamsCofiber. It does not assume
identity or composition laws for the chosen cofiber-map operation. -/
namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

private theorem cofiberMap_isIso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) [IsIso a] [IsIso b] :
    IsIso (HasFunctorialCofiber.cofibMap f g a b h) := by
  let φ : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := a
      hom₂ := b
      hom₃ := HasFunctorialCofiber.cofibMap f g a b h
      comm₁ := h.symm
      comm₂ := (HasFunctorialCofiber.cofibMap_ι f g a b h).symm
      comm₃ := (HasFunctorialCofiber.cofibMap_δ f g a b h).symm }
  exact isIso₃_of_isIso₁₂ φ (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g) inferInstance inferInstance

/-- Each specified stage map of an object isomorphism is an isomorphism. -/
theorem adamsTowerInduced_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (s : ℕ) :
    IsIso (adamsTowerInduced unit f s) := by
  induction s with
  | zero => exact inferInstanceAs (IsIso f)
  | succ s ih =>
    letI := ih
    haveI := cofiberMap_isIso (adamsUnit unit (adamsTower unit X s))
      (adamsUnit unit (adamsTower unit Y s)) (adamsTowerInduced unit f s)
      (H ◁ adamsTowerInduced unit f s) (adamsUnit_naturality unit _)
    change IsIso ((shiftFunctor C (-1 : ℤ)).map _)
    infer_instance

/-- The layer map is an isomorphism by the distinguished-triangle five lemma. -/
theorem adamsLayerInduced_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (s : ℤ) :
    IsIso (adamsLayerInduced unit f s) := by
  letI := adamsTowerInduced_isIso unit f (s + 1).toNat
  letI := adamsTowerInduced_isIso unit f s.toNat
  exact cofiberMap_isIso _ _ _ _ _

/-- Postcomposition with an actual tower isomorphism is bijective. -/
theorem adamsTowerHomInduced_bijective {X Y : C} (f : X ⟶ Y) [IsIso f] (n s : ℤ) :
    Function.Bijective (adamsTowerHomInduced unit f n s) := by
  letI := adamsTowerInduced_isIso unit f s.toNat
  constructor
  · intro a b hab
    exact (cancel_mono (adamsTowerInduced unit f s.toNat)).1 hab
  · intro a
    refine ⟨a ≫ inv (adamsTowerInduced unit f s.toNat), ?_⟩
    change (a ≫ _) ≫ _ = a
    simp

/-- Postcomposition with the actual layer isomorphism is bijective. -/
theorem adamsE1Induced_bijective {X Y : C} (f : X ⟶ Y) [IsIso f] (s t : ℤ) :
    Function.Bijective (adamsE1Induced unit f s t) := by
  letI := adamsLayerInduced_isIso unit f s
  constructor
  · intro a b hab
    exact (cancel_mono (adamsLayerInduced unit f s)).1 hab
  · intro a
    refine ⟨a ≫ inv (adamsLayerInduced unit f s), ?_⟩
    change (a ≫ _) ≫ _ = a
    simp

/-- Cycle preservation is reflected by an object isomorphism. -/
theorem adamsE1Induced_mem_cycles_iff {X Y : C} (f : X ⟶ Y) [IsIso f]
    (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) (a : adamsE1 unit X s t) :
    adamsE1Induced unit f s t a ∈ adamsCycles unit Y r hr s t ↔
      a ∈ adamsCycles unit X r hr s t := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := (adamsTowerHomInduced_bijective unit f (t - s - 1) (s + r)).2 b
    refine ⟨c, (adamsTowerHomInduced_bijective unit f (t - s - 1) (s + 1)).1 ?_⟩
    rw [← adamsI_naturality, ← adamsK_naturality]
    exact hb
  · exact adamsE1Induced_mem_cycles unit f r hr s t

/-- Boundary preservation is reflected by an object isomorphism. -/
theorem adamsE1Induced_mem_boundaries_iff {X Y : C} (f : X ⟶ Y) [IsIso f]
    (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) (a : adamsE1 unit X s t) :
    adamsE1Induced unit f s t a ∈ adamsBoundaries unit Y r hr s t ↔
      a ∈ adamsBoundaries unit X r hr s t := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, rfl⟩ := (adamsTowerHomInduced_bijective unit f (t - s) s).2 b
    refine ⟨c, ?_, (adamsE1Induced_bijective unit f s t).1 ?_⟩
    · change adamsI unit X (t - s) (s - r + 1) s _ c = 0
      apply (adamsTowerHomInduced_bijective unit f (t - s) (s - r + 1)).1
      rw [← adamsI_naturality, map_zero]
      exact hb
    · rw [adamsJ_naturality]
      exact hba
  · exact adamsE1Induced_mem_boundaries unit f r hr s t
/-- Restrict the actual layer isomorphism to any finite cycle module. -/
theorem adamsCycleInduced_bijective {X Y : C} (f : X ⟶ Y) [IsIso f]
    (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Function.Bijective (adamsCycleInduced unit f r hr s t) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact (adamsE1Induced_bijective unit f s t).1 (congrArg Subtype.val hab)
  · intro b
    obtain ⟨a, ha⟩ := (adamsE1Induced_bijective unit f s t).2 b.val
    refine ⟨⟨a, (adamsE1Induced_mem_cycles_iff unit f r hr s t a).1 ?_⟩, ?_⟩
    · rw [ha]
      exact b.property
    · exact Subtype.ext ha

/-- The actual ambient isomorphism preserves and reflects all cycles,
including the intersection defining infinity. -/
theorem adamsCycleInduced_mem_cycleSubmodule_iff {X Y : C} (f : X ⟶ Y) [IsIso f]
    (s t : ℤ) (r : WithTop ℕ) (a : adamsCycleAmbient unit X s t) :
    adamsCycleInduced unit f 2 (Nat.le_succ 1) s t a ∈ adamsCycleSubmodule unit Y s t r ↔
      a ∈ adamsCycleSubmodule unit X s t r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp only [adamsCycleSubmodule, Submodule.mem_iInf]
    exact forall_congr' fun m => adamsE1Induced_mem_cycles_iff unit f (m + 2) (by omega) s t a.val
  · lift r to ℕ using hr
    exact adamsE1Induced_mem_cycles_iff unit f (r + 2) (by omega) s t a.val

/-- The actual ambient isomorphism preserves and reflects all boundaries,
including their supremum at infinity. -/
theorem adamsCycleInduced_mem_boundarySubmodule_iff {X Y : C} (f : X ⟶ Y) [IsIso f]
    (s t : ℤ) (r : WithTop ℕ) (a : adamsCycleAmbient unit X s t) :
    adamsCycleInduced unit f 2 (Nat.le_succ 1) s t a ∈ adamsBoundarySubmodule unit Y s t r ↔
      a ∈ adamsBoundarySubmodule unit X s t r := by
  let e := LinearEquiv.ofBijective (adamsCycleInduced unit f 2 (Nat.le_succ 1) s t)
    (adamsCycleInduced_bijective unit f 2 (Nat.le_succ 1) s t)
  have hf (m : ℕ) : (adamsFiniteBoundarySubmodule unit X s t m).map e.toLinearMap =
      adamsFiniteBoundarySubmodule unit Y s t m := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (adamsE1Induced_mem_boundaries_iff unit f (m + 2) (by omega) s t c.val).2 hc
    · intro hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      apply (adamsE1Induced_mem_boundaries_iff unit f (m + 2) (by omega) s t (e.symm b).val).1
      change e (e.symm b) ∈ adamsFiniteBoundarySubmodule unit Y s t m
      simpa only [e.apply_symm_apply] using hb
  rcases eq_or_ne r ⊤ with rfl | hr
  · have ht : (adamsBoundarySubmodule unit X s t ⊤).map e.toLinearMap =
        adamsBoundarySubmodule unit Y s t ⊤ := by
      simp only [adamsBoundarySubmodule, Submodule.map_iSup, hf]
    change e a ∈ adamsBoundarySubmodule unit Y s t ⊤ ↔ _
    rw [← ht]
    simp only [Submodule.mem_map_equiv, e.symm_apply_apply]
  · lift r to ℕ using hr
    exact adamsE1Induced_mem_boundaries_iff unit f (r + 2) (by omega) s t a.val

end KIP126.Classical.Adams
