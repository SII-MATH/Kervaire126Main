module

public import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs

@[expose] public section

/-! The positive Adams-filtration decomposition follows from the constructed
tower and its homology-zero successor maps. No literature input is required
for this direction. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

theorem adamsTowerChain_composite {H : C} (unit : 𝟙_ C ⟶ H) (Y : C) (k : ℕ) :
    (adamsTowerChain unit Y k).composite =
      adamsTowerMap unit Y 0 k (Nat.zero_le k) := by
  induction k with
  | zero => simp [adamsTowerChain, FiniteMorphismChain.composite, adamsTower]
  | succ k ih =>
    change adamsTowerStep unit Y k ≫ (adamsTowerChain unit Y k).composite = _
    rw [ih, adamsTowerMap_succ unit Y 0 k (Nat.zero_le k)]

variable (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [(tensorLeft H.HF2).PreservesZeroMorphisms]

include R in
theorem adamsTowerChain_all_homologyZero (Y : C) (k : ℕ) :
    (adamsTowerChain H.unit Y k).All (IsZeroOnMod2Homology H) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    exact ⟨mod2_adamsTowerStep_homology_eq_zero H R Y k, ih⟩

include R in
/-- Absorb the original tower lift into the first successor map. The result
has exactly `k` homology-zero factors, with no additional arbitrary factor. -/
theorem AdamsFiltrationAtLeast.hasMod2ZeroFactorization {X Y : C} (f : X ⟶ Y)
    (k : ℕ) (hk : 0 < k) (hf : AdamsFiltrationAtLeast H f k) :
    HasMod2ZeroFactorization H f k := by
  obtain ⟨lift, hlift⟩ := hf
  cases k with
  | zero => omega
  | succ k =>
    refine ⟨.cons (lift ≫ adamsTowerStep H.unit Y k) (adamsTowerChain H.unit Y k),
      ?_, ?_⟩
    · change (lift ≫ adamsTowerStep H.unit Y k) ≫
        (adamsTowerChain H.unit Y k).composite = f
      rw [adamsTowerChain_composite, Category.assoc,
        ← adamsTowerMap_succ H.unit Y 0 k (Nat.zero_le k), hlift]
    · refine ⟨?_, adamsTowerChain_all_homologyZero H R Y k⟩
      intro n
      ext x
      change x ≫ (H.HF2 ◁ (lift ≫ adamsTowerStep H.unit Y k)) = 0
      rw [whiskerLeft_comp, mod2_adamsTowerStep_eq_zero H R,
        Limits.comp_zero, Limits.comp_zero]

end KIP126.Classical.Adams
