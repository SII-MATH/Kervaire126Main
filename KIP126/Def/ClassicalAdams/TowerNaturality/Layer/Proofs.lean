module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Layer.Data
public import KIP126.Def.StableHomotopy.Context.Connecting.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

theorem adamsJ_naturality (s t : ℤ)
    (a : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    adamsE1Induced unit f s t (adamsJ unit X s t a) =
      adamsJ unit Y s t (adamsTowerHomInduced unit f (t - s) s a) := by
  change (a ≫ _) ≫ _ = (a ≫ _) ≫ _
  simp only [Category.assoc, adamsLayerInduced,
    ← HasFunctorialCofiber.cofibMap_ι]

theorem adamsK_naturality (s t : ℤ) (a : adamsE1 unit X s t) :
    adamsK unit Y s t (adamsE1Induced unit f s t a) =
      adamsTowerHomInduced unit f (t - s - 1) (s + 1) (adamsK unit X s t a) :=
  connectingHomomorphism_naturality
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit Y s (s + 1) (by omega)))
    (adamsTowerInduced unit f (s + 1).toNat) (adamsLayerInduced unit f s)
    (HasFunctorialCofiber.cofibMap_δ _ _ _ _ _) (t - s) a

theorem adamsI_naturality (n s t : ℤ) (h : s ≤ t)
    (a : HomotopyGroup n (adamsTowerAt unit X t)) :
    adamsI unit Y n s t h (adamsTowerHomInduced unit f n t a) =
      adamsTowerHomInduced unit f n s (adamsI unit X n s t h a) := by
  change (a ≫ _) ≫ _ = (a ≫ _) ≫ _
  simp only [Category.assoc, adamsTowerInduced_mapAt]

theorem adamsE1Induced_mem_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    {a : adamsE1 unit X s t} (ha : a ∈ adamsCycles unit X r hr s t) :
    adamsE1Induced unit f s t a ∈ adamsCycles unit Y r hr s t := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨adamsTowerHomInduced unit f (t - s - 1) (s + r) b, ?_⟩
  rw [adamsI_naturality, hb, adamsK_naturality]

theorem adamsE1Induced_mem_boundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    {a : adamsE1 unit X s t} (ha : a ∈ adamsBoundaries unit X r hr s t) :
    adamsE1Induced unit f s t a ∈ adamsBoundaries unit Y r hr s t := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨adamsTowerHomInduced unit f (t - s) s b, ?_, ?_⟩
  · change adamsI unit Y (t - s) (s - r + 1) s _ _ = 0
    rw [adamsI_naturality, show adamsI unit X (t - s) (s - r + 1) s _ b = 0 from hb,
      map_zero]
  · exact (adamsJ_naturality unit f s t b).symm

end KIP126.Classical.Adams
