module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Proofs
public import KIP126.Def.SpectralSequence.Basic.Proofs

@[expose] public section

/-! Naturality on the existing quotient pages. The proof transports a chosen
lift and uses independence of that lift, as in the representative argument of
KIPBase/Synthetic/GeometricAdamsPageShift. No second tower or page is defined. -/
namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

theorem adamsCycleInduced_mem_cycleSubmodule (s t : ℤ) (r : WithTop ℕ)
    {a : adamsCycleAmbient unit X s t} (ha : a ∈ adamsCycleSubmodule unit X s t r) :
    adamsCycleInduced unit f 2 (Nat.le_succ 1) s t a ∈ adamsCycleSubmodule unit Y s t r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp only [adamsCycleSubmodule, Submodule.mem_iInf] at ha ⊢
    intro m
    exact adamsE1Induced_mem_cycles unit f (m+2) (by omega) s t (ha m)
  · lift r to ℕ using hr
    exact adamsE1Induced_mem_cycles unit f (r+2) (by omega) s t ha

theorem adamsCycleInduced_mem_boundarySubmodule (s t : ℤ) (r : WithTop ℕ)
    {a : adamsCycleAmbient unit X s t} (ha : a ∈ adamsBoundarySubmodule unit X s t r) :
    adamsCycleInduced unit f 2 (Nat.le_succ 1) s t a ∈ adamsBoundarySubmodule unit Y s t r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · have hmap : (adamsBoundarySubmodule unit X s t ⊤).map
        (adamsCycleInduced unit f 2 (Nat.le_succ 1) s t) ≤ adamsBoundarySubmodule unit Y s t ⊤ := by
      simp only [adamsBoundarySubmodule, Submodule.map_iSup]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun n => adamsFiniteBoundarySubmodule unit Y s t n) m)
      rintro _ ⟨b, hb, rfl⟩
      exact adamsE1Induced_mem_boundaries unit f (m+2) (by omega) s t hb
    exact hmap ⟨a, ha, rfl⟩
  · lift r to ℕ using hr
    exact adamsE1Induced_mem_boundaries unit f (r+2) (by omega) s t ha

end KIP126.Classical.Adams
