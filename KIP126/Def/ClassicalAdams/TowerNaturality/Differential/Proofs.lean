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

theorem adamsTowerHomInduced_cast {n n' : ℤ} (e : n = n') (s : ℤ)
    (a : HomotopyGroup n (adamsTowerAt unit X s)) :
    adamsTowerHomInduced unit f n' s
      (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X s)) e) a) =
    Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit Y s)) e)
      (adamsTowerHomInduced unit f n s a) := by
  subst n'
  rfl

theorem adamsPageInduced_JToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : HomotopyGroup (t-s) (adamsTowerAt unit X s)) :
    adamsPageInduced unit f r hr s t (adamsJToPage unit X r hr s t a) =
      adamsJToPage unit Y r hr s t (adamsTowerHomInduced unit f (t-s) s a) := by
  apply congrArg (adamsCycleBoundaries unit Y r hr s t).mkQ
  exact Subtype.ext (adamsJ_naturality unit f s t a)

theorem adamsPageInduced_differential (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : adamsPage unit X r hr s t) :
    adamsPageInduced unit f r hr (s+r) (t+r-1) (adamsDifferential unit X r hr s t a) =
      adamsDifferential unit Y r hr s t (adamsPageInduced unit f r hr s t a) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    change adamsPageInduced unit f r hr (s+r) (t+r-1)
      (adamsDifferentialValue unit X r hr s t a) =
        adamsDifferentialValue unit Y r hr s t (adamsCycleInduced unit f r hr s t a)
    rw [adamsDifferentialValue_eq_of_lift unit Y r hr s t _
      (adamsTowerHomInduced unit f (t-s-1) (s+r) (adamsCycleLift unit X r hr s t a)) (by
        rw [adamsI_naturality, adamsCycleLift_spec]
        exact (adamsK_naturality unit f s t a).symm)]
    change adamsPageInduced unit f r hr (s+r) (t+r-1)
      (adamsJToPage unit X r hr (s+r) (t+r-1) _) = _
    rw [adamsPageInduced_JToPage]
    exact congrArg (adamsJToPage unit Y r hr (s+r) (t+r-1))
      (adamsTowerHomInduced_cast unit f (by omega) (s+r) (adamsCycleLift unit X r hr s t a))

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
