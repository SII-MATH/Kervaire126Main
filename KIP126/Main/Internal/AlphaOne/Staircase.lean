module
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Def.Computation.Table.Archive
import all KIP126.Main.Internal.AlphaOne.PageVanishing

/-! The two finite staircase records and their permanent-cycle deduction,
AlphaOne/Staircase.lean and Computation/Route/Bounds.lean:88–104 at
bbac1fc05843 (MIT). The records assert reaches 1000; the infinite tail is
proved here from the sphere vanishing line. -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.StableHomotopy KIP126.AdamsSynthetic.Standard
open KIP126.Computation.Table
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem permanent_cycle_of_reaches1000 (s t : ℕ)
    (hn : 1 < (t:ℤ)-s) (hn' : (t:ℤ)-s≤127)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : ReachesPage model.classical.sphere 1000 (s,t) x) :
    IsPermanentCycle model.classical.sphere (s,t) x := by
  apply isPermanentCycle_of_reachesPage model.classical.sphere 1000
    (by rw [model.classical.firstPage]; omega) (s,t) x hx
  intro r hr
  have hp : Subsingleton (model.classical.sphere.Page r ((s:ℤ)+r,(t:ℤ)+r-1)) :=
    page_subsingleton_of_le _ 2 r _ (le_of_eq (model.classical.firstPage _)) (by omega)
      (KIP126.Literature.Standard.sphereVanishing _ _ (by omega) (by omega))
  haveI : Subsingleton (model.classical.sphere.Page r
      (((s:ℤ),(t:ℤ))+model.classical.sphere.diffDeg r)) := by
    rw [model.classical.differentialDegree]
    simpa only [Prod.mk_add_mk,add_sub_assoc] using hp
  ext y
  exact Subsingleton.elim _ _

private theorem full_staircase_high_cycles :
    IsPermanentCycle model.classical.sphere (14,138) (basis .sphere 14 138 2) ∧
    IsPermanentCycle model.classical.sphere (15,139)
      (basis .sphere 15 139 1 + basis .sphere 15 139 3) := by
  have h14 := staircase_result
    ⟨.sphere,.reaches,1000,14,138,[2],14,138,[],"S0_AdamsSS_staircase:23:61",3005⟩
    (by simp [staircaseClaims])
  obtain ⟨x14,hx14,h14⟩ := h14
  have hx14' : x14=basis .sphere 14 138 2 := by
    simpa only [decode, show Raw.coordinatesValid Raw.degrees .sphere 14 138 [2]=true from rfl,
      ↓reduceIte,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] using hx14.symm
  subst x14
  have h15 := staircase_result
    ⟨.sphere,.reaches,1000,15,139,[1,3],15,139,[],"S0_AdamsSS_staircase:24:4",3076⟩
    (by simp [staircaseClaims])
  obtain ⟨x15,hx15,h15⟩ := h15
  have hx15' : x15=basis .sphere 15 139 1 + basis .sphere 15 139 3 := by
    simpa only [decode, show Raw.coordinatesValid Raw.degrees .sphere 15 139 [1,3]=true from rfl,
      ↓reduceIte,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] using hx15.symm
  subst x15
  exact ⟨permanent_cycle_of_reaches1000 14 138 (by decide) (by decide) _ h14,
    permanent_cycle_of_reaches1000 15 139 (by decide) (by decide) _ h15⟩
end
end KIP126.Main.Internal.AlphaOne
end
