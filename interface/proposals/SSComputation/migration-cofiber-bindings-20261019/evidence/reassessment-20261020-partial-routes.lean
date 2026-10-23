module
import KIP126.AdamsCalculations.Standard
import KIP126.SpectralSequence.Computation.Morphism.Proofs
import KIP126.SpectralSequence.FinitePageCalculus.Proofs

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Computation.Standard
open KIP126.AdamsSynthetic.Standard
set_option backward.isDefEq.respectTransparency false

/-- Verified partial result: the exact bottom-cell image has a continuation;
this makes no nonzero claim and does not call cofiber_target_to_e6. -/
example : ReachesPage nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by
  let E := model.classical.sphere
  let A := E.ssData (14,139)
  obtain ⟨z,hz⟩ := t_permanent_cycle
  let k : WithTop ℕ := ↑(6-E.r₀).toNat
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  let z6 := (Subobject.ofLE (A.Z ⊤) (A.Z k) (A.Z_anti le_top)) z
  have hrep : RepresentsOnPage E 6 (14,139) T (A.pageπ k z6) := by
    refine ⟨by decide,z6,?_,rfl⟩
    change (Subobject.ofLE (A.Z k) (A.Z n) _ ≫ A.pageπ n) z6 = T
    dsimp only [z6]
    rw [← ModuleCat.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  let f := model.classical.map (HasFunctorialCofiber.cofibι model.auxiliary.nuMap)
  exact ⟨_, f.representsOnPage hrep⟩

/-- Verified finite window: the already public E5 survival excludes r=2,3,4. -/
example : NeverHitOnWindow model.classical.sphere 2 4 (11,136) Y := by
  refine ⟨by decide,by decide,?_⟩
  intro r hr hlast
  rintro ⟨q,hq,z,y,hy,_,hd⟩
  obtain ⟨x,hx⟩ := FinitePageCalculus.page_has_initial_representative hr z
  have heq : HasDifferential model.classical.sphere r q (11,136) x Y :=
    ⟨hq,z,y,hx,hy,hd⟩
  have hz := FinitePageCalculus.differential_target_later_zero
    (by rw [model.classical.firstPage]; omega) (by omega : r<5) heq
  obtain ⟨y5,hy5,hne⟩ := y_to_e5
  exact hne (RepresentsOnPage.unique hy5 hz)
