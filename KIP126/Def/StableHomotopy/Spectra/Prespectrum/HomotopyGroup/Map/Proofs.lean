module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory Topology
open scoped Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

@[simp] theorem Hom.levelLoop_const {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ) :
    f.levelLoop n r GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact f.point n

theorem Hom.levelLoop_transAt {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (i : Fin r) (p q : GenLoop (Fin r) (X.level n) (X.level n).point) :
    f.levelLoop n r (GenLoop.transAt i p q) =
      GenLoop.transAt i (f.levelLoop n r p) (f.levelLoop n r q) := by
  apply GenLoop.ext
  intro t
  change f.level n ((GenLoop.transAt i p q) t) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

theorem Hom.levelHomotopy_mul {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ) [NeZero r]
    (p q : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    f.levelHomotopy n r (p * q) = f.levelHomotopy n r p * f.levelHomotopy n r q := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      calc
        _ = ⟦f.levelLoop n r (GenLoop.transAt 0 q p)⟧ :=
          congrArg (f.levelHomotopy n r)
            (_root_.HomotopyGroup.mul_spec (i := (0 : Fin r)) (p := p) (q := q))
        _ = ⟦GenLoop.transAt 0 (f.levelLoop n r q) (f.levelLoop n r p)⟧ :=
          congrArg Quotient.mk' (f.levelLoop_transAt n r 0 q p)
        _ = _ := (_root_.HomotopyGroup.mul_spec (i := (0 : Fin r))).symm

theorem stableLevelClass_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) (k : ℕ)
    (x : stableLevelGroup X d k) :
    stableHomotopyMap f d (stableLevelClass X d k x) =
      stableLevelClass Y d k (f.levelHomotopy (stableGroupStage d k) (stableGroupDimension d k) x) := by
  induction x using Quotient.inductionOn with
  | h p => rfl

/-- Two original stable classes have actual loop representatives at one cofinal stage. -/
theorem exists_stableLevelClass_pair (X : Prespectrum.{u}) (d : ℤ)
    (x y : StableHomotopy X d) :
    ∃ (k : ℕ) (p q : stableLevelGroup X d k),
      x = stableLevelClass X d k p ∧ y = stableLevelClass X d k q := by
  obtain ⟨k,p,q,hp,hq⟩ := DirectLimit.exists_eq_mk₂ (stableLevelTransition X d)
    (stableGroupCode X d x) (stableGroupCode X d y)
  refine ⟨k,p,q,?_,?_⟩
  · exact (stableGroupRealize_code X d x).symm.trans (congrArg (stableGroupRealize X d) hp)
  · exact (stableGroupRealize_code X d y).symm.trans (congrArg (stableGroupRealize X d) hq)

theorem stableHomotopyMap_add {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ)
    (x y : StableHomotopy X d) :
    stableHomotopyMap f d (x + y) = stableHomotopyMap f d x + stableHomotopyMap f d y := by
  obtain ⟨k,p,q,rfl,rfl⟩ := exists_stableLevelClass_pair X d x y
  rw [← stableLevelClass_mul, stableLevelClass_natural, Hom.levelHomotopy_mul,
    stableLevelClass_mul, stableLevelClass_natural, stableLevelClass_natural]

theorem stableHomotopyMap_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    stableHomotopyMap f d 0 = 0 := by
  have h := stableHomotopyMap_add f d 0 0
  apply add_left_cancel (a := stableHomotopyMap f d 0)
  simpa only [zero_add, add_zero] using h.symm

end KIP126.StableHomotopy.Spectra.Prespectrum
