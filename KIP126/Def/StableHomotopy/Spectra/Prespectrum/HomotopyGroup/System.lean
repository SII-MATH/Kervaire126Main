module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Proofs
public import Mathlib.Algebra.Colimit.DirectLimit

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open Topology
open scoped Topology.Homotopy

universe u

/-- A cofinal family of stages in which the cubical dimension is at least two. -/
abbrev stableGroupStage (d : ℤ) (k : ℕ) : ℕ := (-d).toNat + 2 + k

/-- Cubical dimension at the chosen cofinal stage. -/
abbrev stableGroupDimension (d : ℤ) (k : ℕ) : ℕ := d.toNat + 2 + k

instance (d : ℤ) (k : ℕ) : NeZero (stableGroupDimension d k) :=
  ⟨by unfold stableGroupDimension; omega⟩

instance (d : ℤ) (k : ℕ) : Nontrivial (Fin (stableGroupDimension d k)) :=
  Fin.nontrivial_iff_two_le.mpr (by unfold stableGroupDimension; omega)

/-- The genuine level homotopy group at a cofinal stage. -/
abbrev stableLevelGroup (X : Prespectrum.{u}) (d : ℤ) (k : ℕ) :=
  _root_.HomotopyGroup (Fin (stableGroupDimension d k))
    (X.level (stableGroupStage d k)) (X.level (stableGroupStage d k)).point

/-- The actual bonding map, now with its proved group homomorphism structure. -/
noncomputable def stableLevelBond (X : Prespectrum.{u}) (d : ℤ) (k : ℕ) :
    stableLevelGroup X d k →* stableLevelGroup X d (k + 1) where
  toFun := stabilizeHomotopy X (stableGroupStage d k) (stableGroupDimension d k)
  map_one' := stabilizeHomotopy_one X _ _
  map_mul' := stabilizeHomotopy_mul X _ _

/-- Finite iteration of the actual bonds between chosen stages. -/
noncomputable def stableLevelTransition (X : Prespectrum.{u}) (d : ℤ)
    (i j : ℕ) (h : i ≤ j) : stableLevelGroup X d i →* stableLevelGroup X d j :=
  Nat.leRec (MonoidHom.id _) (fun k _ f => (stableLevelBond X d k).comp f) h

end KIP126.StableHomotopy.Spectra.Prespectrum

end

section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

universe u

@[simp] theorem stableGroup_degree (d : ℤ) (k : ℕ) :
    (stableGroupDimension d k : ℤ) = d + stableGroupStage d k := by
  unfold stableGroupDimension stableGroupStage
  omega

@[simp] theorem stableLevelTransition_self (X : Prespectrum.{u}) (d : ℤ) (i : ℕ) :
    stableLevelTransition X d i i le_rfl = MonoidHom.id _ := by
  exact Nat.leRec_self _ _

theorem stableLevelTransition_succ (X : Prespectrum.{u}) (d : ℤ)
    {i j : ℕ} (h : i ≤ j) :
    stableLevelTransition X d i (j + 1) (Nat.le_succ_of_le h) =
      (stableLevelBond X d j).comp (stableLevelTransition X d i j h) := by
  exact Nat.leRec_succ _ _ h

theorem stableLevelTransition_comp (X : Prespectrum.{u}) (d : ℤ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (stableLevelTransition X d j k hjk).comp (stableLevelTransition X d i j hij) =
      stableLevelTransition X d i k (hij.trans hjk) := by
  induction hjk with
  | refl => simp
  | @step k h ih =>
    rw [stableLevelTransition_succ X d h,
      stableLevelTransition_succ X d (hij.trans h)]
    rw [MonoidHom.comp_assoc, ih]

instance (X : Prespectrum.{u}) (d : ℤ) :
    DirectedSystem (stableLevelGroup X d) (fun i j h => stableLevelTransition X d i j h) where
  map_self {i} x := by rw [stableLevelTransition_self]; rfl
  map_map {k j i} hij hjk x := DFunLike.congr_fun (stableLevelTransition_comp X d hij hjk) x

end KIP126.StableHomotopy.Spectra.Prespectrum

end
