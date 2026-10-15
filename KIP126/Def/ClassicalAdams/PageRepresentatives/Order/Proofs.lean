module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.PageRepresentatives

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

theorem cycleMap_factor (p : ℤ × ℤ) (a b : WithTop ℕ) (h : a ≤ b) :
    let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
    Subobject.ofLE (D.Z b) (D.Z a) (D.Z_anti h) ≫ cycleMap H X a p =
      cycleMap H X b p := by
  dsimp [cycleMap]
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]

theorem boundaryMap_factor (p : ℤ × ℤ) (a b : WithTop ℕ) (h : a ≤ b) :
    let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
    Subobject.ofLE (D.B a) (D.B b) (D.B_mono h) ≫ boundaryMap H X b p =
      boundaryMap H X a p := by
  dsimp [boundaryMap]
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]

theorem cycles_antitone (p : ℤ × ℤ) : Antitone (fun c : ℤ => cycles H X c p) := by
  intro a b hab x hx
  obtain ⟨z, rfl⟩ := hx
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have h : (↑(a - 1).toNat : WithTop ℕ) ≤ ↑(b - 1).toNat := by
    exact_mod_cast (show (a - 1).toNat ≤ (b - 1).toNat by omega)
  refine ⟨(Subobject.ofLE _ _ (D.Z_anti h)) z, ?_⟩
  exact congrArg (fun f => f z) (cycleMap_factor H X p _ _ h)

theorem boundaries_monotone (p : ℤ × ℤ) : Monotone (fun b : ℤ => boundaries H X b p) := by
  intro a b hab x hx
  obtain ⟨z, rfl⟩ := hx
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have h : (↑(a - 1).toNat : WithTop ℕ) ≤ ↑(b - 1).toNat := by
    exact_mod_cast (show (a - 1).toNat ≤ (b - 1).toNat by omega)
  refine ⟨(Subobject.ofLE _ _ (D.B_mono h)) z, ?_⟩
  exact congrArg (fun f => f z) (boundaryMap_factor H X p _ _ h)

/-- Actual infinite-cycle representatives define classes on every finite page. -/
theorem permanentCycles_le_cycles (p : ℤ × ℤ) (c : ℤ) :
    permanentCycles H X p ≤ cycles H X c p := by
  rintro x ⟨z, rfl⟩
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  refine ⟨(Subobject.ofLE _ _ (D.Z_anti (show (↑(c - 1).toNat : WithTop ℕ) ≤ ⊤
    from le_top))) z, ?_⟩
  exact congrArg (fun f => f z) (cycleMap_factor H X p _ ⊤ le_top)

/-- Boundaries at every finite level lie in the actual permanent-cycle submodule. -/
theorem boundaries_le_permanentCycles (p : ℤ × ℤ) (b : ℤ) :
    boundaries H X b p ≤ permanentCycles H X p := by
  rintro x ⟨z, rfl⟩
  let D := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have h : D.B (↑(b - 1).toNat) ≤ D.Z ⊤ :=
    (D.B_mono le_top).trans (D.B_le_Z ⊤)
  refine ⟨(Subobject.ofLE _ _ h) z, ?_⟩
  have heq : Subobject.ofLE _ _ h ≫ cycleMap H X ⊤ p =
      boundaryMap H X (↑(b - 1).toNat) p := by
    dsimp [cycleMap, boundaryMap]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact congrArg (fun f => f z) heq

theorem boundaries_le_cycles (p : ℤ × ℤ) (b c : ℤ) :
    boundaries H X b p ≤ cycles H X c p :=
  (boundaries_le_permanentCycles H X p b).trans (permanentCycles_le_cycles H X p c)

end
end KIP126.Classical.Adams.PageRepresentatives
