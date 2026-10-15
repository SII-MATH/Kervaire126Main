module

public import KIP126.Def.StableHomotopy.FiniteType.Predicates
public import KIP126.Def.StableHomotopy.Context.Proofs
public import KIP126.Def.StableHomotopy.Context.Mapping.Data
public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

namespace KIP126.StableHomotopy
open CategoryTheory MonoidalCategory Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Finite mod-two homology is preserved by an actual spectrum isomorphism. -/
theorem FiniteMod2Type.of_iso {H : Mod2EilenbergMacLane (C := C)}
    {X Y : C} (hX : FiniteMod2Type H X) (e : X ≅ Y) : FiniteMod2Type H Y := by
  intro n
  letI := hX n
  let k := (tensorLeft H.HF2).mapIso e
  exact Finite.of_injective
    (fun a : Mod2Homology H n Y => (a ≫ k.inv : Mod2Homology H n X))
    (fun _ _ h => (cancel_mono k.inv).1 h)

/-- Boundedness below is preserved by an actual spectrum isomorphism. -/
theorem BoundedBelow.of_iso {X Y : C} (hX : BoundedBelow X) (e : X ≅ Y) :
    BoundedBelow Y := by
  obtain ⟨N, hN⟩ := hX
  refine ⟨N, fun n hn => ?_⟩
  letI := hN n hn
  exact ⟨fun a b => (cancel_mono e.inv).1
    (Subsingleton.elim (a ≫ e.inv) (b ≫ e.inv))⟩

/-- The long exact sequence bounds the third object of a cofiber triangle. -/
theorem BoundedBelow.of_cofiber (T : HoCofiberSequence (C := C))
    (hX : BoundedBelow T.X) (hY : BoundedBelow T.Y) : BoundedBelow T.Z := by
  obtain ⟨NX, hNX⟩ := hX
  obtain ⟨NY, hNY⟩ := hY
  refine ⟨min NY (NX + 1), fun n hn => ?_⟩
  have hnY : n < NY := lt_of_lt_of_le hn (min_le_left _ _)
  have hnX : n - 1 < NX := by
    have := min_le_right NY (NX + 1)
    omega
  letI := hNY n hnY
  letI := hNX (n - 1) hnX
  have hz (z : HomotopyGroup n T.Z) : z = 0 := by
    obtain ⟨y, hy⟩ := (les_homotopy_exact_g T n z).mp
      (Subsingleton.elim _ _)
    rw [show y = 0 from Subsingleton.elim _ _] at hy
    simpa using hy.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Suspension reindexes represented homotopy groups and preserves a bound. -/
theorem BoundedBelow.shift {X : C} (hX : BoundedBelow X) (k : ℤ) :
    BoundedBelow (X⟦k⟧) := by
  obtain ⟨N, hN⟩ := hX
  refine ⟨N + k, fun n hn => ?_⟩
  letI := hN (n - k) (by omega)
  let e := (shiftFunctorAdd' C (n - k) k n (by omega)).app SphereSpectrum
  let h := (shiftEquiv C k).fullyFaithfulFunctor.homEquiv
    (X := Sphere (n - k)) (Y := X)
  exact ⟨fun a b => (cancel_epi e.inv).1
    (h.symm.injective (Subsingleton.elim (h.symm (e.inv ≫ a))
      (h.symm (e.inv ≫ b))))⟩

/-- Exact tensoring and the homology long exact sequence preserve finite type. -/
theorem FiniteMod2Type.of_cofiber {H : Mod2EilenbergMacLane (C := C)}
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (T : HoCofiberSequence (C := C)) (hX : FiniteMod2Type H T.X)
    (hY : FiniteMod2Type H T.Y) : FiniteMod2Type H T.Z := by
  classical
  intro n
  let U := T.map (tensorLeft H.HF2)
  have hfiniteX : Finite (HomotopyGroup (n - 1) U.X) := hX (n - 1)
  have hfiniteY : Finite (HomotopyGroup n U.Y) := hY n
  letI := hfiniteX
  letI := hfiniteY
  letI := Fintype.ofFinite (HomotopyGroup (n - 1) U.X)
  letI := Fintype.ofFinite (HomotopyGroup n U.Y)
  letI := AddGroup.fintypeOfKerLeRange (inducedMap U.g n)
    (connectingHomomorphism U n) (by
      intro z hz
      exact (les_homotopy_exact_g U n z).mp hz)
  change Finite (HomotopyGroup n U.Z)
  infer_instance

/-- Shift-compatible tensoring preserves degreewise finite mod-two homology. -/
theorem FiniteMod2Type.shift {H : Mod2EilenbergMacLane (C := C)}
    [(tensorLeft H.HF2).CommShift ℤ] {X : C}
    (hX : FiniteMod2Type H X) (k : ℤ) : FiniteMod2Type H (X⟦k⟧) := by
  intro n
  letI := hX (n - k)
  let e := (shiftFunctorAdd' C (n - k) k n (by omega)).app SphereSpectrum
  let h := (shiftEquiv C k).fullyFaithfulFunctor.homEquiv
    (X := Sphere (n - k)) (Y := H.HF2 ⊗ X)
  let t := ((tensorLeft H.HF2).commShiftIso k).app X
  exact Finite.of_injective
    (fun a : Mod2Homology H n (X⟦k⟧) => h.symm (e.inv ≫ a ≫ t.hom)) (by
      intro a b hab
      apply (cancel_mono t.hom).1
      apply (cancel_epi e.inv).1
      exact h.symm.injective hab)

/-- The sphere has degreewise finite mod-two homology, directly from the
Eilenberg--Mac Lane homotopy groups and the tensor right unitor. -/
theorem finiteMod2Type_sphere (H : Mod2EilenbergMacLane (C := C)) :
    FiniteMod2Type H SphereSpectrum := by
  intro n
  have hfinite : Finite (HomotopyGroup n H.HF2) := by
    by_cases hn : n = 0
    · subst n
      exact Finite.of_injective H.pi0Equiv H.pi0Equiv.injective
    · letI := H.homotopy_vanishes n hn
      infer_instance
  letI := hfinite
  exact Finite.of_injective
    (fun a : Mod2Homology H n SphereSpectrum => a ≫ (ρ_ H.HF2).hom)
    (fun _ _ h => (cancel_mono (ρ_ H.HF2).hom).1 h)

end KIP126.StableHomotopy
