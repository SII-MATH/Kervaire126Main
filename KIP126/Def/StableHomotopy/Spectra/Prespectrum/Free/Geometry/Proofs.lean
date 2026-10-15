module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Free.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Suspension.Compact.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual free maps are determined by their original generating-level
continuous map, independently of the chosen adjunction equivalence. -/
theorem freeHom_ext_at_generator (n : ℕ) (A : BasedSpace.{u})
    {X : Prespectrum.{u}} (f g : free n A ⟶ X) (h : f.level n = g.level n) : f = g := by
  apply (freeEvaluation n A X).injective
  apply BasedSpace.Hom.ext
  exact eq_of_heq (((freeEvaluation_exists n A X).choose_spec f).trans
    ((heq_of_eq h).trans ((freeEvaluation_exists n A X).choose_spec g).symm))

/-- The specified free map really is its input map at the generating
level, with the definitional object identifications stated explicitly. -/
theorem freeMap_at_generator (n : ℕ) {A B : BasedSpace.{u}} (f : A ⟶ B) :
    HEq ((freeMap n f).level n) f.map := by
  have h := ((freeEvaluation_exists n A (free n B)).choose_spec (freeMap n f)).symm
  change HEq ((freeMap n f).level n)
    ((freeEvaluation n A (free n B) (freeMap n f)).map) at h
  have he : freeEvaluation n A (free n B) (freeMap n f) =
      f ≫ eqToHom (free_level n B).symm := by
    simp only [freeMap,Equiv.apply_symm_apply,freeEvaluation_id]
  rw [he] at h
  have hc {B' : BasedSpace.{u}} (hB : B' = B) :
      HEq ((f ≫ eqToHom hB.symm).map) f.map := by
    subst B'
    rfl
  exact h.trans (hc (free_level n B))

/-- At zero free level the chosen free map is the explicit iterated
suspension map of suspension spectra. -/
theorem freeMap_zero {A B : BasedSpace.{u}} (f : A ⟶ B) :
    freeMap 0 f = suspensionSpectrumMap f := by
  apply freeHom_ext_at_generator 0 A
  exact eq_of_heq (freeMap_at_generator 0 f)

/-- Padding commutes with the actual free map, including the specified
identifications of the existing free objects. -/
theorem freeMap_succ (n : ℕ) {A B : BasedSpace.{u}} (f : A ⟶ B) :
    freeMap (n+1) f = eqToHom (free_succ n A) ≫
      desuspensionMap (freeMap n f) ≫ eqToHom (free_succ n B).symm := by
  apply freeHom_ext_at_generator (n+1) A
  apply eq_of_heq
  apply (freeMap_at_generator (n+1) f).trans
  apply HEq.symm
  have ht {X X' Y Y' : Prespectrum.{u}} (hX : X = X') (hY : Y' = Y)
      (g : X' ⟶ Y') (k : ℕ) :
      HEq ((eqToHom hX ≫ g ≫ eqToHom hY).level k) (g.level k) := by
    subst X'
    subst Y'
    rfl
  exact (ht (free_succ n A) (free_succ n B).symm (desuspensionMap (freeMap n f)) (n+1)).trans
    (freeMap_at_generator n f)

/-- Every level of the actual free prespectrum on a compact Hausdorff
space is compact and Hausdorff. -/
theorem free_level_compact_t2 (n : ℕ) (A : BasedSpace.{u}) [CompactSpace A] [T2Space A]
    (k : ℕ) : CompactSpace ((free n A).level k) ∧ T2Space ((free n A).level k) := by
  induction n generalizing k with
  | zero => exact BasedSpace.iterateSuspension_compact_t2 A k
  | succ n ih =>
    rw [free_succ]
    cases k with
    | zero => exact ⟨inferInstanceAs (CompactSpace PUnit),inferInstanceAs (T2Space PUnit)⟩
    | succ k => exact ih k

/-- Actual free maps preserve levelwise injectivity. -/
theorem freeMap_level_injective (n : ℕ) {A B : BasedSpace.{u}} (f : A ⟶ B)
    (hf : Function.Injective f.map) (k : ℕ) :
    Function.Injective ((freeMap n f).level k) := by
  induction n generalizing k with
  | zero =>
    rw [freeMap_zero]
    exact BasedSpace.iterateSuspensionMap_injective f hf k
  | succ n ih =>
    rw [freeMap_succ]
    have heq {X X' Y Y' : Prespectrum.{u}} (hX : X = X') (hY : Y' = Y)
        (g : X' ⟶ Y') (k : ℕ) (hg : Function.Injective (g.level k)) :
        Function.Injective ((eqToHom hX ≫ g ≫ eqToHom hY).level k) := by
      subst X'
      subst Y'
      exact hg
    apply heq
    cases k with
    | zero => exact Function.injective_id
    | succ k => exact ih k

/-- Free maps of compact Hausdorff based injections are actual closed
embeddings at every spectrum level. -/
theorem freeMap_level_isClosedEmbedding (n : ℕ) {A B : BasedSpace.{u}}
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (f : A ⟶ B) (hf : Function.Injective f.map) (k : ℕ) :
    IsClosedEmbedding ((freeMap n f).level k) := by
  letI := (free_level_compact_t2 n A k).1
  letI := (free_level_compact_t2 n B k).2
  exact ((freeMap n f).level k).continuous.isClosedEmbedding (freeMap_level_injective n f hf k)

end KIP126.StableHomotopy.Spectra.Prespectrum
