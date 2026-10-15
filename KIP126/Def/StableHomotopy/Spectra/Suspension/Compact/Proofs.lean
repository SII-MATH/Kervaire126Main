module

public import KIP126.Def.StableHomotopy.Spectra.Generators
public import KIP126.Def.Topology.Collapse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory _root_.Topology Set
open scoped unitInterval OnePoint

universe u

set_option backward.isDefEq.respectTransparency false

/-- The exact fibers of the actual reduced-suspension quotient. -/
theorem suspensionProjection_eq_iff (X : BasedSpace.{u}) (p q : X × I) :
    X.suspensionProjection p = X.suspensionProjection q ↔
      p = q ∨ (SuspensionCollapsed X p ∧ SuspensionCollapsed X q) := by
  constructor
  · intro h
    change (Quot.mk (SuspensionRelation X) p : Quot _) = Quot.mk _ q at h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b h => exact Or.inr h
    | refl a => exact Or.inl rfl
    | symm a b _ ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2,h.1⟩)
    | trans a b c _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | h₁
      · exact ih₂
      · rcases ih₂ with rfl | h₂
        · exact Or.inr h₁
        · exact Or.inr ⟨h₁.1,h₂.2⟩
  · rintro (rfl | h)
    · rfl
    · exact Quot.sound h

/-- Reduced suspension of an actual compact space remains compact. -/
theorem suspension_compactSpace (X : BasedSpace.{u}) [CompactSpace X] :
    CompactSpace X.suspension :=
  inferInstanceAs (CompactSpace (Quot (SuspensionRelation X)))

/-- The actual suspension of a compact Hausdorff based space is
Hausdorff, using its specified closed-collapse quotient. -/
theorem suspension_t2Space (X : BasedSpace.{u}) [CompactSpace X] [T2Space X] :
    T2Space X.suspension := by
  let S : Set (X × I) := {z | SuspensionCollapsed X z}
  have hS : IsClosed S :=
    (isClosed_eq continuous_fst continuous_const).union
      ((isClosed_eq continuous_snd continuous_const).union
        (isClosed_eq continuous_snd continuous_const))
  letI : LocallyCompactSpace (Sᶜ : Set (X × I)) := hS.isOpen_compl.locallyCompactSpace
  obtain ⟨e,_,_⟩ := KIP126.Topology.exists_collapse_homeomorph_onePoint S hS
    ⟨(X.point,0),Or.inl rfl⟩
  exact e.symm.t2Space

/-- An injective based map remains injective on the actual reduced
suspension quotient. No homotopy replacement is used. -/
theorem suspendMap_injective {X Y : BasedSpace.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f.map) : Function.Injective (suspendMap f).map := by
  intro p q
  induction p using Quot.inductionOn with
  | h p =>
    induction q using Quot.inductionOn with
    | h q =>
      intro hpq
      change Y.suspensionProjection (f.map p.1,p.2) =
        Y.suspensionProjection (f.map q.1,q.2) at hpq
      apply (suspensionProjection_eq_iff X p q).mpr
      rcases (suspensionProjection_eq_iff Y _ _).mp hpq with he | ⟨hp,hq⟩
      · exact Or.inl (Prod.ext (hf (congrArg (fun z : Y × I => z.1) he))
          (congrArg (fun z : Y × I => z.2) he))
      · have h (z : X × I) (hz : SuspensionCollapsed Y (f.map z.1,z.2)) :
            SuspensionCollapsed X z := by
          rcases hz with hz | hz | hz
          · exact Or.inl (hf (hz.trans f.point.symm))
          · exact Or.inr (Or.inl hz)
          · exact Or.inr (Or.inr hz)
        exact Or.inr ⟨h p hp,h q hq⟩

/-- A based injection between compact Hausdorff spaces gives a genuine
closed embedding after actual reduced suspension. -/
theorem suspendMap_isClosedEmbedding {X Y : BasedSpace.{u}}
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (f : X ⟶ Y) (hf : Function.Injective f.map) :
    IsClosedEmbedding (suspendMap f).map := by
  letI := suspension_compactSpace X
  letI := suspension_t2Space Y
  exact (suspendMap f).map.continuous.isClosedEmbedding (suspendMap_injective f hf)

/-- Every actual iterated suspension of a compact Hausdorff based
space is compact and Hausdorff. -/
theorem iterateSuspension_compact_t2 (X : BasedSpace.{u}) [CompactSpace X] [T2Space X]
    (n : ℕ) : CompactSpace (X.iterateSuspension n) ∧ T2Space (X.iterateSuspension n) := by
  induction n with
  | zero => exact ⟨‹CompactSpace X›,‹T2Space X›⟩
  | succ n ih =>
    letI := ih.1
    letI := ih.2
    exact ⟨suspension_compactSpace _,suspension_t2Space _⟩

/-- Actual iterated suspension preserves based injections. -/
theorem iterateSuspensionMap_injective {X Y : BasedSpace.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f.map) (n : ℕ) :
    Function.Injective (iterateSuspensionMap f n).map := by
  induction n with
  | zero => exact hf
  | succ n ih => exact suspendMap_injective _ ih

/-- All iterated suspension maps of compact Hausdorff based injections
are actual closed embeddings. -/
theorem iterateSuspensionMap_isClosedEmbedding {X Y : BasedSpace.{u}}
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (f : X ⟶ Y) (hf : Function.Injective f.map) (n : ℕ) :
    IsClosedEmbedding (iterateSuspensionMap f n).map := by
  letI := (iterateSuspension_compact_t2 X n).1
  letI := (iterateSuspension_compact_t2 Y n).2
  exact (iterateSuspensionMap f n).map.continuous.isClosedEmbedding
    (iterateSuspensionMap_injective f hf n)

end KIP126.StableHomotopy.Spectra.BasedSpace
