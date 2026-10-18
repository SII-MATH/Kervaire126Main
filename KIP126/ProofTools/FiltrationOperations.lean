module

public import KIP126.SpectralSequence

/-! Internal element calculations used by the finite stretching proof.
Adapted from PageExtensionStretching/Proofs.lean at bbac1fc05843,
lines 1293–1322, 1380–1410 and 1644–1689 (MIT).
Only the public filtration and filtered-map interfaces are used. -/

@[expose] section
namespace KIP126.ProofTools.Internal
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
noncomputable section
universe u v w
variable {R : Type u} [Ring R] {ι : Type w}
  {A B : ι → ModuleCat.{v} R}
  {F : Filtration A} {G : Filtration B}

/-- Equality in the graded piece retains exactly the next-level ambiguity. -/
theorem element_grade_equal_iff (F : Filtration A) (s : ℤ) (i : ι)
    (a b : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
    F.toAssociatedGraded s i a = F.toAssociatedGraded s i b ↔
      (F.F s i).arrow a - (F.F s i).arrow b ∈
        (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
  simpa only [map_sub, sub_eq_zero] using
    F.toAssociatedGraded_eq_zero_iff s i (a-b)

theorem graded_map_representative (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (a : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
    f.inducedGrMap s i (F.toAssociatedGraded s i a) =
      G.toAssociatedGraded s i ((f.compat s i).choose a) := by
  have h : F.toAssociatedGraded s i ≫ f.inducedGrMap s i =
      (f.compat s i).choose ≫ G.toAssociatedGraded s i := by
    unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap
      Filtration.inducedAssocGradedMap
    dsimp only [cokernel.map]
    exact cokernel.π_desc _ _ _
  exact ConcreteCategory.congr_hom h a

/-- Being in the image on the graded piece means lifting modulo the next level. -/
theorem graded_image_iff_lift (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (x : (Subobject.underlying.obj (G.F s i) : ModuleCat R)) :
    (∃ z : F.associatedGraded s i,
      f.inducedGrMap s i z = G.toAssociatedGraded s i x) ↔
    ∃ a : A i, a ∈ (ModuleCat.subobjectModule (A i)) (F.F s i) ∧
      (G.F s i).arrow x - f.map i a ∈
        (ModuleCat.subobjectModule (B i)) (G.F (s+1) i) := by
  have hc (a : (Subobject.underlying.obj (F.F s i) : ModuleCat R)) :
      f.map i ((F.F s i).arrow a) = (G.F s i).arrow ((f.compat s i).choose a) :=
    (ConcreteCategory.congr_hom (f.compat s i).choose_spec a).symm
  constructor
  · rintro ⟨z, hz⟩
    haveI : Epi (F.toAssociatedGraded s i) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s i)).mp inferInstance z
    refine ⟨(F.F s i).arrow a, ⟨a, rfl⟩, ?_⟩
    rw [hc]
    apply (element_grade_equal_iff G s i x _).mp
    rw [← graded_map_representative f s i a, ha, hz]
  · rintro ⟨_, ⟨a, rfl⟩, ha⟩
    refine ⟨F.toAssociatedGraded s i a, ?_⟩
    rw [hc] at ha
    rw [graded_map_representative]
    exact ((element_grade_equal_iff G s i x _).mpr ha).symm

/-- Graded injectivity reflects the next filtration level, without ambient
injectivity or any assumption of separatedness. -/
theorem next_filtration_mem_of_graded_mono (f : FilteredMorphism F G)
    (s : ℤ) (i : ι) [Mono (f.inducedGrMap s i)]
    (a : A i) (ha : a ∈ (ModuleCat.subobjectModule (A i)) (F.F s i))
    (hb : f.map i a ∈ (ModuleCat.subobjectModule (B i)) (G.F (s+1) i)) :
    a ∈ (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
  obtain ⟨x, rfl⟩ := ha
  have hy : (G.F s i).arrow ((f.compat s i).choose x) =
      f.map i ((F.F s i).arrow x) :=
    ConcreteCategory.congr_hom (f.compat s i).choose_spec x
  have hzero : G.toAssociatedGraded s i ((f.compat s i).choose x) = 0 := by
    apply (G.toAssociatedGraded_eq_zero_iff s i _).mpr
    rwa [hy]
  have hsource : F.toAssociatedGraded s i x = 0 := by
    apply (ModuleCat.mono_iff_injective (f.inducedGrMap s i)).mp inferInstance
    rw [map_zero, graded_map_representative, hzero]
  exact (F.toAssociatedGraded_eq_zero_iff s i x).mp hsource

end
end KIP126.ProofTools.Internal
