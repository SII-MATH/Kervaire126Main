module

public import KIP126.Def.Topology.FiberBundle.Chart.Data

@[expose] public section

namespace KIP126.Topology.FiberBundle

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- Around a specified base point, nonemptiness of the model fiber supplies
the hopfAndDetector values needed to turn the actual product chart into a
standard bundle trivialization. -/
theorem exists_trivialization_at_of_open_product [Nonempty F]
    (p : C(E, B)) (U : Set B) (hU : IsOpen U)
    (e : (p ⁻¹' U) ≃ₜ U × F) (he : ∀ z, (e z).1.val = p z.val)
    (b : B) (hb : b ∈ U) :
    ∃ T : Bundle.Trivialization F p, T.baseSet = U ∧ b ∈ T.baseSet := by
  obtain ⟨f⟩ := ‹Nonempty F›
  letI : Nonempty (p ⁻¹' U) := ⟨e.symm (⟨b, hb⟩, f)⟩
  exact ⟨trivializationOfOpenProduct p U hU e he, rfl, hb⟩

end KIP126.Topology.FiberBundle
