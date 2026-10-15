module

public import KIP126.Computation.WellFormedness.LinCoordinates.E2

@[expose] public section

namespace KIP126.LinE2

noncomputable def h0 : E2 := generator ⟨0, by decide⟩
noncomputable def h1 : E2 := generator ⟨1, by decide⟩
noncomputable def h2 : E2 := generator ⟨2, by decide⟩

noncomputable def dataH0 : E2At 1 1 :=
  ⟨h0, by simpa only [h0, h0Generator_degree] using generator_mem ⟨0, by decide⟩⟩

noncomputable def dataH1 : E2At 1 2 :=
  ⟨h1, by simpa only [h1, h1Generator_degree] using generator_mem ⟨1, by decide⟩⟩

noncomputable def dataH6 : E2At 1 64 :=
  ⟨generator h6Generator, by
    simpa [h6Generator_degree] using generator_pow_mem h6Generator 1⟩

/-- The actual square in the fixed CSV quotient. Homogeneity is proved, not
inherited from PR #110's unfinished `multiply_mem`. -/
noncomputable def dataH6Sq : E2At 2 128 :=
  ⟨generator h6Generator ^ 2, by
    simpa [h6Generator_degree] using generator_pow_mem h6Generator 2⟩

end KIP126.LinE2
