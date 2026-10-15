module

public import KIP126.Computation.LinCoordinates.Model.E2.Data
public import KIP126.Def.ComputationModel.PolynomialAlgebra.HomogeneousParts

@[expose] public section


namespace KIP126.LinE2

/-- Homogeneous multiplication is a property of the actual quotient algebra;
it does not depend on the CSV basis certification or the reduction algorithm. -/
theorem multiply_mem {s t s' t' : ℕ} {a b : E2}
    (ha : a ∈ homogeneousPart s t) (hb : b ∈ homogeneousPart s' t') :
    a*b ∈ homogeneousPart (s+s') (t+t') :=
  KIP126.Algebra.PolynomialCoordinates.multiply_mem generatorDegree definingIdeal ha hb

theorem h6Generator_degree : generatorDegree h6Generator = (1, 64) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk2, RawData.generatorCount, h6Generator,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem h0Generator_degree : generatorDegree ⟨0, by decide⟩ = (1, 1) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

theorem h1Generator_degree : generatorDegree ⟨1, by decide⟩ = (1, 2) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

theorem generator_pow_mem (i : Generator) (n : ℕ) :
    generator i ^ n ∈ homogeneousPart
      (n * (generatorDegree i).1) (n * (generatorDegree i).2) :=
  KIP126.Algebra.PolynomialCoordinates.generator_pow_mem generatorDegree definingIdeal i n

theorem generator_mem (i : Generator) :
    generator i ∈ homogeneousPart (generatorDegree i).1 (generatorDegree i).2 := by
  simpa using generator_pow_mem i 1

end KIP126.LinE2
