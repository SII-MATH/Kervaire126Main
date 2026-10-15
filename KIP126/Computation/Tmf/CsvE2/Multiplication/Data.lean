module

public import KIP126.Computation.WellFormedness.Tmf.Classes

@[expose] public section

/-! The homogeneous operations are restrictions of the fixed coordinate
quotient's ring operations. Their preservation proofs remain explicit
obligations in `CsvE2/Proofs.lean`. -/

namespace KIP126.Classical.Adams.Tmf.CsvE2

noncomputable section

/-- The coordinate unit, with its actual bidegree. -/
def one : E2At 0 0 := ⟨1, one_mem_homogeneousPart⟩

/-- The existing quotient-ring multiplication, restricted to homogeneous parts. -/
def mul {s t s' t' : ℕ} (x : E2At s t) (y : E2At s' t') :
    E2At (s + s') (t + t') :=
  ⟨x.val * y.val, mul_mem_homogeneousPart x.property y.property⟩

end
end KIP126.Classical.Adams.Tmf.CsvE2
