module

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Combination

@[expose] section

namespace KIP126.Topology.Simplex.BarycentricSubdivisionMesh

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual uniform affine average of a finite family of vectors. -/
noncomputable def avg (v : ι → E) (s : Finset ι) : E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i

end KIP126.Topology.Simplex.BarycentricSubdivisionMesh
