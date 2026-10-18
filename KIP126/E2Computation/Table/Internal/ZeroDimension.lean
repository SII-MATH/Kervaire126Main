module
public import KIP126.E2Computation.Table.Dimensions

/-! A zero entry in the bounded archive, together with the existing actual
page coordinates, proves that every element of that page is zero. This is a
coordinate argument; it adds no source equation or pending obligation. -/
@[expose] section
namespace KIP126.Computation.Table.Internal
open KIP126.AdamsSynthetic.Standard
noncomputable section

private theorem actual_page_zero (s t : ℕ) (ht : t ≤ 261)
    (hz : basisDimension s t = 0) (x : model.classical.sphere.Page 2 (s,t)) : x = 0 := by
  let e := Standard.coordinates s t ht
  have hn : Standard.archive.basisCount s t = 0 := (archive_dimension s t ht).trans hz
  haveI : Subsingleton (Fin (Standard.archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _

end
end KIP126.Computation.Table.Internal
